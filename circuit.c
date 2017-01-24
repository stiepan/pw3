#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <stdbool.h>
#include "err.h"

/* Types and structures to represent circuit */
typedef enum NodeType {
  PNUM, VAR, UNARY, BINARY, UNRECOGNIZED_TYPE_ERR
} NodeType;

typedef union {
    int var;
    char op;
} Label;

typedef struct Node {
  NodeType type;
  Label label;
  struct Node *left, *right;
  bool is_root; //of some parse tree
  int id; //unqiue of registered nodes
  bool visited;
  int post; //in some topological order
  //pipes fall into two different categories: propagated and not, the first need to be opened
  //when creating processes tree, because need to be propagated down it to make connection
  //between 1. descendants (root x and leaves labaleed with x), 2.circuit and leaves labelled with x
  //the second category comprises pipes parallel to process tree edges, close them as soon as possbile
  /* propagated pipes - these are stored only in root nodes, var leaf knows index in corresponidng array */
  int *root_write_to_var; //root nodes use them to message var leaves
  int *root_read_from_var;
  int *var_write_to_root; //var leaves use them to message root
  int *var_read_from_root;
  //if node is a leaf labeled with variable it is the index in array of pipes in corresponding tree
  //if there is such a tree of course
  int pipe_id;
  int pipes_counter;
  int pipes_list_cap;
  //communication between var leaf and circuit
  int var_read_from_circuit;
  int var_write_to_circuit;
  int circuit_write_to_var;
  int circuit_read_from_var;
  /* not propagated pipes - parallel to edges in process tree */ 
  int parent_read_from_me;
  int parent_write_to_me;
  int read_from_parent;
  int write_to_parent;
} *ParseTree;

struct Circuit {
  //a list of all the nodes allocated within program, handy in terms of resource management
  ParseTree *variables;
  size_t list_len; //number on nodes in a variables array
  size_t list_cap; //capacity of variables
  ParseTree *trees; //x[0], .., x[V - 1] varaibles as a roots of trees representing its equations
  int *topo_ord; //topo_ord[topo_ord_len -1, .., 0] gives a topological ordering of trees
  size_t topo_ord_len;
} circuit;

typedef struct {
  int i;
  long val;
} Mes;

int N, K, V, nr;

/* Initiates [circuit] structure making allowance for arguments passed by user */
int init_circuit() {
  int DEFAULT_BUF_CAP = 2*V;
  circuit.variables = (ParseTree *) calloc(DEFAULT_BUF_CAP, sizeof(*circuit.variables));
  if (circuit.variables == NULL)
    return -1;
  circuit.list_cap = DEFAULT_BUF_CAP;
  circuit.trees = (ParseTree *) calloc(V, sizeof(*circuit.trees));
  circuit.topo_ord = (int *) calloc(V, sizeof(*circuit.trees));
  if (circuit.trees == NULL || circuit.topo_ord == NULL)
    return -1;
  return 0;
}

/* Frees memory storing [circuit] elements and removes all registered nodes. */
void free_circuit() {
  for (int i=circuit.list_len-1; i>=0; i--) {
    if (circuit.variables[i]->root_write_to_var != NULL) {
      free(circuit.variables[i]->root_write_to_var);
      free(circuit.variables[i]->root_read_from_var);
      free(circuit.variables[i]->var_read_from_root);
      free(circuit.variables[i]->var_write_to_root);
    }
    free(circuit.variables[i]);
  }
  free(circuit.topo_ord);
  free(circuit.trees);
  free(circuit.variables);
}

/* Adds [t] to the list of nodes that should be deleted if [free_nodes] is evoked. */
int register_node(ParseTree t) {
  if (circuit.list_cap == circuit.list_len) {
    size_t nsize = circuit.list_cap * 2;
    ParseTree *narray = (ParseTree *) realloc(circuit.variables,
                                              sizeof(*circuit.variables) * nsize);
    if (narray == NULL)
      return -1;
    circuit.variables = narray;
    circuit.list_cap = nsize;
  }
  t->id = circuit.list_len;
  circuit.variables[circuit.list_len++] = t;
  return 0;
}

/* Create node of given type and label, it will be registered and thus deleted
   if [free_nodes] is evoked */
ParseTree new_tree(NodeType type, Label label) {
  ParseTree tree = NULL;
  tree = (ParseTree) calloc(1, sizeof(*tree));
  if (tree == NULL)
    return NULL;
  register_node(tree);
  tree->label = label;
  tree->type = type;
  return tree;
}

/* Gets first element of grammar alphabet from line sufix, stores it in [label] and returns
  the type of the match */
NodeType retrieve_var(char **line, Label *label) {
  NodeType type = UNRECOGNIZED_TYPE_ERR;
  while (**line != '\0' && isspace(**line)) {
    ++(*line); 
  }
  if (**line == 'x' && *(*line + 1) == '[') {
    *line += 2;
    int v = atoi(*line);
    while (**line != '\0' && *((*line)++) != ']');
    label->var = v;
    type = VAR;
  }
  else if (isdigit(**line)) {
    int n = atoi(*line);
    while (isdigit(*(++(*line))));
    label->var = n;
    type = PNUM;
  }
  else if (**line == '+' || **line == '*') {
    label->op = **line;
    type = BINARY; 
    ++(*line);
  }
  else if (**line == '-') {
    label->op = **line;
    type = UNARY;
    ++(*line);
  }
  return type;
}

/*[line] is a sufix which has yet to be procesed
  [op] and [nop] are tops of stacks that keep respectively opeators and variables/numerals. */
ParseTree parse_line(char **line, ParseTree op, ParseTree nop) {
  while (**line != '\0' && (isspace(**line) || **line == '(')) {
    ++(*line);
  }
  // end of currently processed expression, pop the operator and combine it variable from top, if
  // the operator is binary one it will have its left child added in the parent of recursion tree
  if (**line == ')') { 
    ++(*line);
    op->right = nop;
    return op;
  }
  else if (**line != '\0') {
    Label label;
    NodeType nodetype;
    if ((nodetype = retrieve_var(line, &label)) == UNRECOGNIZED_TYPE_ERR) //error
      return NULL;
    ParseTree tree = new_tree(nodetype, label);
    if (nodetype == PNUM || nodetype == VAR) {
      // if its variable or numeral put it on the top of the [nop] stack
      return parse_line(line, op, tree);
    }
    else { //nodetype is either BINARY or UNARY
      // both types of operators need to be joined with expression that follows them, so put it
      // on the top of [op] stack
      ParseTree op_joined_with_var = parse_line(line, tree, NULL);
      // and binary ones need join with the preceeding expression as well
      if (nodetype == BINARY)
        op_joined_with_var->left = nop;
      // put parsed subtree on the top of [nop] stack
      return parse_line(line, op, op_joined_with_var);
    }
  }
  return nop;
}

/*root_id represents variable x[root_id] if tree represent variable or
  is -1 if its the inner node of some parse tree*/
int dfs(ParseTree tree, int root_id) {
  tree->visited = true;
  if (tree->type == VAR) {
    int x_i = tree->label.var;
    ParseTree var_tree = circuit.trees[x_i];
    if (var_tree != NULL) {
      if (var_tree->visited) {
        if (var_tree->post == -1) { // var_tree is a grandparent of mine
          return -1;
        }
      }
      else {
        if (dfs(var_tree, x_i) < 0)
          return -1;
      }
    }
  }
  else if (tree->type == UNARY || tree->type == BINARY) {
    if ((dfs(tree->right, -1) < 0) || (tree->type == BINARY && (dfs(tree->left, -1) < 0)))
      return -1;
  }
  if (root_id >= 0) {
    tree->post = circuit.topo_ord_len;
    circuit.topo_ord[circuit.topo_ord_len++] = root_id;
  }
  return 0;
}

int topo_sort() {
  circuit.topo_ord_len = 0;
  for (int v=0; v<V; v++) {
    if (circuit.trees[v] != NULL) {
      circuit.trees[v]->visited = false;
      circuit.trees[v]->post = -1;
    }
  }
  for (int v=0; v<V; v++) {
    if (circuit.trees[v] != NULL && (!(circuit.trees[v]->visited))) {
      if (dfs(circuit.trees[v], v) < 0)
        return -1;
    }
  }
  return 0;
}

/*\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
void print_tree(ParseTree t) {
  if(t == NULL) {
    printf ("UUUUBS!\n");
    exit(1);
  }
  if (t->type == BINARY) {
    if(t->left == NULL || t->right == NULL) {
      printf("ERRRR %c %d %d\n", t->label.op, t->left == NULL, t->right==NULL);
      exit(1);
    }
    printf("(");
    print_tree(t->left);
    printf(" %c ", t->label.op);
    print_tree(t->right);
    printf(")");
  }
  else if (t->type == UNARY) {
    if (t->left != NULL || t->right == NULL) {
      printf ("ERRR %c %d %d\n", t->label.op, t->left == NULL, t->right == NULL);
      exit(1);
    }
    printf("(%c", t->label.op);
    print_tree(t->right);
    printf(")");
  }
  else if (t->type == PNUM) {
    printf("%d", t->label.var);
  }
  else if (t->type == VAR) {
    printf("x[%d]", t->label.var);
  }
  else {
    printf("TYPE!!!!\n");
    exit(1);
  }
}

void print_topo() {
  for (int v=circuit.topo_ord_len - 1; v>=0; v--) {
    printf("(%d %d) ", circuit.topo_ord[v], circuit.trees[circuit.topo_ord[v]]->post);
  }
  printf("\n");
}
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\*/

// Creates pipes between x root nad x labeled leaf
int register_pipe(ParseTree varLabeledLeaf) {
  int v = varLabeledLeaf->label.var;
  ParseTree root = circuit.trees[v];
  if (root->root_read_from_var == NULL) {
    int DEFAULT_PIPES_QUANT = 1;
    root->root_read_from_var = (int *) calloc(DEFAULT_PIPES_QUANT, sizeof(*(root->root_read_from_var)));
    root->root_write_to_var = (int *) calloc(DEFAULT_PIPES_QUANT, sizeof(*(root->root_write_to_var)));
    root->var_read_from_root = (int *) calloc(DEFAULT_PIPES_QUANT, sizeof(*(root->var_read_from_root)));
    root->var_write_to_root = (int *) calloc(DEFAULT_PIPES_QUANT, sizeof(*(root->var_write_to_root)));
    int *arrays[4] = {root->root_read_from_var, root->root_write_to_var, root->var_read_from_root, root->var_write_to_root};
    for (int i=0; i<4; i++) {
      if (arrays[i] == NULL)
        return -1;
    }
    root->pipes_list_cap = DEFAULT_PIPES_QUANT;
  }
  else if (root->pipes_counter == root->pipes_list_cap) {
    int nsize = root->pipes_list_cap * 2;
    int **arrays[4] = {&root->root_read_from_var, &root->root_write_to_var,
                     &root->var_read_from_root, &root->var_write_to_root};
    int *narrays[4];
    for (int i=0; i<4; i++) {
      narrays[i] = realloc(*arrays[i], sizeof(int)*nsize); 
      if (narrays[i] == NULL)
        return -1;
    }
    for (int i=0; i<4; i++) {
      *arrays[i] = narrays[i];
    }
    root->pipes_list_cap = nsize;
  }
  int w_to_root[2];
  int w_to_var[2];
  if (pipe(w_to_root) < 0 || pipe(w_to_var) < 0)
    return -1;
  varLabeledLeaf->pipe_id = root->pipes_counter;
  root->root_write_to_var[root->pipes_counter] = w_to_var[1];
  root->var_read_from_root[root->pipes_counter] = w_to_var[0];
  root->var_write_to_root[root->pipes_counter] = w_to_root[1];
  root->root_read_from_var[root->pipes_counter++] = w_to_root[0];
  return 0;
}

int extern_var(ParseTree tree) {
  if (tree->type == VAR) {
    if (circuit.trees[tree->label.var] != NULL && register_pipe(tree) < 0)
      return -1;
    // create pipes to circuit
    int w_to_circuit[2];
    int w_to_var[2];
    if (pipe(w_to_circuit) < 0 || pipe(w_to_var) < 0)
      return -1;
    tree->var_read_from_circuit = w_to_var[0];
    tree->var_write_to_circuit = w_to_circuit[1];
    tree->circuit_write_to_var = w_to_var[1];
    tree->circuit_read_from_var = w_to_circuit[0];
  }
  else if (tree->type == BINARY || tree->type == UNARY) {
    if (extern_var(tree->right) < 0 || ((tree->type == BINARY) && (extern_var(tree->left) < 0)))
      return -1;
  }
  return 0;
}

/* Prepares descriptors used to communicate between trees roots and 
   leaves labeled with particular variable. */
int prepare_non_tree_pipes() {
  for (int v=circuit.topo_ord_len - 1; v>=0; v--) {
    if (extern_var(circuit.trees[circuit.topo_ord[v]]) < 0)
      return -1;
  }
  return 0;
}

/* And now somethng completely different. */
void looming_doom(char *ERR) {
  free_circuit();
  if (ERR != NULL)
    syserr(ERR);
  exit(0);
}

void close_pipe_or_perish_any_hope(int pipe, char *err) {
  if(close(pipe) < 0)
    looming_doom(err);
}

void listen(ParseTree self) {
  /*if (self->is_root)
    entries += 1;
  if (self->type == PNUM || self->type == UNARY)
    entries += 1;
  else if (self)
  if (self->type == PNUM) {
    Mes mes;
    while (read(self->pnum_pipes[0], &mes, sizeof(mes)))
      write(parent_dsc, &mes, sizeof(mes));
  }*/
}

/* Map ParseTree to process tree */ 
void proc_node(ParseTree self, int x) {
/*  // close propagated descriptors from roots to variable nodes the given root describe
  // fisrt if you are not a root you do not need non-tree descriptors that your root was given
  if (!self->is_root) {
    ParseTree root = circuit.trees[x];
    for (int i=0; i<root->pipes_counter; i++)
      close(root->root_pipes_w[i]);
  }
  // if you are a leaf of var v type you should be able to read from tree[v]
  for (int v=0; v<V; v++) {
    if (circuit.trees[v] == NULL)
      continue;
    ParseTree t = circuit.trees[v];
    if (t->root_pipes_r != NULL) {
      for(int i=0; i<t->pipes_counter; i++) {
        if (self->type == VAR && v == x && i == self->pipe_id)
          continue;
        if (close(t->root_pipes_r[i]) < 0)
          looming_doom("CLOSE WRITE PIPES FOR OTHER ROOTS");
      }
    }
  }
  listen(self, parent);*/
}

/* x:{X[0], .., X[V-1]} */
void processes_tree(int x) {
  //Tree x defienietly doesn't need other trees' descriptors to write to var labeled leaves 
  ParseTree self = circuit.trees[x];
  for (int i=0; i<V; i++) {
    ParseTree root = circuit.trees[i];
    if (i == x || root == NULL)
      continue;
    if (root->root_write_to_var != NULL) {
      for(int j=0; j<root->pipes_counter; j++) {
        if (close(root->root_write_to_var[j]) < 0 || close(root->root_read_from_var[j]) < 0)
          looming_doom("CLOSE WRITE PIPES FOR OTHER ROOTS");
      }
    }
  }
  //So now create the processes tree mapping ParseTree of x
  int w_to_c[2], w_to_p[2];
  bool parent_proc = false;
  while (!parent_proc && (self->type == BINARY || self->type == UNARY)) {
    bool child = false;
    for (int i=0; i<1+(self->type == BINARY) && !child; i++) {
      if (pipe(w_to_c) < 0 || pipe(w_to_p)) {
        looming_doom("PIPES BETWEEN TREE NODES");
      }
      switch (fork()) {
        case -1:
          looming_doom("FORK IN PROC_NODE");
        case 0:
          if (self->is_root && self->root_write_to_var != NULL) { //you're children, dispose root desc
            for (int j=0; j<self->pipes_counter; j++) {
              if (close(self->root_write_to_var[j]) < 0 || close(self->root_read_from_var[j]) < 0)
                looming_doom("CLOSE WRITE TO VARS IN NONROOT");
            }
          }
          // close pipes to grandparent
          close_pipe_or_perish_any_hope(self->read_from_parent, "GRANDP");
          close_pipe_or_perish_any_hope(self->write_to_parent, "GRANDP");
          printf ("ParseTree nr %d ", x);
          if (i == 0) {
            printf ("right %d %d\n", self->right->label.var, getpid());
            self = self->right;
          }
          else { //you're the second child
            close_pipe_or_perish_any_hope(self->right->parent_read_from_me, "LEFT CHILD");
            close_pipe_or_perish_any_hope(self->right->parent_write_to_me, "LEFT CHILD W");
            printf ("left %d %d\n", self->left->label.var, getpid());
            self = self->left;
          }
          self->read_from_parent = w_to_c[0];
          self->write_to_parent = w_to_p[1];
          self->parent_read_from_me = w_to_p[0];
          self->parent_write_to_me = w_to_c[1];
          close_pipe_or_perish_any_hope(self->parent_read_from_me, "CHILD PARENT");
          close_pipe_or_perish_any_hope(self->parent_write_to_me, "CHILD PARENT W");
          parent_proc = false;
          child = true;
          break;
        default: ;
          ParseTree child = (i==0) ? self->right : self->left;
          child->read_from_parent = w_to_c[0];
          child->write_to_parent = w_to_p[1];
          child->parent_read_from_me = w_to_p[0];
          child->parent_write_to_me = w_to_c[1];
          close_pipe_or_perish_any_hope(child->read_from_parent, "FROM PARENT WITH ERROR");
          close_pipe_or_perish_any_hope(child->write_to_parent, "FROM PARENT WITH ERROR W");
          parent_proc = true;
      }
    }
  }
  //we have the whole tree, so all 'to be propagated' pipes reached thier destination
  //close copies that missed the point
  for (int i=0; i<circuit.list_len; i++) {
    ParseTree node = circuit.variables[i];
    if (node->type == VAR && !(self->type == VAR && self->id == node->id)) {
      close_pipe_or_perish_any_hope(node->var_write_to_circuit, "UNNEC VAR CIRC");
      close_pipe_or_perish_any_hope(node->var_read_from_circuit, "UNNEC VAR CIRC R");
    }
    if (node->is_root) {
      for (int i=0; i<node->pipes_counter; i++) {
        if (self->type == VAR && self->id == node->id)
          continue;
        close_pipe_or_perish_any_hope(node->var_write_to_root[i], "UNNEC TO ROOT");
        close_pipe_or_perish_any_hope(node->var_read_from_root[i], "UNNEC TO ROOT R");
      }
    }
  }
  listen(self);
  for (int i=0; i < 2*(self->type == BINARY) + (self->type == UNARY); i++) {
    if (wait(0) == -1)
      looming_doom("WAIT ERR");
  }
  sleep(30);
  looming_doom(NULL);
}

void broadcast_to_leaves_and_vars(int *vars, int q) {
}

int main() {
  scanf("%d%d%d", &N, &K, &V);
  if (init_circuit() == 0) {
    char *line = NULL;
    size_t len = 0;
    for (int k=1; k<=K; k++) {
      scanf("%d", &nr);
      if (getline(&line, &len, stdin) < 0)
        break;
      char *mock_line = line;
      Label label;
      NodeType nodetype = retrieve_var(&mock_line, &label); //left side of equation
      if (nodetype != VAR || circuit.trees[label.var] != NULL) {
        printf("%d F\n", nr);
        free(line);
        looming_doom(NULL);
      }
      while (*mock_line != '\0' && (isspace(*mock_line) || *mock_line == '='))
        ++mock_line;
      ParseTree tree = parse_line(&mock_line, NULL, NULL);
      if (tree == NULL) {
        free(line);
        looming_doom("PARSE ERR");
      }
      //print_tree(tree);
      circuit.trees[label.var] = tree;
      tree->is_root = true;
      if (topo_sort() < 0) {
        printf("%d F\n", nr);
        free(line);
        looming_doom(NULL);
      }
      else {
        //print_topo();
        printf("%d P\n", nr);
      }
    }
    free(line);
    if (prepare_non_tree_pipes() < 0) {
      looming_doom("PREP NON TREE PIPES");
    }
    for (int v=0; v<V; v++) {
      ParseTree root = circuit.trees[v];
      if (root == NULL)
        continue;
      int w_to_root[2];
      int w_to_circuit[2];
      if (pipe(w_to_root) == -1 || pipe(w_to_circuit) == -1)
        looming_doom("PIPE BETWEEN CIRC AND ROOT");
      root->parent_read_from_me = w_to_circuit[0];
      root->write_to_parent = w_to_circuit[1];
      root->parent_write_to_me = w_to_root[1];
      root->read_from_parent = w_to_root[0];
      switch (fork()) {
        case -1:
          looming_doom("FORK IN CIRC");
        case 0: //root process of variable v
          for (int i=v; i>=0; i--) {
            close_pipe_or_perish_any_hope(circuit.trees[i]->parent_read_from_me, "ROOT HERE");
            close_pipe_or_perish_any_hope(circuit.trees[i]->parent_write_to_me, "ROOT HERE W");
          }
          // you're not a circuit so
          for (int i=0; i<circuit.list_len; i++) {
            if (circuit.variables[i]->type == VAR) {
              close_pipe_or_perish_any_hope(circuit.variables[i]->circuit_write_to_var, "ROOT: CIRCS PIPE");
              close_pipe_or_perish_any_hope(circuit.variables[i]->circuit_read_from_var, "ROOT: CIRCS PIPE R");
            }
          }
          processes_tree(v); //should not return
        default://circuit 
          close_pipe_or_perish_any_hope(root->write_to_parent, "CIRC: ROOT PIPE");
          close_pipe_or_perish_any_hope(root->read_from_parent, "CIRC: ROOT PIPE R");
      }
    } 
    // only circuit should step in here
    for (int i=0; i<circuit.list_len; i++) {
      ParseTree node = circuit.variables[i];
      if (node->type == VAR) {
        close_pipe_or_perish_any_hope(node->var_write_to_circuit, "CIRC: VARW");
        close_pipe_or_perish_any_hope(node->var_read_from_circuit, "CIRC: VAR READ");
      }
      if (node->is_root) {
        for (int i=0; i<node->pipes_counter; i++) {
          close_pipe_or_perish_any_hope(node->root_write_to_var[i], "CIRC: ROOTWVAR");
          close_pipe_or_perish_any_hope(node->root_read_from_var[i], "CIRC: ROOTRVAR");
          close_pipe_or_perish_any_hope(node->var_write_to_root[i], "CIRC: VARWROOT");
          close_pipe_or_perish_any_hope(node->var_read_from_root[i], "CIRC: VARRROOT");
        }
      }
    }
    line = NULL;
    len = 0;
    char *err = NULL;
    int *vars = calloc(V, sizeof(int));
    if (vars != NULL) { 
      for (int i=0; i<N-K && err == NULL; i++) {
        scanf("%d", &nr);
        if (getline(&line, &len, stdin) < 0) {
          err = "GETLINE 2";
          break;
        }
        for (int j=0; j<V; j++)
          vars[j] = 5001; //INFINITY
        char *mock_line = line;
        while (*mock_line != '\0' && err == NULL) {
          Label labell;
          NodeType nodetypel = retrieve_var(&mock_line, &labell); 
          if (nodetypel != VAR) {
            break;
          }
          Label labelr;
          NodeType nodetyper = retrieve_var(&mock_line, &labelr); 
          if (labell.var<0 || labell.var>=V || vars[labell.var] <= 5000) {
            err = "PARSING INIT LIST VAR";
            break;
          }
          vars[labell.var] = labelr.var;
          while (*mock_line != '\0' && isspace(*mock_line)) {
            ++(mock_line); 
          }
        }
        if (err == NULL) {
          if (circuit.trees[0] == NULL) {
            printf("%d F\n", nr);
          }
          else {
            broadcast_to_leaves_and_vars(vars, nr);
          }
        }
      }
      free(line);
      free(vars);
      if (err != NULL)
        looming_doom(err);
    }
    // Wait for roots
    for (int i=0; i<circuit.topo_ord_len; i++) {
      if (wait(0) == -1)
        looming_doom("WAIT ERR");
    }
  }
  looming_doom(NULL);
  printf("OJ!");
  return 1; //shoul not happen
}
