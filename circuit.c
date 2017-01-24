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
  bool visited;
  bool is_root;
  int post;
  int id;
  //if node is a root this pipes connect it with nodes labeled with varaible it represents
  int *root_pipes_w;
  int *root_pipes_r;
  //if node is a leaf labeled with variable it is the index to root_pipe of corresponding tree
  int pipe_id;
  int pipes_counter;
  int pipes_list_cap;
  //pipes to communicate circuit with variables roots 
  int read; //from circuit
  int write; //to root
  int pnum_pipes[2]; //if you are a pnum, circut must message you there's propagation needed
} *ParseTree;

struct Circuit {
  int V;
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
int init_circuit(int V) {
  int DEFAULT_BUF_CAP = 2*V;
  circuit.V = V;
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
    if (circuit.variables[i]->root_pipes_w != NULL) {
      free(circuit.variables[i]->root_pipes_w);
      free(circuit.variables[i]->root_pipes_r);
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
  for (int v=0; v<circuit.V; v++) {
    if (circuit.trees[v] != NULL) {
      circuit.trees[v]->visited = false;
      circuit.trees[v]->post = -1;
    }
  }
  for (int v=0; v<circuit.V; v++) {
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

int register_pipe(ParseTree varLabeledLeaf) {
  int v = varLabeledLeaf->label.var;
  ParseTree root = circuit.trees[v];
  if (root->root_pipes_w == NULL) {
    int DEFAULT_PIPES_QUANT = 1;
    root->root_pipes_w = (int *) calloc(DEFAULT_PIPES_QUANT, sizeof(*(root->root_pipes_w)));
    root->root_pipes_r = (int *) calloc(DEFAULT_PIPES_QUANT, sizeof(*(root->root_pipes_r)));
    root->pipes_list_cap = DEFAULT_PIPES_QUANT;
  }
  else if (root->pipes_counter == root->pipes_list_cap) {
    int nsize = root->pipes_list_cap * 2;
    int *n_w = realloc(root->root_pipes_w, sizeof(*(root->root_pipes_w))*nsize);
    if (n_w == NULL)
      return -1;
    int *n_r = realloc(root->root_pipes_r, sizeof(*(root->root_pipes_r))*nsize);
    if (n_r == NULL)
      return -1;
    root->root_pipes_w = n_w;
    root->root_pipes_r = n_r;
    root->pipes_list_cap = nsize;
  }
  int npipe[2];
  if (pipe(npipe) < 0)
    return -1;
  varLabeledLeaf->pipe_id = root->pipes_counter;
  root->root_pipes_r[root->pipes_counter] = npipe[0];
  root->root_pipes_w[root->pipes_counter++] = npipe[1];
  return 0;
}

int extern_var(ParseTree tree) {
  if (tree->type == VAR) {
    if (circuit.trees[tree->label.var] != NULL && register_pipe(tree) < 0)
      return -1;
  }
  else if (tree->type == PNUM) {
    if (pipe(tree->pnum_pipes) < 0)
      return -1;
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

void listen(ParseTree self, int parent_dsc) {
  int entries = 0;
  if (self->is_root)
    entries += 1;
  if (self->type == PNUM || self->type == UNARY)
    entries += 1;
  else if (self)
  if (self->type == PNUM) {
    Mes mes;
    while (read(self->pnum_pipes[0], &mes, sizeof(mes)))
      write(parent_dsc, &mes, sizeof(mes));
  }
  else if ()
}

/* Map ParseTree to process tree */ 
void proc_node(ParseTree self, int x) {
  // desc to parent or circut if t is the root
  int parent = self->read;
  int lpipes[2], rpipes[2];
  bool parent_proc = false;
  while (!parent_proc && (self->type == BINARY || self->type == UNARY)) {
    if (pipe(rpipes) < 0) {
      looming_doom("PIPES BETWEEN TREE NODES R");
    }
    switch (fork()) {
      case -1:
        looming_doom("FORK IN PROC_NODE");
      case 0: 
        close(rpipes[0]);
        close(parent); // close socket to grandparent
        parent = rpipes[1];
        self = self->right;
        break;
      default: 
        close(rpipes[1]);
        parent_proc = true;
    }
    if (self->type == BINARY) {
      if (pipe(lpipes) < 0) {
        looming_doom("PIPES BETWEEN TREE NODES L");
      }
      switch (fork()) {
        case -1:
          looming_doom("FORK IN PROC_NODE");
        case 0: 
          self = self->left;
          close(lpipes[0]);
          close(rpipes[0]);
          close(parent); // close socket to grandparent
          parent = lpipes[1];
          break;
        default: 
          close(lpipes[1]);
      }
    }
  }
  // close propagated descriptors from circuit to PNUM leaves (apart from the one for [self])
  for (int i=0; i<circuit.list_len; i++) {
    ParseTree node = circuit.variables[i];
    if (node->type == PNUM && node->id != self->id) {
      if (close(circuit.variables[i]->pnum_pipes[0]) < 0)
        looming_doom("CLOSE READ PIPES FOR A PNUM LEAF");
    }
  }
  // close propagated descriptors from roots to variable nodes the given root describe
  for (int v=0; v<circuit.V; v++) {
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
  listen(self, parent);
}

/* x:{X[0], .., X[V-1]}, listsq - quantity of initializations lists */
void tree_process(int x, int listsq) {
  // Close writting descriptors from roots to variables that are not yours
  for (int v=0; v<circuit.V; v++) {
    if (v == x || circuit.trees[v] == NULL)
      continue;
    ParseTree t = circuit.trees[v];
    if (t->root_pipes_w != NULL) {
      for(int i=0; i<t->pipes_counter; i++) {
        if (close(t->root_pipes_w[i]) < 0)
          looming_doom("CLOSE WRITE PIPES FOR OTHER ROOTS");
      }
    }
  }
  // Close wrtting descriptors of PNUM leaves (they are propagated so that circut could directly
  // prompt them to pass their value down the graph)
  for (int i=0; i<circuit.list_len; i++) {
    if (circuit.variables[i]->type == PNUM) {
      if (close(circuit.variables[i]->pnum_pipes[1]) < 0)
        looming_doom("CLOSE WRITE PIPES FOR A PNUM LEAF");
    }
  }
  proc_node(circuit.trees[x], x);
  looming_doom(NULL);
}

bool can_be_computed(ParseTree t, int *vars) {
  if (t == NULL)
    return false;
  else if (t->type == PNUM)
    return true;
  else if (t->type == VAR) {
    if (vars[t->label.var] <= 5000) //not an inifity - was defined
      return true;
    else {
      ParseTree var = circuit.trees[t->label.var];
      return can_be_computed(var, vars);
    }
  }
  else if (t->type == BINARY || t->type == UNARY) {
    return can_be_computed(t->right, vars) && (t->type != BINARY || can_be_computed(t->left, vars));
  }
  return false;
}

void broadcast_to_leaves_and_vars(int *vars, int q) {
  int mes_id = q-K;
  for (int x=0; x<circuit.V; x++) {
    if (vars[x] <= 5000) { //was defined
      Mes mes;
      mes.i = mes_id;
      mes.val = vars[x];
      write(circuit.trees[x]->write, &mes, sizeof(mes));
    }
  }
  //give sign for leaves to propagate values for i-th query
  Mes mes;
  mes.i = mes_id;
  mes.val = -1;
  for (int v=0; v<circuit.list_len; v++) {
    if (circuit.variables[v]->type == PNUM) {
      write(circuit.variables[v]->pnum_pipes[1], &mes, sizeof(mes));
    }
  }
  for (int x=0; x<circuit.V; x++) {
    if (circuit.trees[x] != NULL) {
      write(circuit.trees[x]->write, &mes, sizeof(mes));
    }
  }
}

int main() {
  scanf("%d%d%d", &N, &K, &V);
  if (init_circuit(V) == 0) {
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
    for (int v=0; v<circuit.V; v++) {
      if (circuit.trees[v] == NULL)
        continue;
      int pipes[2];
      if (pipe(pipes) == -1)
        looming_doom("PIPE IN CIRC");
      circuit.trees[v]->read = pipes[0];
      circuit.trees[v]->write = pipes[1];
      switch (fork()) {
        case -1:
          looming_doom("FORK IN CIRC");
        case 0: //root process of variable v
          for (int i=v; i>=0; i--) {
            close(circuit.trees[v]->write);
          }
          tree_process(v, N-K); //should not return
        default://circuit 
          close(circuit.trees[v]->read);
      }
    }
    // only circuit should step in here
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
          if (circuit.trees[0] == NULL || (vars[0]>5000 && !can_be_computed(circuit.trees[0], vars))) {
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
