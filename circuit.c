#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <stdbool.h>
#include <poll.h>
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
  bool *root_pending_vars;
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
  bool err;
} Mes;

int const NODES_MAX = 1000;
int const INFINITY = 5001;

Mes *message = NULL;

int N, K, V, nr;

/* Initiates [circuit] structure making allowance for arguments passed by user */
int init_circuit() {
  int DEFAULT_BUF_CAP = 2*V;
  circuit.variables = (ParseTree *) calloc(DEFAULT_BUF_CAP, sizeof(*circuit.variables));
  if (circuit.variables == NULL)
    return -1;
  circuit.list_cap = DEFAULT_BUF_CAP;
  circuit.trees = (ParseTree *) calloc(NODES_MAX, sizeof(*circuit.trees));
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
  free(message);
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
  // end of currently processed expression, pop the operator and combine it with variable from the top,
  // if the operator is binary one it will have its left child added in the parent of recursion tree
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
      // if it's variable or numeral put it on the top of the [nop] stack
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
  for (int v=0; v<NODES_MAX; v++) {
    if (circuit.trees[v] != NULL) {
      circuit.trees[v]->visited = false;
      circuit.trees[v]->post = -1;
    }
  }
  for (int v=0; v<NODES_MAX; v++) {
    if (circuit.trees[v] != NULL && (!(circuit.trees[v]->visited))) {
      if (dfs(circuit.trees[v], v) < 0)
        return -1;
    }
  }
  return 0;
}

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

void send_message(int to, int i, long val, bool err) {
  if (message == NULL)
    message = calloc(1, sizeof(*message));
  if (message == NULL) {
    looming_doom("CALLOC IN SM");
  }
  message->i = i;
  message->val = val;
  message->err = err;
  if (write(to, message, sizeof(*message)) <= 0)
    looming_doom("WRITE IN SM");
}

void pnum_response(ParseTree self, int i, int from) {
  int write2 = (from == 0)? self->write_to_parent : self->root_write_to_var[from-1]; 
  send_message(write2, i, self->label.var, false);
}

void broadcast(ParseTree self, int x, int *cache_status, long *cached, int i, long val, int status) {
  if (cache_status[i] <= 0) {
    if (status) {
      cache_status[i] = 1;
    }
    else {
      cache_status[i] = 2;
      cached[i] = val;
    }
  }
  if (!self->is_root || x == 0) // trees different than 0 should not respond to parent (circuit)
    send_message(self->write_to_parent, i, val, status);
  for (int j=0; j<self->pipes_counter; j++) {
    send_message(self->root_write_to_var[j], i, val, status);
  }
}

void send_cached(ParseTree self, int *cache_status, long *cached, Mes *mes, int from, int n) {
  if (cache_status[mes->i] > 0) { //already responded for this query
    if (from < n) { // it was actually a query not some delayed response
      int write2 = (from == 0) ? self->write_to_parent : self->root_write_to_var[from-1];
      if (cache_status[mes->i] == 1) { //not possible to compute value with given initial list
        send_message(write2, mes->i, 0, true);
      }
      else {
        send_message(write2, mes->i, cached[mes->i], false);
      }
    }
  }
}

void op_response(ParseTree self, int x, int *cache_status, long *cached, Mes *mes, int from, int n) {
  if (cache_status[mes->i] > 0) { //already responded for this query
    send_cached(self, cache_status, cached, mes, from, n);
  }
  else if (cache_status[mes->i] == 0) { //know nothing, ask children
    cache_status[mes->i] = -1;
    send_message(self->right->parent_write_to_me, mes->i, 0, false);
    if (self->type == BINARY)
      send_message(self->left->parent_write_to_me, mes->i, 0, false);
  }
  else { //waiting for children's 
    if (from >= n) { //so only children should be indeed waited on
      if (mes->err) { // one of the subtrees cannot be comptued with given init list 
        broadcast(self, x, cache_status, cached, mes->i, 0, true);
      }
      else {
        if (self->type == UNARY) {
          broadcast(self, x, cache_status, cached, mes->i, -mes->val, false);
        }
        else {
          if (cache_status[mes->i] == -2) {
            long val = cached[mes->i];
            val = (self->label.op == '+')? val + mes->val : val * mes->val;
            broadcast(self, x, cache_status, cached, mes->i, val, false);
          }
          else {
            cache_status[mes->i] = -2;
            cached[mes->i] = mes->val;
          }
        }
      }
    }
  }
}

void var_response(ParseTree self, int x, int *cache_status, long *cached, Mes *mes, int from, int n) {
  if (cache_status[mes->i] > 0) { //already responded for this query
    send_cached(self, cache_status, cached, mes, from, n);
  }
  else if (cache_status[mes->i] == 0) { //know nothing, ask circuit
    cache_status[mes->i] = -1;
    send_message(self->var_write_to_circuit, mes->i, 0, false);
  }
  else if (cache_status[mes->i] == -1) { //waiting for circuit response
    if (from == n) { //so only circuit should be indeed waited on
      if (!mes->err) {
        broadcast(self, x, cache_status, cached, mes->i, mes->val, false);
      }
      else { //there was no value in the init list for this variable
        ParseTree treevar = circuit.trees[self->label.var];
        if (treevar == NULL) {
          broadcast(self, x, cache_status, cached, mes->i, 0, true);
        }
        else {
          cache_status[mes->i] = -2;
          send_message(treevar->var_write_to_root[self->pipe_id], mes->i, 0, false);
        }
      }
    }
  }
  else if (cache_status[mes->i] == -2) { //waiting for the response from root repesenting var's label
    if (from == n+1) {
      broadcast(self, x, cache_status, cached, mes->i, mes->val, mes->err);
    }
  }
}

void listen(ParseTree self, int x) {
  int *cache_status = NULL;
  long *cached = NULL;
  struct pollfd *entries = NULL;
  Mes message;
  if (self->type != PNUM) {
    cache_status = calloc(N-K, sizeof(int));
    cached = calloc(N-K, sizeof(long));
    if (cache_status == NULL || cached == NULL)
      looming_doom("CACHE CALLOC");
  }
  //readpoll table: [parentNode][pipes from var leaves if you are a root][var/opartor pipes]
  size_t n=1;
  if (self->is_root) {
    n += self->pipes_counter;
  }
  int oftype = 0;
  entries = calloc(n+2, sizeof(*entries));
  entries[0].fd = self->read_from_parent;
  entries[0].events = POLLIN;
  for (int i=0; i<self->pipes_counter; i++) {
    entries[i+1].events = POLLIN;
    entries[i+1].fd = self->root_read_from_var[i];
  }
  if (self->type == BINARY || self->type == UNARY) {
    entries[n+oftype].events = POLLIN;
    entries[n+oftype].fd = self->right->parent_read_from_me;
    oftype += 1;
    if (self->type == BINARY) {
      entries[n+oftype].events = POLLIN;
      entries[n+(oftype++)].fd = self->left->parent_read_from_me;
    }
  }
  else if (self->type == VAR) {
    entries[n+oftype].events = POLLIN;
    entries[n+oftype++].fd = self->var_read_from_circuit;
    ParseTree treevar = circuit.trees[self->label.var];
    if (treevar != NULL) {
      entries[n+oftype].events = POLLIN;
      entries[n+oftype].fd = treevar->var_read_from_root[self->pipe_id];
      oftype += 1;
    }
  }
  bool finish = false;
  int ret, len;
  while (!finish) {
    for (int i=0; i<n+oftype; i++)
      entries[i].revents = 0;
    if ((ret = poll(entries, n+oftype, -1)) < 0) {
      looming_doom ("POLL READ CHILD");
    }
    else if (ret > 0) {
      for (int i=0; i<n+oftype; i++) {
        if (entries[i].revents & POLLHUP) {
          finish = true; //pipe is closed
        }
        if (entries[i].revents & (POLLIN | POLLERR)) {
          if ((len = read(entries[i].fd, &message, sizeof(message))) == -1)
            looming_doom("READ IN CHILD");
          if (len == 0) {
            finish = true;
          }
          else {
            switch(self->type) {
              case PNUM:
                pnum_response(self, message.i, i);
                break;
              case VAR:
                var_response(self, x, cache_status, cached, &message, i, n);
                break;
              case BINARY:
              case UNARY:
                op_response(self, x, cache_status, cached, &message, i, n);
                break;
              default:
                looming_doom("NODE TYPE ERR");
            }
          }
        }
      }
    }
  }
  free(entries);
  free(cached);
  free(cache_status);
}

/* x:{X[0], .., X[V-1]} */
void processes_tree(int x) {
  //Tree x defienietly doesn't need other trees' descriptors to write to var labeled leaves 
  ParseTree self = circuit.trees[x];
  for (int i=0; i<NODES_MAX; i++) {
    ParseTree root = circuit.trees[i];
    if (i == x || root == NULL) {
      continue;
    }
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
          if (i == 0) {
            self = self->right;
          }
          else { //you're the second child
            close_pipe_or_perish_any_hope(self->right->parent_read_from_me, "LEFT CHILD");
            close_pipe_or_perish_any_hope(self->right->parent_write_to_me, "LEFT CHILD W");
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
  //we have the whole tree, so all 'to be propagated' pipes reached thier destination;
  //close copies that missed the point
  for (int i=0; i<circuit.list_len; i++) {
    ParseTree node = circuit.variables[i];
    if (node->type == VAR && !(self->type == VAR && self->id == node->id)) {
      close_pipe_or_perish_any_hope(node->var_write_to_circuit, "UNNEC VAR CIRC");
      close_pipe_or_perish_any_hope(node->var_read_from_circuit, "UNNEC VAR CIRC R");
    } 
  }
  for (int v=0; v<NODES_MAX; v++) {
    ParseTree node = circuit.trees[v];
    if (node == NULL)
      continue;
    for (int i=0; i<node->pipes_counter; i++) {
      if (self->type == VAR && self->label.var == v && self->pipe_id == i)
        continue;
      close_pipe_or_perish_any_hope(node->var_write_to_root[i], "UNNEC TO ROOT");
      close_pipe_or_perish_any_hope(node->var_read_from_root[i], "UNNEC TO ROOT R");
    }
  }
  listen(self, x);
  if (self->type == BINARY || self->type == UNARY) {
    close(self->right->parent_write_to_me);
    if (self->type == BINARY)
      close(self->left->parent_write_to_me);
  }
  for (int i=0; i < 2*(self->type == BINARY) + (self->type == UNARY); i++) {
    if (wait(0) == -1)
      looming_doom("WAIT ERR");
  }
  looming_doom(NULL);
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
      circuit.trees[label.var] = tree;
      tree->is_root = true;
      if (topo_sort() < 0) {
        printf("%d F\n", nr);
        free(line);
        looming_doom(NULL);
      }
      else {
        printf("%d P\n", nr);
      }
    }
    fflush(stdout);
    free(line);
    if (prepare_non_tree_pipes() < 0) {
      looming_doom("PREP NON TREE PIPES");
    }
    for (int v=circuit.topo_ord_len - 1; v>=0; v--) {
      ParseTree root = circuit.trees[circuit.topo_ord[v]];
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
          for (int i=v; i < circuit.topo_ord_len; i++) {
            ParseTree droot = circuit.trees[circuit.topo_ord[i]];
            close_pipe_or_perish_any_hope(droot->parent_read_from_me, "ROOT HERE");
            close_pipe_or_perish_any_hope(droot->parent_write_to_me, "ROOT HERE W");
          }
          // you're not a circuit so
          for (int i=0; i<circuit.list_len; i++) {
            if (circuit.variables[i]->type == VAR) {
              close_pipe_or_perish_any_hope(circuit.variables[i]->circuit_write_to_var, "ROOT: CIRCS PIPE");
              close_pipe_or_perish_any_hope(circuit.variables[i]->circuit_read_from_var, "ROOT: CIRCS PIPE R");
            }
          }
          processes_tree(circuit.topo_ord[v]); //should not return
        default://circuit 
          close_pipe_or_perish_any_hope(root->write_to_parent, "CIRC: ROOT PIPE");
          close_pipe_or_perish_any_hope(root->read_from_parent, "CIRC: ROOT PIPE R");
      }
    } 
    size_t how_many_labeled_vars = 0;
    // only circuit should step in here
    for (int i=0; i<circuit.list_len; i++) {
      ParseTree node = circuit.variables[i];
      if (node->type == VAR) {
        ++how_many_labeled_vars;
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
    int *vars = calloc(NODES_MAX*(N-K), sizeof(int));
    int *labels = calloc(N-K, sizeof(int));
    if (vars == NULL || labels == NULL)
      looming_doom("VARS");
    for (int j=0; j<NODES_MAX*(N-K); j++)
      vars[j] = INFINITY; //INFINITY
    for (int i=0; i<N-K && err == NULL; i++) {
      scanf("%d", &nr);
      labels[i] = nr;
      if (getline(&line, &len, stdin) < 0) {
        err = "GETLINE 2";
        break;
      }
      char *mock_line = line;
      while (*mock_line != '\0' && err == NULL) {
        Label labell;
        NodeType nodetypel = retrieve_var(&mock_line, &labell); 
        if (nodetypel != VAR) {
          break;
        }
        Label labelr;
        NodeType nodetyper = retrieve_var(&mock_line, &labelr); 
        if (labell.var<0 || labell.var>=NODES_MAX || vars[i*NODES_MAX + labell.var] < INFINITY) {
          err = "PARSING INIT LIST VAR";
          break;
        }
        vars[i*NODES_MAX + labell.var] = labelr.var;
        while (*mock_line != '\0' && isspace(*mock_line)) {
          ++(mock_line); 
        }
      }
      if (err != NULL)
        looming_doom(err);
    }
    free(line);
    if (circuit.trees[0] == NULL) {
      for (int i=0; i<N-K; i++) {
        printf("%d F\n", labels[i]);
      }
    }
    else {
      Mes message;
      struct pollfd *entries = calloc(how_many_labeled_vars + 1, sizeof(struct pollfd));
      ParseTree *node2write = calloc(how_many_labeled_vars + 1, sizeof(ParseTree));
      entries[0].fd = circuit.trees[0]->parent_read_from_me;
      entries[0].events = POLLIN;
      node2write[0] = circuit.trees[0];
      size_t entq = 1;
      for (int i=0; i<circuit.list_len; i++) {
        ParseTree node = circuit.variables[i];
        if (node->type == VAR) {
          entries[entq].fd = node->circuit_read_from_var;
          entries[entq].events = POLLIN;
          node2write[entq++] = node;
        }
      }
      int answers = 0;
      for (int i=0; i<N-K; i++) {
        if (vars[i*NODES_MAX] < INFINITY) { //not an infinity
          printf("%d P %d\n", labels[i], vars[i*1000]);
          ++answers;
        }
        else {
          send_message(node2write[0]->parent_write_to_me, i, -1, false);
        }
      }
      int ret;
      bool finish = false;
      while (answers < N-K && !finish) {  
        for (int i=0; i<how_many_labeled_vars + 1; i++)
          entries[i].revents = 0;
        ret = poll(entries, how_many_labeled_vars + 1, -1);
        if ((ret) < 0) {
          looming_doom ("POLL READ CIRC");
        }
        else if (ret > 0) {
          for (int i=0; i<how_many_labeled_vars + 1; i++) {
            if (entries[i].revents & POLLHUP) {
              finish = true; //pipe is closed
            }
            if (entries[i].revents & (POLLIN | POLLERR)) {
              if ((len = read(entries[i].fd, &message, sizeof(message))) == -1)
                looming_doom("READ IN CIRC");
              if (len == 0) {
                finish = true;
              }
              else {
                if (i == 0) {
                  if (message.err)
                    printf("%d F\n", labels[message.i]);
                  else
                    printf("%d P %ld\n", labels[message.i], message.val);
                  answers++;
                }
                else {
                  long var = vars[message.i*NODES_MAX + node2write[i]->label.var];
                  if (var < INFINITY) { //not an infinity
                    send_message(node2write[i]->circuit_write_to_var, message.i, var, false);
                  }
                  else {
                    send_message(node2write[i]->circuit_write_to_var, message.i, 0, true);
                  }
                }
              }
            }
          }
        }
      }
      free(node2write);
      free(entries);
    }
    free(labels);
    free(vars);
    for (int v=0; v<NODES_MAX; v++) {
      if (circuit.trees[v] != NULL)
        close(circuit.trees[v]->parent_write_to_me);
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
