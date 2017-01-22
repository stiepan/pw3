#include <stdio.h>
#include <ctype.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <stdbool.h>
#include "err.h"

typedef enum NodeType {
  PNUM, VAR, UNARY, BINARY, UNRECOGNIZED_TYPE_ERR
} NodeType;

typedef union {
    int num;
    int var;
    char op;
} Label;

typedef struct Node {
  NodeType type;
  Label label;
  struct Node *left, *right;
} *ParseTree;

struct Circuit {
  int V;
  //for 0<=i<V variable[i] is an array of nodes labeled with X[i] variable, variable[V] is
  //a list of all the nodes allocated within program, handy in terms of resource management
  ParseTree **variables; // variable[i] is an array of nodes labeled with X[i] variable
  size_t *list_len; //number on nodes in a variable[i] array
  size_t *list_cap; //capacity of variable[i] array
  ParseTree *trees; //x[0], .., x[V - 1] varaibles as a roots of trees representing its equations
} circuit;

int init_circuit(int V) {
  int const DEFAULT_CAP = 2;
  int const DEFAULT_BUF_CAP = 2*V;
  circuit.V = V;
  circuit.list_len = (size_t *) calloc(V + 1, sizeof(*circuit.list_len));
  circuit.list_cap = (size_t *) calloc(V + 1, sizeof(*circuit.list_cap));
  circuit.variables = (ParseTree **) calloc(V + 1, sizeof(*circuit.variables));
  if (circuit.variables == NULL || circuit.list_len == NULL || circuit.list_cap == NULL)
    return -1;
  for (int v=0; v<V; v++) {
    circuit.variables[v] = (ParseTree *) calloc(DEFAULT_CAP, sizeof(*circuit.variables[v]));
    if (circuit.variables[v] == NULL)
      return -1;
    circuit.list_cap[v] = DEFAULT_CAP;
  }
  circuit.variables[V] = (ParseTree *) calloc(DEFAULT_BUF_CAP, sizeof(*circuit.variables[V])); 
  circuit.list_cap[V] = DEFAULT_BUF_CAP;
  circuit.trees = (ParseTree *) calloc(V, sizeof(*circuit.trees));
  if (circuit.variables[V] == NULL || circuit.trees == NULL)
    return -1;
  return 0;
}

void free_circuit() {
  free(circuit.trees);
  for (int i=0; i<circuit.list_len[circuit.V]; i++)
    free(circuit.variables[circuit.V][i]);
  for (int v=0; v<=circuit.V; v++) {
    if (circuit.variables[v] == NULL)
      break;
    free(circuit.variables[v]);
  }
  free(circuit.variables);
  free(circuit.list_cap);
  free(circuit.list_len);
}

int register_node(int v, ParseTree t) {
  if (circuit.list_cap[v] == circuit.list_len[v]) {
    size_t nsize = circuit.list_cap[v] * 2;
    ParseTree *narray = (ParseTree *) realloc(circuit.variables[v],
                                              sizeof(circuit.variables[v]) * nsize);
    if (narray == NULL)
      return -1;
    circuit.variables[v] = narray;
    circuit.list_cap[v] = nsize;
  }
  circuit.variables[v][circuit.list_len[v]++] = t;
  return 0;
}

ParseTree new_tree(NodeType type, Label label) { 
  ParseTree tree = NULL;
  tree = (ParseTree) calloc(1, sizeof(*tree));
  if (tree == NULL)
    return NULL;
  register_node(circuit.V, tree);
  tree->label = label;
  tree->type = type;
  return tree;
}

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
    while (isdigit(*(*line)++));
    label->num = n;
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
  }
  return type;
}

ParseTree parse_line(ParseTree nop, ParseTree op, char *line, int blevel) {
  while (*line != '\0') {
    Label label;
    NodeType nodetype;
    while (*line != '\0' && (isspace(*line) || *line == '(')) {
      ++line;
      blevel += (*line == '(');
    }
    if (*line == ')') {
      if (blevel == 0)
        return NULL;
      --blevel;
      return nop;
    }
    if ((nodetype = retrieve_var(&line, &label)) == UNRECOGNIZED_TYPE_ERR)
      return NULL;
  }
  int var = retrieve_var(&line);
  printf("x[%d]\n", var);
  return 0;
}


// and now somethng completely different
void looming_doom() {
  free_circuit();
}

int main() {
  int N, K, V;
  scanf("%d%d%d", &N, &K, &V);
  if (init_circuit(V + 1) == 0) {
    char *line = NULL;
    size_t len = 0;
    for (int k=1; k<=K; k++) {
      int nr;
      scanf("%d", &nr);
      if (getline(&line, &len, stdin) < 0)
        break;
      char *mock_line = line;
      Label label;
      NodeType nodetype = retrieve_var(&mock_line, &label);
      if (nodetype == VAR) // right side of equation ought to be x[]
        break;
      while(*mock_line != '\0' && (isspace(*mock_line) || *mock_line == '='))
        ++mock_line;
      ParseTree tree = parse_line(mock_line, NULL, NULL);
      if (tree = NULL)
        break;
      circuit.tree[label.var] = tree;
    }
    free(line);
  }
  looming_doom();
  return 0;
}
