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
} *ParseTree;

struct Circuit {
  int V;
  //a list of all the nodes allocated within program, handy in terms of resource management
  ParseTree *variables;
  size_t list_len; //number on nodes in a variables array
  size_t list_cap; //capacity of variables
  ParseTree *trees; //x[0], .., x[V - 1] varaibles as a roots of trees representing its equations
} circuit;


/* Initiates [circuit] structure making allowance for arguments passed by user */
int init_circuit(int V) {
  int DEFAULT_BUF_CAP = 2*V;
  circuit.V = V;
  circuit.variables = (ParseTree *) calloc(DEFAULT_BUF_CAP, sizeof(*circuit.variables));
  if (circuit.variables == NULL)
    return -1;
  circuit.list_cap = DEFAULT_BUF_CAP;
  circuit.trees = (ParseTree *) calloc(V, sizeof(*circuit.trees));
  if (circuit.trees == NULL)
    return -1;
  return 0;
}

/* Frees memory storing [circuit] elements. */
void free_circuit() {
  free(circuit.trees);
  free(circuit.variables);
}

/* Frees memeory used to store nodes that have been registered when created. */
void free_nodes() {
  for (int i=circuit.list_len-1; i>=0; i--)
    free(circuit.variables[i]);
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

/* And now somethng completely different. */
void looming_doom() {
  free_nodes();
  free_circuit();
}

int main() {
  int N, K, V, nr;
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
        printf ("%d F", nr);
        break;
      }
      while (*mock_line != '\0' && (isspace(*mock_line) || *mock_line == '='))
        ++mock_line;
      ParseTree tree = parse_line(&mock_line, NULL, NULL);
      if (tree == NULL)
        break;
      print_tree(tree);
      circuit.trees[label.var] = tree;
    }
    free(line);
  }
  looming_doom();
  return 0;
}
