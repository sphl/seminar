#ifndef __NODE_H__
#define __NODE_H__

#include "stdlib.h"

struct node {
  struct node *next;
  char value;
};

/*@
predicate nodes(struct node *first, struct node *last, list<char> vs) =
  first == last ?
    vs == nil
  :
    first->next |-> ?next &*&
    first->value |-> ?val &*&
    malloc_block_node(first) &*&
    nodes(next, last, ?vs0) &*&
    vs == cons(val, vs0);
@*/

int nodes_count(struct node *f, struct node *l);
  //@ requires nodes(f, l, ?vs);
  //@ ensures nodes(f, l, vs) &*& result == length(vs);

bool nodes_contains(struct node *f, struct node *l, char c);
  //@ requires nodes(f, l, ?vs);
  //@ ensures nodes(f, l, vs) &*& result == mem(c, vs);

/* __NODE_H__ */