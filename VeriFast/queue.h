#ifndef __QUEUE_H__
#define __QUEUE_H__

#include "stdlib.h"

/*@
fixpoint t last<t>(list<t> xs) {
  return head(reverse(xs));
}
@*/

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

struct queue {
  struct node *first;
  struct node *last;
};

/*@
predicate queue(struct queue *q, list<char> vs) =
  q->first |-> ?first &*&
  q->last |-> ?last &*&
  malloc_block_queue(q) &*&
  nodes(first, last, vs) &*&
  last->next |-> _ &*&
  last->value |-> _ &*&
  malloc_block_node(last);
@*/

struct queue *create();
  //@ requires true;
  //@ ensures queue(result, nil);

bool is_empty(struct queue *q);
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == (vs == nil);

int count(struct queue *q);
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == length(vs);

bool contains(struct queue *q, char c);
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == mem(c, vs);

void enqueue(struct queue *q, char c);
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, append(vs, cons(c, nil)));

/*
 * This is just a prototype that can be useful when
 * trying to implement a circular buffer.
 */
void enqueue2(struct queue *q, char c, int limit);
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, ?vs0) &*& last(vs0) == c;

char dequeue(struct queue *q);
  //@ requires queue(q, ?vs) &*& vs != nil;
  //@ ensures queue(q, ?vs0) &*& vs == cons(result, vs0);

bool dequeue2(struct queue *q, char *c);
  //@ requires queue(q, ?vs) &*& character(c, _);
  /*@
  ensures queue(q, ?vs0) &*& character(c, _) &*&
    (length(vs) == 0) ?
      result == false &*& vs0 == vs
    :
      result == true &*& vs0 == tail(vs);
  @*/

void destroy(struct queue *q);
  //@ requires queue(q, _);
  //@ ensures true;

#endif /* QUEUE_H */
