#include "stdlib.h"

struct node {
  struct node *next;
  char value;
};

/*@
predicate lseg(struct node *first, struct node *last, list<char> values) =
  first == last ?
      values == nil
  :
      first->next |-> ?next &*& first->value |-> ?value &*&
      malloc_block_node(first) &*&
      lseg(next, last, ?values0) &*&
      values == cons(value, values0);
lemma void lseg_add(struct node *first)
  requires lseg(first, ?last, ?values) &*&
      last->next |-> ?next &*& last->value |-> ?value &*&
      malloc_block_node(last) &*&
      next->next |-> ?nextNext;
  ensures lseg(first, next, append(values, cons(value, nil)))
      &*& next->next |-> nextNext;
{
  open lseg(first, last, values);
  if (first == last) {
      close lseg(next, next, nil);
  } else {
      lseg_add(first->next);
  }
  close lseg(first, next, _);
}
@*/

struct queue {
  struct node *first;
  struct node *last;
};

/*@
predicate queue(struct queue *q, list<char> values) =
  q->first |-> ?first &*& q->last |-> ?last &*&
  malloc_block_queue(q) &*&
  lseg(first, last, values) &*&
  last->next |-> _ &*& last->value |-> _ &*&
  malloc_block_node(last);
@*/

struct queue *create()
  //@ requires true;
  //@ ensures queue(result, nil);
{
  struct queue *q = malloc(sizeof(struct queue));
  if (q == 0) abort();
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  q->first = n;
  q->last = n;
  //@ close lseg(n, n, nil);
  //@ close queue(q, nil);
  return q;
}

void enqueue(struct queue *q, char c)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, append(vs, cons(c, nil)));
{
  //@ open queue(q, vs);
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) abort();
  q->last->next = n;
  q->last->value = c;
  q->last = n;
  //@ lseg_add(q->first);
  //@ close queue(q, _);
}

char dequeue(struct queue *q)
  //@ requires queue(q, ?vs) &*& vs != nil;
  //@ ensures queue(q, ?vs0) &*& vs == cons(result, vs0);
{
  //@ open queue(q, _);
  struct node *n = q->first;
  //@ open lseg(n, _, _);
  char result = n->value;
  q->first = n->next;
  free(n);
  //@ close queue(q, _);
  return result;
}

void dispose(struct queue *q)
  //@ requires queue(q, nil);
  //@ ensures true;
{
  //@ open queue(q, nil);
  //@ open lseg(_, _, _);
  free(q->first);
  free(q);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct queue *q = create();
  enqueue(q, 'a');
  enqueue(q, 'b');
  char c1 = dequeue(q);
  assert(c1 == 'a');
  char c2 = dequeue(q);
  assert(c2 == 'b');
  dispose(q);
  return 0;
}