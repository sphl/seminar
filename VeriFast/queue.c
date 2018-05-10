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

struct fifo {
  struct node *first;
  struct node *last;
};

/*@
predicate fifo(struct fifo *fifo, list<char> values) =
  fifo->first |-> ?first &*&
  fifo->last |-> ?last &*&
  malloc_block_fifo(fifo) &*&
  lseg(first, last, values) &*&
  last->next |-> _ &*& last->value |-> _ &*&
  malloc_block_node(last);
@*/

struct fifo *create()
  //@ requires true;
  //@ ensures fifo(result, nil);
{
  struct fifo *fifo = malloc(sizeof(struct fifo));
  if (fifo == 0) {
    abort();
  }
  struct node *node = malloc(sizeof(struct node));
  if (node == 0) {
    free(fifo);
    abort();
  }
  fifo->first = node;
  fifo->last = node;
  //@ close lseg(node, node, nil);
  //@ close fifo(fifo, nil);
  return fifo;
}

int count(struct fifo *fifo)
  //@ requires fifo(fifo, ?vs);
  //@ ensures fifo(fifo, vs) &*& result == length(vs);
{
  //@ open fifo(fifo, vs);
  
}

void enqueue(struct fifo *fifo, char c)
  //@ requires fifo(fifo, ?vs);
  //@ ensures fifo(fifo, ?vs0) &*& vs0 == append(vs, cons(c, nil));
{
  //@ open fifo(fifo, vs);
  struct node *node = malloc(sizeof(struct node));
  if (node == 0) {
    abort();
  }
  fifo->last->next = node;
  fifo->last->value = c;
  fifo->last = node;
  //@ lseg_add(fifo->first);
  //@ close fifo(fifo, _);
}

char dequeue(struct fifo *fifo)
  //@ requires fifo(fifo, ?vs) &*& vs != nil;
  //@ ensures fifo(fifo, ?vs0) &*& vs == cons(result, vs0);
{
  //@ open fifo(fifo, _);
  struct node *node = fifo->first;
  //@ open lseg(node, _, _);
  char result = node->value;
  fifo->first = node->next;
  free(node);
  //@ close fifo(fifo, _);
  return result;
}

void dispose(struct fifo *fifo)
  //@ requires fifo(fifo, nil);
  //@ ensures true;
{
  //@ open fifo(fifo, nil);
  //@ open lseg(_, _, _);
  free(fifo->first);
  free(fifo);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct fifo *fifo = create();
  enqueue(fifo, 'a');
  enqueue(fifo, 'b');
  char c1 = dequeue(fifo);
  assert(c1 == 'a');
  char c2 = dequeue(fifo);
  assert(c2 == 'b');
  dispose(fifo);
  return 0;
}
