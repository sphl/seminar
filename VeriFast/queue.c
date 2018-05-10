#include "stdlib.h"

struct node {
  struct node *next;
  char value;
};

/*@
predicate nodes(struct node *first, struct node *last, list<char> values) =
  first == last ?
      values == nil
  :
      first->next |-> ?next &*&
      first->value |-> ?value &*&
      malloc_block_node(first) &*&
      nodes(next, last, ?values0) &*&
      values == cons(value, values0);
@*/

/*@
lemma void nodes_add(struct node *first)
  requires nodes(first, ?last, ?values) &*&
      last->next |-> ?next &*&
      last->value |-> ?value &*&
      malloc_block_node(last) &*&
      next->next |-> ?nextNext;
  ensures nodes(first, next, append(values, cons(value, nil)))
      &*& next->next |-> nextNext;
{
  open nodes(first, last, values);
  if (first == last) {
      close nodes(next, next, nil);
  } else {
      nodes_add(first->next);
  }
  close nodes(first, next, _);
}
@*/

struct queue {
  struct node *first;
  struct node *last;
};

/*@
predicate queue(struct queue *q, list<char> values) =
  q->first |-> ?first &*&
  q->last |-> ?last &*&
  malloc_block_queue(q) &*&
  nodes(first, last, values) &*&
  last->next |-> _ &*&
  last->value |-> _ &*&
  malloc_block_node(last);
@*/

struct queue *create()
  //@ requires true;
  //@ ensures queue(result, nil);
{
  struct queue *q = malloc(sizeof(struct queue));
  if (q == 0) {
    abort();
  }
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) {
    free(q);
    abort();
  }
  q->first = n;
  q->last = n;
  //@ close nodes(n, n, nil);
  //@ close queue(q, nil);
  return q;
}

bool is_empty(struct queue *q)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == (vs == nil);
{
  //@ open queue(q, vs);
  //@ open nodes(q->first, q->last, vs);
  bool res = (q->first == q->last);
  //@ close nodes(q->first, q->last, vs);
  //@ close queue(q, vs);
  return res;
}

int nodes_count(struct node *f, struct node *l)
  //@ requires nodes(f, l, ?vs);
  //@ ensures nodes(f, l, vs) &*& result == length(vs);
{
  //@ open nodes(f, l, vs);
  int res = 0;
  if (f != l) {
    int cnt = nodes_count(f->next, l);
    res = cnt + 1;
  }
  //@ close nodes(f, l, vs);
  return res;
}

int count(struct queue *q)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == length(vs);
{
  //@ open queue(q, vs);
  int cnt = nodes_count(q->first, q->last);
  //@ close queue(q, vs);
  return cnt;
}

bool nodes_contains(struct node *f, struct node *l, char c)
  //@ requires nodes(f, l, ?vs);
  //@ ensures nodes(f, l, vs) &*& result == mem(c, vs);
{
  //@ open nodes(f, l, vs);
  bool res = false;
  if (f != l) {
    bool cmp = (f->value == c);
    bool tmp = nodes_contains(f->next, l, c);
    res = (cmp || tmp);
  }
  //@ close nodes(f, l, vs);
  return res;
}

bool contains(struct queue *q, char c)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == mem(c, vs);
{
  //@ open queue(q, vs);
  bool res = nodes_contains(q->first, q->last, c);
  //@ close queue(q, vs);
  return res;
}

void enqueue(struct queue *q, char c)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, append(vs, cons(c, nil)));
{
  //@ open queue(q, vs);
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) {
    abort();
  }
  q->last->next = n;
  q->last->value = c;
  q->last = n;
  //@ nodes_add(q->first);
  //@ close queue(q, _);
}

char dequeue(struct queue *q)
  //@ requires queue(q, ?vs) &*& vs != nil;
  //@ ensures queue(q, ?vs0) &*& vs == cons(result, vs0);
{
  //@ open queue(q, _);
  struct node *n = q->first;
  //@ open nodes(n, _, _);
  char result = n->value;
  q->first = n->next;
  free(n);
  //@ close queue(q, _);
  return result;
}

bool dequeue2(struct queue *q, char *c)
  //@ requires queue(q, ?vs) &*& character(c, _);
  /*@
  ensures queue(q, ?vs0) &*& character(c, _) &*&
    (length(vs) == 0) ?
      result == false &*& vs0 == vs
    :
      result == true &*& vs0 == tail(vs);
  @*/
{
  int cnt = count(q);
  if (cnt == 0) {
    return false;
  } else {
    //@ open queue(q, _);
    struct node *n = q->first;
    //@ open nodes(n, _, _);
    *c = n->value;
    q->first = n->next;
    free(n);
    //@ close queue(q, _);
    return true;
  }
}

void dispose(struct queue *q)
  //@ requires queue(q, _);
  //@ ensures true;
{
  int cnt = count(q);
  //@ open queue(q, _);
  struct node *l = q->last;
  struct node *n = q->first;
  while (cnt > 0)
    //@ invariant nodes(n, l, ?vs) &*& cnt == length(vs);
  {
    //@ open nodes(n, l, _);
    struct node *tmp = n->next;
    free(n);
    n = tmp;
    cnt--;
  }
  assert(cnt == 0);
  // Don't forget to destroy the last node!
  //@ open nodes(n, l, _);
  free(l);
  free(q);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct queue *q = create();
  enqueue(q, 'a');
  enqueue(q, 'b');
  enqueue(q, 'c');
  enqueue(q, 'd');
  enqueue(q, 'e');

  char c1 = dequeue(q);
  assert(c1 == 'a');

  char c2 = dequeue(q);
  assert(c2 == 'b');

  bool b1 = contains(q, 'c');
  assert(b1 == true);

  bool b2 = is_empty(q);
  assert(b2 == false);

  int n1 = count(q);
  assert(n1 == 3);

  dispose(q);
  return 0;
}