#include "queue.h"

/*@
lemma void nodes_add(struct node *first)
  requires nodes(first, ?last, ?vs) &*&
    last->next |-> ?next &*&
    last->value |-> ?val &*&
    malloc_block_node(last) &*&
    next->next |-> ?nextNext;
  ensures nodes(first, next, ?vs0) &*&
    //vs0 == append(vs, cons(val, nil)) &*&
    vs0 == reverse(cons(val, reverse(vs))) &*&
    next->next |-> nextNext;
{
  open nodes(first, last, vs);
  if (first == last) {
      close nodes(next, next, nil);
  } else {
      nodes_add(first->next);
  }
  close nodes(first, next, _);
}
@*/

struct queue *create_queue()
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

bool queue_is_empty(struct queue *q)
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

int queue_count(struct queue *q)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == length(vs);
{
  //@ open queue(q, vs);
  int cnt = nodes_count(q->first, q->last);
  //@ close queue(q, vs);
  return cnt;
}

bool queue_contains(struct queue *q, char c)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, vs) &*& result == mem(c, vs);
{
  //@ open queue(q, vs);
  bool res = nodes_contains(q->first, q->last, c);
  //@ close queue(q, vs);
  return res;
}

void queue_enqueue(struct queue *q, char c)
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

void queue_enqueue2(struct queue *q, char c, int limit)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, ?vs0) &*& last(vs0) == c;
{
  if (queue_count(q) == limit) {
    // Dequeue first node to not exceed the limit
    char c0;
    queue_dequeue2(q, &c0);
  }
  //@ open queue(q, _);
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

char queue_dequeue(struct queue *q)
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

bool queue_dequeue2(struct queue *q, char *c)
  //@ requires queue(q, ?vs) &*& character(c, _);
  /*@
  ensures queue(q, ?vs0) &*& character(c, _) &*&
    (length(vs) == 0) ?
      result == false &*& vs0 == vs
    :
      result == true &*& vs0 == tail(vs);
  @*/
{
  if (queue_count(q) == 0) {
    //*c = '\0';
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

void queue_destroy(struct queue *q)
  //@ requires queue(q, _);
  //@ ensures true;
{
  //@ open queue(q, _);
  struct node *l = q->last;
  struct node *n = q->first;
  while (n != l)
    //@ invariant nodes(n, l, ?vs);
  {
    //@ open nodes(n, l, _);
    struct node *tmp = n->next;
    free(n);
    n = tmp;
  }
  // Don't forget to destroy the last node
  //@ open nodes(n, l, _);
  free(l);
  free(q);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct queue *q = create_queue();
  queue_enqueue(q, 'a');
  queue_enqueue(q, 'b');
  queue_enqueue(q, 'c');
  queue_enqueue(q, 'd');
  queue_enqueue(q, 'e');

  char c1 = queue_dequeue(q);
  assert(c1 == 'a');
  
  char c2 = queue_dequeue(q);
  assert(c2 == 'b');

  bool b1 = queue_contains(q, 'c');
  assert(b1);

  bool b2 = queue_is_empty(q);
  assert(!b2);

  int n1 = queue_count(q);
  assert(n1 == 3);

  queue_dequeue(q);
  queue_dequeue(q);
  queue_dequeue(q);
  
  bool b3 = queue_is_empty(q);
  assert(b3);

  queue_enqueue(q, 'e');
  queue_enqueue(q, 'f');
  queue_enqueue(q, 'g');

  queue_destroy(q);
  return 0;
}