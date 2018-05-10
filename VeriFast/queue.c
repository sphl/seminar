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

static int nodes_count(struct node *f, struct node *l)
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


static bool nodes_contains(struct node *f, struct node *l, char c)
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

void enqueue2(struct queue *q, char c, int limit)
  //@ requires queue(q, ?vs);
  //@ ensures queue(q, ?vs0) &*& last(vs0) == c;
{
  if (count(q) == limit) {
    // Dequeue first node to not exceed the limit
    char c0;
    dequeue2(q, &c0);
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
  if (count(q) == 0) {
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

void destroy(struct queue *q)
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
  // Don't forget to destroy the last node
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
  assert(b1);

  bool b2 = is_empty(q);
  assert(!b2);

  int n1 = count(q);
  assert(n1 == 3);

  dequeue(q);
  dequeue(q);
  dequeue(q);
  
  bool b3 = is_empty(q);
  assert(b3);

  enqueue(q, 'e');
  enqueue(q, 'f');
  enqueue(q, 'g');

  destroy(q);
  return 0;
}