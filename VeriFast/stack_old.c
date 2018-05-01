#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct stack {
  struct node *head;
};

/*@
predicate nodes(struct node *node, int count) =
  node == 0 ?
    count == 0
  :
    0 < count
    &*& node->next |-> ?next &*& node->value |-> ?value
    &*& malloc_block_node(node) &*& nodes(next, count - 1);

predicate stack(struct stack *stack, int count) =
  stack->head |-> ?head &*& malloc_block_stack(stack) &*& 0 <= count &*& nodes(head, count);

predicate lseg(struct node *first, struct node *last, int count) =
  first == last ?
    count == 0
  :
    count > 0 &*& first != 0 &*& first->value |-> _ &*& first->next |-> ?next
    &*& malloc_block_node(first) &*& lseg(next, last, count - 1);

lemma void nodes_to_lseg_lemma(struct node *first)
  requires nodes(first, ?count);
  ensures lseg(first, 0, count);
{
  open nodes(first, count);
  if (first != 0) {
    nodes_to_lseg_lemma(first->next);
  }
  close lseg(first, 0, count);
}

lemma void lseg_to_nodes_lemma(struct node *first)
  requires lseg(first, 0, ?count);
  ensures nodes(first, count);
{
  open lseg(first, 0, count);
  if (first != 0) {
    lseg_to_nodes_lemma(first->next);
  }
  close nodes(first, count);
}

lemma void lseg_add_lemma(struct node *first)
  requires lseg(first, ?last, ?count) &*& last != 0 &*& last->value |-> _ &*& last->next |-> ?next
    &*& malloc_block_node(last) &*& lseg(next, 0, ?count0);
  ensures lseg(first, next, count + 1) &*& lseg(next, 0, count0);
{
  open lseg(first, last, count);
  if (first == last) {
    close lseg(next, next, 0);
  } else {
    lseg_add_lemma(first->next);
  }
  open lseg(next, 0, count0);
  close lseg(next, 0, count0);
  close lseg(first, next, count + 1);
}
@*/

struct stack *create_stack()
  //@ requires true;
  //@ ensures stack(result, 0);
{
  struct stack *stack = malloc(sizeof(struct stack));
  if (stack == 0) { abort(); }
  stack->head = 0;
  //@ close nodes(0, 0);
  //@ close stack(stack, 0);
  return stack;
}

bool stack_is_empty(struct stack *stack)
  //@ requires stack(stack, ?count);
  //@ ensures stack(stack, count) &*& result == (count == 0);
{
  //@ open stack(stack, count);
  struct node *head = stack->head;
  //@ open nodes(head, count);
  bool result = head == 0;
  //@ close nodes(head, count);
  //@ close stack(stack, count);
  return result;
}

void stack_push(struct stack *stack, int value)
  //@ requires stack(stack, ?count);
  //@ ensures stack(stack, count + 1);
{
  //@ open stack(stack, count);
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->next = stack->head;
  n->value = value;
  stack->head = n;
  //@ close nodes(n, count + 1);
  //@ close stack(stack, count + 1);
}

int stack_pop(struct stack *stack)
  //@ requires stack(stack, ?count) &*& 0 < count;
  //@ ensures stack(stack, count - 1);
{
  //@ open stack(stack, count);
  struct node *head = stack->head;
  //@ open nodes(head, count);
  int result = head->value;
  stack->head = head->next;
  free(head);
  //@ close stack(stack, count - 1);
  return result;
}

int stack_get_count(struct stack *stack)
  //@ requires stack(stack, ?count);
  //@ ensures stack(stack, count) &*& result == count;
{
  //@ open stack(stack, count);
  struct node *head = stack->head;
  //@ nodes_to_lseg_lemma(head);
  struct node *n = head;
  int i = 0;
  //@ close lseg(head, head, 0);
  while (n != 0)
    //@ invariant lseg(head, n, i) &*& lseg(n, 0, count - i);
  {
    //@ open lseg(n, 0, count - i);
    n = n->next;
    i++;
    //@ lseg_add_lemma(head);
  }
  //@ open lseg(0, 0, _);
  //@ lseg_to_nodes_lemma(head);
  //@ close stack(stack, count);
  return i;
}

void stack_dispose1(struct stack *stack)
  //@ requires stack(stack, 0);
  //@ ensures true;
{
  //@ open stack(stack, 0);
  //@ open nodes(_, _);
  free(stack);
}

void nodes_dispose(struct node *node)
  //@ requires nodes(node, _);
  //@ ensures true;
{
  //@ open nodes(node, _);
  if (node != 0) {
    struct node *next = node->next;
    free(node);
    nodes_dispose(next);
  }
}

void stack_dispose2(struct stack *stack)
  //@ requires stack(stack, _);
  //@ ensures true;
{
  //@ open stack(stack, _);
  nodes_dispose(stack->head);
  free(stack);
}

void stack_dispose3(struct stack *stack)
  //@ requires stack(stack, _);
  //@ ensures true;
{
  //@ open stack(stack, _);
  struct node *node = stack->head;
  while (node != 0)
    //@ invariant nodes(node, _);
  {
    //@ open nodes(node, _);
    struct node *next = node->next;
    free(node);
    node = next;
  }
  //@ open nodes(node, _);
  free(stack);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct stack *s = create_stack();
  stack_push(s, 10);
  stack_push(s, 20);
  stack_pop(s);
  stack_pop(s);
  stack_dispose2(s);
  return 0;
}