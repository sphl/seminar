#include "stdlib.h"

struct node {
  struct node *next;
  int value;
};

struct stack {
  struct node *head;
};

/*@

inductive ints = ints_nil | ints_cons(int, ints);

fixpoint int ints_head(ints values) {
  switch (values) {
    case ints_nil: return 0;
    case ints_cons(value, values0): return value;
  }
}

fixpoint ints ints_tail(ints values) {
  switch (values) {
    case ints_nil: return ints_nil;
    case ints_cons(value, values0): return values0;
  }
}

fixpoint int ints_sum(ints values) {
  switch (values) {
    case ints_nil: return 0;
    case ints_cons(value, values0): return value + ints_sum(values0);
  }
}

predicate nodes(struct node *node, ints values) =
  node == 0 ?
    values == ints_nil
  :
    node->next |-> ?next &*& node->value |-> ?value
    &*& malloc_block_node(node) &*& nodes(next, ?values0)
    &*& values == ints_cons(value, values0);

predicate stack(struct stack *stack, ints values) =
  stack->head |-> ?head &*& malloc_block_stack(stack) &*& nodes(head, values);

@*/

struct stack *create_stack()
  //@ requires true;
  //@ ensures stack(result, ints_nil);
{
  struct stack *stack = malloc(sizeof(struct stack));
  if (stack == 0) { abort(); }
  stack->head = 0;
  //@ close nodes(0, ints_nil);
  //@ close stack(stack, ints_nil);
  return stack;
}

bool stack_is_empty(struct stack *stack)
  //@ requires stack(stack, ?values);
  //@ ensures stack(stack, values) &*& result == (values == ints_nil);
{
  //@ open stack(stack, values);
  struct node *head = stack->head;
  //@ open nodes(head, values);
  bool result = head == 0;
  //@ close nodes(head, values);
  //@ close stack(stack, values);
  return result;
}

void stack_push(struct stack *stack, int value)
  //@ requires stack(stack, ?values);
  //@ ensures stack(stack, ints_cons(value, values));
{
  //@ open stack(stack, values);
  struct node *n = malloc(sizeof(struct node));
  if (n == 0) { abort(); }
  n->next = stack->head;
  n->value = value;
  stack->head = n;
  //@ close nodes(n, ints_cons(value, values));
  //@ close stack(stack, ints_cons(value, values));
}

int stack_pop(struct stack *stack)
  //@ requires stack(stack, ?values) &*& values == ints_cons(?value0, ?values0);
  //@ ensures stack(stack, ints_tail(values)) &*& result == ints_head(values);
{
  //@ open stack(stack, values);
  struct node *head = stack->head;
  //@ open nodes(head, values);
  int result = head->value;
  stack->head = head->next;
  free(head);
  //@ close stack(stack, values0);
  return result;
}

int nodes_get_sum(struct node *node)
  //@ requires nodes(node, ?values);
  //@ ensures nodes(node, values) &*& result == ints_sum(values);
{
  //@ open nodes(node, values);
  int result = 0;
  if (node != 0) {
    int tailSum = nodes_get_sum(node->next);
    result = node->value + tailSum;
  }
  //@ close nodes(node, values);
  return result;
}

int stack_get_sum(struct stack *stack)
  //@ requires stack(stack, ?values);
  //@ ensures stack(stack, values) &*& result == ints_sum(values);
{
  //@ open stack(stack, values);
  int result = nodes_get_sum(stack->head);
  //@ close stack(stack, values);
  return result;
}

void stack_dispose1(struct stack *stack)
  //@ requires stack(stack, ints_nil);
  //@ ensures true;
{
  //@ open stack(stack, ints_nil);
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
  int result1 = stack_pop(s);
  assert(result1 == 20);
  int result2 = stack_pop(s);
  assert(result2 == 10);
  stack_dispose3(s);
  return 0;
}