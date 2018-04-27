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