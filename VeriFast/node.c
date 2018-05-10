#include "node.h"

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