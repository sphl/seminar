#include "stdlib.h"

struct cblock {
  int pos;
  int len;
  char *arr;
};

/*@
predicate cblock(struct cblock *cblock, int len, list<char> list) =
  cblock->pos |-> ?pos &*&
  cblock->len |-> len &*&
  cblock->arr |-> ?arr &*&
  chars(arr, len, list) &*&
  malloc_block(arr, len) &*&
  malloc_block_cblock(cblock);
@*/

struct cblock *create_cblock(int len)
  //@ requires len >= 0;
  //@ ensures cblock(result, len, _);
{
  struct cblock *cblock = malloc(sizeof(struct cblock));
  if (cblock == 0) {
    abort();
  }
  char *arr = malloc(len);
  if (arr == 0) {
    free(cblock);
    abort();
  }
  cblock->pos = 0;
  cblock->len = len;
  cblock->arr = arr;
  //@ close cblock(cblock, len, _);
  return cblock;
}

bool array_contains(char *arr, int len, char c)
  //@ requires chars(arr, len, ?list);
  //@ ensures chars(arr, len, list) &*& result == mem<char>(c, list);
{
  //@ open chars(arr, len, list);
  bool res = false;
  if (len > 0) {
    bool cmp = (*arr == c);
    bool tmp = array_contains(arr + 1, len - 1, c);
    res = (cmp || tmp);
  }
  //@ close chars(arr, len, list);
  return res;
}

bool cblock_contains(struct cblock *cblock, char c)
  //@ requires cblock(cblock, ?len, ?list);
  //@ ensures cblock(cblock, len, list) &*& result == mem<char>(c, list);
{
  //@ open cblock(cblock, len, list);
  bool res = array_contains(cblock->arr, cblock->len, c);
  //@ close cblock(cblock, len, list);
  return res;
}

void cblock_dispose(struct cblock *cblock)
  //@ requires cblock(cblock, _, _);
  //@ ensures true;
{
  //@ open cblock(cblock, _, _);
  free(cblock->arr);
  free(cblock);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  int len = 100;
  struct cblock *cblock = create_cblock(len);
  // ...
  bool res = cblock_contains(cblock, 'x');
  cblock_dispose(cblock);
  return 0;
}