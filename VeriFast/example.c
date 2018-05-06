#include "stdlib.h"

/*@
predicate cblock(struct cblock *cblock, int pos, int len, list<char> list) =
  cblock->pos |-> pos &*&
  cblock->len |-> len &*&
  cblock->arr |-> ?arr &*&
  chars(arr, len, list) &*&
  malloc_block(arr, len) &*&
  malloc_block_cblock(cblock);
@*/

struct cblock {
  int pos;
  int len;
  char *arr;
};

struct cblock *create_cblock(int len)
  //@ requires len >= 0;
  //@ ensures cblock(result, -1, len, ?list);
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
  cblock->pos = -1;
  cblock->len = len;
  cblock->arr = arr;
  //@ close cblock(cblock, -1, len, _);
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
  //@ requires cblock(cblock, ?pos, ?len, ?list);
  //@ ensures cblock(cblock, pos, len, list) &*& result == mem<char>(c, list);
{
  //@ open cblock(cblock, pos, len, list);
  bool res = array_contains(cblock->arr, cblock->len, c);
  //@ close cblock(cblock, pos, len, list);
  return res;
}

void array_append(char *arr, int len, int pos, char c)
  //@ requires chars(arr, len, ?list) &*& pos >= 0 &*& pos < len;
  //@ ensures chars(arr, len, ?list0) &*& nth<char>(pos, list0) == c;
{
  //@ open chars(arr, len, list);
  if (pos == 0) {
    *arr = c;
    //@ close chars(arr, len, cons(c, tail(list)));
  } else {
    array_append(arr + 1, len - 1, pos - 1, c);
    //@ close chars(arr, len, _);
  }
}

void cblock_append(struct cblock *cblock, char c)
  //@ requires cblock(cblock, ?pos, ?len, ?list) &*& pos >= -1;
  //@ ensures cblock(cblock, ?pos0, len, ?list0) &*& ((pos + 1) < len) ? nth<char>(pos0, list0) == c &*& pos0 == pos + 1 : list0 == list &*& pos0 == pos;

{
  //@ open cblock(cblock, pos, len, list);
  if ((cblock->pos + 1) < cblock->len) {
    cblock->pos += 1;
    array_append(cblock->arr, cblock->len, cblock->pos, c);
    assert(cblock->arr[cblock->pos] == c);
  }
  //@ close cblock(cblock, _, len, _);
}

void cblock_dispose(struct cblock *cblock)
  //@ requires cblock(cblock, _, _, _);
  //@ ensures true;
{
  //@ open cblock(cblock, _, _, _);
  free(cblock->arr);
  free(cblock);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  int len = 100;
  struct cblock *cblock = create_cblock(len);
  cblock_append(cblock, 'a');
  cblock_append(cblock, 'b');
  cblock_append(cblock, 'c');
  // ...
  bool res = cblock_contains(cblock, 'z');
  cblock_dispose(cblock);
  return 0;
}