#include "stdlib.h"

struct cblock {
  int pos;
  int len;
  char *arr;
};

/*@
predicate cblock(struct cblock *cb, int pos, int len, list<char> list) =
  cb->pos |-> pos &*&
  cb->len |-> len &*&
  cb->arr |-> ?arr &*&
  chars(arr, len, list) &*&
  malloc_block(arr, len) &*&
  malloc_block_cblock(cb);
@*/

struct cblock *create_cblock(int len)
  //@ requires len >= 0;
  //@ ensures cblock(result, -1, len, ?list) &*& length<char>(list) == len;
{
  struct cblock *cb = malloc(sizeof(struct cblock));
  if (cb == 0) {
    abort();
  }
  char *arr = malloc(len);
  if (arr == 0) {
    free(cb);
    abort();
  }
  cb->pos = -1;
  cb->len = len;
  cb->arr = arr;
  //@ close cblock(cb, -1, len, _);
  return cb;
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

bool cblock_contains(struct cblock *cb, char c)
  //@ requires cblock(cb, ?pos, ?len, ?list);
  //@ ensures cblock(cb, pos, len, list) &*& result == mem<char>(c, list);
{
  //@ open cblock(cb, pos, len, list);
  bool res = array_contains(cb->arr, cb->len, c);
  //@ close cblock(cb, pos, len, list);
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

void cblock_append(struct cblock *cb, char c)
  //@ requires cblock(cb, ?pos, ?len, ?list) &*& pos >= -1;
  /*@ ensures cblock(cb, ?pos0, len, ?list0) &*&
        ((pos + 1) < len) ?
          pos0 == pos + 1 &*& nth<char>(pos0, list0) == c
        :
          pos0 == pos &*& list0 == list;
  @*/
{
  //@ open cblock(cb, pos, len, list);
  if ((cb->pos + 1) < cb->len) {
    cb->pos += 1;
    array_append(cb->arr, cb->len, cb->pos, c);
    assert(cb->arr[cb->pos] == c);
  }
  //@ close cblock(cb, _, len, _);
}

void cblock_dispose(struct cblock *cb)
  //@ requires cblock(cb, _, _, _);
  //@ ensures true;
{
  //@ open cblock(cb, _, _, _);
  free(cb->arr);
  free(cb);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  int len = 100;
  struct cblock *cb = create_cblock(len);
  cblock_append(cb, 'a');
  cblock_append(cb, 'b');
  cblock_append(cb, 'c');
  // ...
  bool res = cblock_contains(cb, 'a');
  cblock_dispose(cb);
  return 0;
}