#include "stdlib.h"

bool contains(char *arr, int len, char c)
  //@ requires chars(arr, len, ?list);
  /*@ ensures chars(arr, len, list) &*&
        (len == 0) ?
          result == false
        :
          result == (c == head(list) || result);
  @*/
{
  bool res = false;
  if (len > 0) {
    //@ open chars(arr, len, list);
    bool cmp = (*arr == c);
    bool tmp = contains(arr + 1, len - 1, c);
    res = (cmp || tmp);
    //@ close chars(arr, len, list);
  }
  return res;
}

int main()
  //@ requires true;
  //@ ensures true;
{
  int len = 100;
  char *arr = malloc(len);
  if (arr == 0) { abort(); }
  // ...
  bool res = contains(arr, len, 'x');
  free(arr);
  return 0;
}