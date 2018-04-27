#include "stdlib.h"

struct account {
  int limit;
  int balance;
};

/*@
predicate account_pred(struct account *myAccount, int theLimit, int theBalance) =
  myAccount->limit |-> theLimit &*& myAccount->balance |-> theBalance &*& malloc_block_account(myAccount);
@*/

struct account *create_account(int limit)
  //@ requires limit <= 0;
  //@ ensures account_pred(result, limit, 0);
{
  struct account *myAccount = malloc(sizeof(struct account));
  if (myAccount == 0) { abort(); }
  myAccount->limit = limit;
  myAccount->balance = 0;
  //@ close account_pred(myAccount, limit, 0);
  return myAccount;
}

void account_deposit(struct account *myAccount, int amount)
  //@ requires account_pred(myAccount, ?theLimit, ?theBalance) &*& amount >= 0;
  //@ ensures account_pred(myAccount, theLimit, theBalance + amount);
{
  //@ open account_pred(myAccount, theLimit, theBalance);
  myAccount->balance += amount;
  //@ close account_pred(myAccount, theLimit, theBalance + amount);
}

int account_get_balance(struct account *myAccount)
  //@ requires account_pred(myAccount, ?theLimit, ?theBalance);
  //@ ensures account_pred(myAccount, theLimit, theBalance) &*& result == theBalance;
{
  //@ open account_pred(myAccount, theLimit, theBalance);
  int result = myAccount->balance;
  //@ close account_pred(myAccount, theLimit, theBalance);
  return result;
}

int account_withdraw(struct account *myAccount, int amount)
  //@ requires account_pred(myAccount, ?theLimit, ?theBalance) &*& amount >= 0;
  //@ ensures account_pred(myAccount, theLimit, theBalance - result) &*& result == (theBalance - amount < theLimit ? theBalance - theLimit : amount);
{
  //@ open account_pred(myAccount, theLimit, theBalance);
  int result = myAccount->balance - amount < myAccount->limit ? myAccount->balance - myAccount->limit : amount;
  myAccount->balance -= result;
  //@ close account_pred(myAccount, theLimit, theBalance - result);
  return result;
}

void account_dispose(struct account *myAccount)
  //@ requires account_pred(myAccount, _, _);
  //@ ensures true;
{
  //@ open account_pred(myAccount, _, _);
  free(myAccount);
}

int main()
  //@ requires true;
  //@ ensures true;
{
  struct account *myAccount = create_account(-100);
  account_deposit(myAccount, 200);
  int w1 = account_withdraw(myAccount, 50);
  assert(w1 == 50);
  int b1 = account_get_balance(myAccount);
  assert(b1 == 150);
  int w2 = account_withdraw(myAccount, 250);
  assert(w2 == 250);
  int b2 = account_get_balance(myAccount);
  assert(b2 == -100);
  account_dispose(myAccount);
  return 0;
}