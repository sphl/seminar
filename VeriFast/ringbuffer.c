#include "stdlib.h"

struct node {
    struct node *next;
    char value;
};

/*@
predicate lseg(struct node *first, struct node *last, list<char> values) =
    first == last ?
        values == nil
    :
        first->next |-> ?next &*& first->value |-> ?value &*&
        malloc_block_node(first) &*&
        lseg(next, last, ?values0) &*&
        values == cons(value, values0);

lemma void lseg_add(struct node *first)
    requires lseg(first, ?last, ?values) &*&
        last->next |-> ?next &*& last->value |-> ?value &*&
        malloc_block_node(last) &*&
        next->next |-> ?nextNext;
    ensures lseg(first, next, append(values, cons(value, nil)))
        &*& next->next |-> nextNext;
{
    open lseg(first, last, values);
    if (first == last) {
        close lseg(next, next, nil);
    } else {
        lseg_add(first->next);
    }
    close lseg(first, next, _);
}
@*/

struct queue {
    struct node *first;
    struct node *last;
};

/*@
predicate queue(struct queue *q, list<char> values) =
    q->first |-> ?first &*&
    q->last |-> ?last &*&
    malloc_block_queue(q) &*&
    lseg(first, last, values) &*&
    last->next |-> _ &*&
    last->value |-> _ &*&
    malloc_block_node(last);
@*/

struct ringbuffer {
    int count;
    int capacity;
    struct queue *fifo;
};

/*@
predicate ringbuffer(struct ringbuffer *rb, int count, int capacity, list<char> values) =
    rb->count |-> count &*&
    rb->capacity |-> capacity &*&
    rb->fifo |-> ?fifo &*&
    queue(fifo, values) &*&
    malloc_block_ringbuffer(rb);
@*/

struct ringbuffer *create(int capacity)
    //@ requires capacity > 0;
    //@ ensures ringbuffer(result, 0, capacity, nil);
{
    struct ringbuffer *rb = malloc(sizeof(struct ringbuffer));
    if (rb == 0) abort();
    struct queue *q = malloc(sizeof(struct queue));
    if (q == 0) abort();
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    q->first = n;
    q->last = n;
    rb->count = 0;
    rb->capacity = capacity;
    rb->fifo = q;
    //@ close lseg(n, n, nil);
    //@ close queue(q, nil);
    //@ close ringbuffer(rb, 0, capacity, nil);
    return rb;
}

void enqueue(struct ringbuffer *rb, char c)
    //@ requires ringbuffer(rb, ?count, ?capacity, ?vs) &*& capacity > 0;
    //@ ensures ringbuffer(rb, ?count0, capacity, ?vs0) &*& vs0 == append(vs, cons(c, nil));
{
    //@ open ringbuffer(rb, count, _, vs);
    if (rb->count == rb->capacity) {
        //@ close ringbuffer(rb, count, _, vs);
        dequeue(rb);
        //@ open ringbuffer(rb, count, _, vs);
    }
    //@ open queue(rb->fifo, vs);
    struct node *n = malloc(sizeof(struct node));
    if (n == 0) abort();
    rb->fifo->last->next = n;
    rb->fifo->last->value = c;
    rb->fifo->last = n;
    rb->count += 1;
    //@ lseg_add(rb->fifo->first);
    //@ close queue(rb->fifo, _);
    //@ close ringbuffer(rb, _, _, _);
}

char dequeue(struct ringbuffer *rb)
    //@ requires ringbuffer(rb, ?count, _, ?vs) &*& vs != nil;
    //@ ensures ringbuffer(rb, ?count0, _, ?vs0) &*& vs == cons(result, vs0);
{
    //@ open ringbuffer(rb, count, _, vs);
    //@ open queue(rb->fifo, _);
    struct node *n = rb->fifo->first;
    //@ open lseg(n, _, _);
    char result = n->value;
    rb->fifo->first = n->next;
    free(n);
    rb->count -= 1;
    //@ close queue(rb->fifo, _);
    //@ close ringbuffer(rb, _, _, _);
    return result;
}

/*
void dispose(struct queue *q)
    //@ requires queue(q, nil);
    //@ ensures true;
{
    //@ open queue(q, nil);
    //@ open lseg(_, _, _);
    free(q->first);
    free(q);
}
*/

int main()
    //@ requires true;
    //@ ensures true;
{
    struct queue *q = create();
    enqueue(q, 10);
    enqueue(q, 20);
    int x1 = dequeue(q);
    assert(x1 == 10);
    int x2 = dequeue(q);
    assert(x2 == 20);
    //dispose(q);
    return 0;
}
