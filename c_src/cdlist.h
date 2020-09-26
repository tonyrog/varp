#ifndef __CDLIST_H__
#define __CDLIST_H__

#include <stdlib.h>
#include <stdint.h>
#include <memory.h>
#include <float.h>

#include "dlist.h"

#if defined(UINT32_ORDER)
typedef uint32_t order_t;
#define ORDER_T_EPSILON 2
#define ORDER_0 0
#define ORDER_1 (0x7fffffff)
#elif defined(UINT64_ORDER)
typedef uint64_t order_t;
#define ORDER_T_EPSILON 2
#define ORDER_0 0
#define ORDER_1 (0x7fffffffffffffff)
#elif defined(DOUBLE_ORDER)
typedef double order_t;
#define ORDER_T_EPSILON      (4*DBL_EPSILON)
#define ORDER_0 0.0
#define ORDER_1 1.0
#else
typedef float order_t;
#define ORDER_T_EPSILON      (4*FLT_EPSILON)
#define ORDER_0 0.0f
#define ORDER_1 1.0f
#endif

// comparable doubly linked list element
// order fields is kept in order so that elements
// may be compared.

typedef struct _cdlink_t {
    dlink_t link;
    order_t order;
} cdlink_t;

typedef dlist_t cdlist_t;
typedef dlist_iter_t cdlist_iter_t;

#define CDLIST_LOCAL static
#if defined(__WIN32__) || defined(_WIN32)
#define CDLIST_API
#else
#define CDLIST_API __attribute__ ((unused))
#endif

CDLIST_LOCAL void cdlist_init(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void cdlist_clear(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL size_t cdlist_length(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL int cdlist_is_empty(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void* cdlist_first(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void* cdlist_last(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL int cdlist_is_last(cdlist_t* list, void* elem) CDLIST_API;
CDLIST_LOCAL int cdlist_is_first(cdlist_t* list, void* elem) CDLIST_API;
CDLIST_LOCAL void* cdlist_next(void* elem) CDLIST_API;
CDLIST_LOCAL void* cdlist_prev(void* elem) CDLIST_API;
CDLIST_LOCAL void cdlist_renumber_from(cdlist_t* list, void* ptr, order_t order, order_t step) CDLIST_API;
CDLIST_LOCAL void cdlist_renumber(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void cdlist_set_order(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL int cdlist_is_after(void* aptr, void* bptr) CDLIST_API;
CDLIST_LOCAL int cdlist_is_before(void* aptr, void* bptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_insert_after(cdlist_t* list, void* aptr, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_insert_before(cdlist_t* list, void* aptr, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_insert_first(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_insert_last(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_remove(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_take_first(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void* cdlist_take_last(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void cdlist_merge(cdlist_t* from, cdlist_t* to) CDLIST_API;

CDLIST_LOCAL void cdlist_iter_init(cdlist_iter_t* iter, cdlist_t* list) DLIST_API;
CDLIST_LOCAL void* cdlist_iter_current(cdlist_iter_t* iter) DLIST_API;
CDLIST_LOCAL int cdlist_iter_end(cdlist_iter_t* iter) DLIST_API;
CDLIST_LOCAL void* cdlist_iter_next(cdlist_iter_t* iter) DLIST_API;
CDLIST_LOCAL void cdlist_iter_remove(cdlist_iter_t* iter) DLIST_API;

    
CDLIST_LOCAL void cdlist_init(cdlist_t* list)
{
    dlist_init(list);
}

CDLIST_LOCAL void cdlist_clear(cdlist_t* list)
{
    dlist_init(list);
}

CDLIST_LOCAL size_t cdlist_length(cdlist_t* list)
{
    return dlist_length(list);
}

CDLIST_LOCAL int cdlist_is_empty(cdlist_t* list)
{
    return dlist_is_empty(list);
}
 
CDLIST_LOCAL void* cdlist_first(cdlist_t* list)
{
    return dlist_first(list);    
}
 
CDLIST_LOCAL void* cdlist_last(cdlist_t* list)
{
    return dlist_last(list);        
}

CDLIST_LOCAL int cdlist_is_last(cdlist_t* list, void* elem)
{
    return dlist_is_last(list, elem);
}

CDLIST_LOCAL int cdlist_is_first(cdlist_t* list, void* elem)
{
    return dlist_is_first(list, elem);
}

CDLIST_LOCAL void* cdlist_next(void* elem)
{
    return dlist_next(elem);
}

CDLIST_LOCAL void* cdlist_prev(void* elem)
{
    return dlist_prev(elem);    
}

CDLIST_LOCAL void cdlist_renumber_from(cdlist_t* list, void* ptr,
				       order_t order, order_t step)
{
    (void) list;
    cdlink_t* elem = (cdlink_t*) ptr;
    while(elem != NULL) {
	elem->order = order;
	order = order + step;
	elem = cdlist_next(elem);
    }
}

CDLIST_LOCAL void cdlist_renumber(cdlist_t* list)
{
    cdlink_t* elem = cdlist_first(list);
    order_t step = ORDER_1/((order_t)(list->length+1));
    cdlist_renumber_from(list, elem, step, step);
}

CDLIST_LOCAL order_t cdlist_order(void* elem, order_t def)
{
    return (elem == NULL) ? def : ((cdlink_t*)elem)->order;
}

// Should normally not be necessary to call from user code
CDLIST_LOCAL void cdlist_set_order(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    order_t p_order = cdlist_order(elem->link.prev, ORDER_0);
    order_t n_order = cdlist_order(elem->link.next, ORDER_1);
    order_t order = (p_order + n_order) / 2;
    if ((order - p_order) <= ORDER_T_EPSILON)
	cdlist_renumber(list);
    else
	elem->order = order;
}

// check if element A is (somewhere) after element B in list
CDLIST_LOCAL int cdlist_is_after(void* aptr, void* bptr)
{
    return ((cdlink_t*)aptr)->order > ((cdlink_t*)bptr)->order;
}

// check if element A is (somewhere) before element B in list
CDLIST_LOCAL int cdlist_is_before(void* aptr, void* bptr)
{
    return ((cdlink_t*)aptr)->order < ((cdlink_t*)bptr)->order;
}

// insert first element
// update order as previous first element order - 1
// of 0 if no previous first element
CDLIST_LOCAL void* cdlist_insert_first(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = dlist_insert_first(list, ptr);
    cdlink_t* next = (cdlink_t*) elem->link.next;
    if (next == NULL)
	elem->order = 0.0;
    else
	elem->order = next->order - 1.0;
    return elem;
}

CDLIST_LOCAL void* cdlist_insert_last(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = dlist_insert_last(list, ptr);
    cdlink_t* prev = (cdlink_t*) elem->link.prev;
    if (prev == NULL)
	elem->order = 0.0;
    else
	elem->order = prev->order + 1.0;
    return elem;    
}

CDLIST_LOCAL void* cdlist_insert_after(cdlist_t* list, void* aptr, void* ptr)
{
    if (dlist_is_last(list, aptr))
	return cdlist_insert_last(list, ptr);
    else {
	cdlink_t* elem = dlist_insert_after(list, aptr, ptr);
	cdlist_set_order(list, elem);
	return elem;
    }
}

CDLIST_LOCAL void* cdlist_insert_before(cdlist_t* list, void* aptr, void* ptr)
{
    if (dlist_is_first(list, aptr))
	return cdlist_insert_first(list, ptr);
    else {
	cdlink_t* elem = dlist_insert_before(list, aptr, ptr);
	cdlist_set_order(list, elem);
	return elem;
    }
}


CDLIST_LOCAL void* cdlist_remove(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = dlist_remove(list, ptr);
    return elem;
}

// "pop" return and remove from head of list
CDLIST_LOCAL void* cdlist_take_first(cdlist_t* list)
{
    return dlist_take_first(list);
}

// "deq" return and remove from tail of list
CDLIST_LOCAL void* cdlist_take_last(cdlist_t* list)
{
    return dlist_take_last(list);
}
 
// merge (append) element from list from last in list to
// and clear original from list to and from must be diffrent lists
//
CDLIST_LOCAL void cdlist_merge(cdlist_t* from, cdlist_t* to)
{
    dlist_merge(from, to);
    cdlist_renumber(to);
    cdlist_init(from);
}


CDLIST_LOCAL void cdlist_iter_init(cdlist_iter_t* iter, cdlist_t* list)
{
    dlist_iter_init(iter, list);
}

CDLIST_LOCAL void* cdlist_iter_current(cdlist_iter_t* iter)
{
    return dlist_iter_current(iter);
}

CDLIST_LOCAL int cdlist_iter_end(cdlist_iter_t* iter)
{
    return dlist_iter_end(iter);
}

CDLIST_LOCAL void* cdlist_iter_next(cdlist_iter_t* iter)
{
    return dlist_iter_next(iter);
}

CDLIST_LOCAL void cdlist_iter_remove(cdlist_iter_t* iter)
{
    dlist_iter_remove(iter);
}


#endif
