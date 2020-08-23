#ifndef __CDLIST_H__
#define __CDLIST_H__

#include <stdlib.h>
#include <stdint.h>
#include <memory.h>
#include <float.h>

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
    struct _cdlink_t *next;
    struct _cdlink_t *prev;
    order_t order;
} cdlink_t;

typedef struct _cdlist_t {
    cdlink_t head;      // head link
    cdlink_t tail;      // tail link
    size_t  length;    // list length
} cdlist_t;

#ifndef CDLIST_ALLOC
#define CDLIST_ALLOC(n) malloc((n))
#define CDLIST_RELLOC(ptr,n) realloc((ptr),(n))
#define CDLIST_FREE(ptr) free((ptr))
#endif

#define CDLIST_LOCAL static
#define CDLIST_API __attribute__ ((unused))

CDLIST_LOCAL void cdlist_init(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL cdlist_t* cdlist_new(void) CDLIST_API;
CDLIST_LOCAL void cdlist_free(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL size_t cdlist_length(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL int cdlist_is_empty(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void* cdlist_first(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void* cdlist_last(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL int cdlist_is_last(cdlist_t* list, void* elem) CDLIST_API;
CDLIST_LOCAL int cdlist_is_first(cdlist_t* list, void* elem) CDLIST_API;
CDLIST_LOCAL int cdlist_is_eol(void* elem) CDLIST_API;
CDLIST_LOCAL int cdlist_is_bol(void* elem) CDLIST_API;
CDLIST_LOCAL void* cdlist_next(void* elem) CDLIST_API;
CDLIST_LOCAL void* cdlist_prev(void* elem) CDLIST_API;
    CDLIST_LOCAL void cdlist_renumber_from(cdlist_t* list, void* ptr, order_t order, order_t step) CDLIST_API;
CDLIST_LOCAL void cdlist_renumber(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void cdlist_set_order(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL int cdlist_is_after(void* aptr, void* bptr) CDLIST_API;
CDLIST_LOCAL int cdlist_is_before(void* aptr, void* bptr) CDLIST_API;
CDLIST_LOCAL void cdlist_insert_after(cdlist_t* list, void* aptr, void* ptr) CDLIST_API;
CDLIST_LOCAL void cdlist_insert_before(cdlist_t* list, void* aptr, void* ptr) CDLIST_API;
CDLIST_LOCAL void cdlist_insert_first(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void cdlist_insert_last(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_remove(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void* cdlist_take_first(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL void* cdlist_take_last(cdlist_t* list) CDLIST_API;
CDLIST_LOCAL cdlink_t* cdlist_restore(cdlist_t* list, void* ptr) CDLIST_API;
CDLIST_LOCAL void cdlist_merge(cdlist_t* from, cdlist_t* to) CDLIST_API;
    
    
CDLIST_LOCAL void cdlist_init(cdlist_t* list)
{
    list->length  = 0;
    list->head.prev  = NULL;
    list->head.next  = &list->tail;
    list->head.order = ORDER_0;

    list->tail.next  = NULL;
    list->tail.prev  = &list->head;
    list->tail.order = ORDER_1;
}

CDLIST_LOCAL cdlist_t* cdlist_new(void)
{
    cdlist_t* list = CDLIST_ALLOC(sizeof(cdlist_t));
    if (list != NULL)
	cdlist_init(list);
    return list;
}

// cdlist_free does not fre the list elements! only the allocated!
// list structure
CDLIST_LOCAL void cdlist_free(cdlist_t* list)
{
    CDLIST_FREE(list);
}

CDLIST_LOCAL size_t cdlist_length(cdlist_t* list)
{
    return list->length;
}

CDLIST_LOCAL int cdlist_is_empty(cdlist_t* list)
{
    return (list->length == 0);
}
 
CDLIST_LOCAL void* cdlist_first(cdlist_t* list)
{
    return list->head.next;
}
 
CDLIST_LOCAL void* cdlist_last(cdlist_t* list)
{
    return list->tail.prev;
}

CDLIST_LOCAL int cdlist_is_last(cdlist_t* list, void* elem)
{
    return (((cdlink_t*)elem)->next == &list->tail);
}

CDLIST_LOCAL int cdlist_is_first(cdlist_t* list, void* elem)
{
    return (((cdlink_t*)elem)->prev == &list->head);
}

// use is_eol when loop over list!
// ptr = cdlist_fiest(list);
// while(!cdlist_is_eol(ptr)) {
//    ...
//    ptr = cdlist_next(ptr)
// }
CDLIST_LOCAL int cdlist_is_eol(void* elem)
{
    return (((cdlink_t*)elem)->next == NULL);
}

CDLIST_LOCAL int cdlist_is_bol(void* elem)
{
    return (((cdlink_t*)elem)->prev == NULL);
}

CDLIST_LOCAL void* cdlist_next(void* elem)
{
    return (void*)(((cdlink_t*)elem)->next);
}

CDLIST_LOCAL void* cdlist_prev(void* elem)
{
    return (void*)(((cdlink_t*)elem)->prev);
}

CDLIST_LOCAL void cdlist_renumber_from(cdlist_t* list, void* ptr,
				       order_t order, order_t step)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    while(!cdlist_is_eol(elem)) {
	elem->order = order;
	order = order + step;
	elem = elem->next;
    }
    list->tail.order = ORDER_1;
}

CDLIST_LOCAL void cdlist_renumber(cdlist_t* list)
{
    cdlink_t* elem = cdlist_first(list);
    order_t step = ORDER_1/((order_t)(list->length+1));
    list->head.order = ORDER_0;
    cdlist_renumber_from(list, elem, step, step);
}

// Should normally not be necessary to call from user code
CDLIST_LOCAL void cdlist_set_order(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    order_t order = (elem->prev->order + elem->next->order) / 2;
    if ((order - elem->prev->order) <= ORDER_T_EPSILON)
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

CDLIST_LOCAL void cdlist_insert_after(cdlist_t* list, void* aptr, void* ptr)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    cdlink_t* anchor = (cdlink_t*) aptr;
    elem->prev = anchor;
    elem->next = anchor->next;
    elem->next->prev = elem;
    anchor->next = elem;
    list->length++;
    cdlist_set_order(list, elem);
}

CDLIST_LOCAL void cdlist_insert_before(cdlist_t* list, void* aptr, void* ptr)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    cdlink_t* anchor = (cdlink_t*) aptr;    
    elem->next = anchor;    
    elem->prev = anchor->prev;
    elem->prev->next = elem;
    anchor->prev = elem;
    list->length++;
    cdlist_set_order(list, elem);
}

CDLIST_LOCAL void cdlist_insert_first(cdlist_t* list, void* ptr)
{
    cdlist_insert_after(list, &list->head, ptr);
}

CDLIST_LOCAL void cdlist_insert_last(cdlist_t* list, void* ptr)
{
    cdlist_insert_before(list, &list->tail, ptr);
}

CDLIST_LOCAL void* cdlist_remove(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    elem->prev->next = elem->next;
    elem->next->prev = elem->prev;
    list->length--;
    return ptr;
}

// "pop" return and remove from head of list
CDLIST_LOCAL void* cdlist_take_first(cdlist_t* list)
{
    return cdlist_remove(list, list->head.next);
}

// "deq" return and remove from tail of list
CDLIST_LOCAL void* cdlist_take_last(cdlist_t* list)
{
    return cdlist_remove(list, list->tail.prev);
}
 
CDLIST_LOCAL cdlink_t* cdlist_restore(cdlist_t* list, void* ptr)
{
    cdlink_t* elem = (cdlink_t*) ptr;
    elem->prev->next = elem;
    elem->next->prev = elem;
    list->length++;
    return elem;
}

// merge (append) element from list from last in list to
// and clear original from list to and from must be diffrent lists
//
CDLIST_LOCAL void cdlist_merge(cdlist_t* from, cdlist_t* to)
{
    if (from->length == 0)
	return;
    else if (to->length == 0) {
	to->head = from->head;
	to->head.prev = &to->head;
	to->tail = from->tail;
	to->tail.next = &to->tail;
	to->length = from->length;
    }
    else {
	to->tail.prev->next = from->head.next;
	from->head.next->prev = to->tail.prev;
	from->tail.prev->next = &to->tail;
	to->tail.prev = from->tail.prev; 
	to->length += from->length;
	cdlist_renumber(to);
    }
    cdlist_init(from);
}

#endif
