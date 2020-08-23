#ifndef __DLLIST_H__
#define __DLLIST_H__

// Like dlist but without fancy stuff,
// this allow the data structure to be moved!
// The dlist have elements have pointers into the head.

#include <stdlib.h>
#include <memory.h>

typedef struct _dlink_t {
    struct _dlink_t *next;
    struct _dlink_t *prev;
} dlink_t;

typedef struct _dlist_t {
    dlink_t* first;
    dlink_t* last;
    size_t  length;    // list length
} dlist_t;

#ifndef DLIST_ALLOC
#define DLIST_ALLOC(n) malloc((n))
#define DLIST_RELLOC(ptr,n) realloc((ptr),(n))
#define DLIST_FREE(ptr) free((ptr))
#endif

#define DLIST_LOCAL static

DLIST_LOCAL void dlist_init(dlist_t* list)
{
    list->length  = 0;
    list->first = NULL;
    list->last  = NULL;
}

DLIST_LOCAL dlist_t* dlist_new(void)
{
    dlist_t* list = DLIST_ALLOC(sizeof(dlist_t));
    if (list != NULL)
	dlist_init(list);
    return list;
}

// dlist_free does not fre the list elements! only the allocated!
// list structure
DLIST_LOCAL void dlist_free(dlist_t* list)
{
    DLIST_FREE(list);
}

DLIST_LOCAL size_t dlist_length(dlist_t* list)
{
    return list->length;
}

DLIST_LOCAL int dlist_is_empty(dlist_t* list)
{
    return (list->length == 0);
}
 
DLIST_LOCAL void* dlist_first(dlist_t* list)
{
    return list->first;
}
 
DLIST_LOCAL void* dlist_last(dlist_t* list)
{
    return list->last;
}

DLIST_LOCAL int dlist_is_last(dlist_t* list, void* elem)
{
    return (list->last == (dlink_t*)elem);
}

DLIST_LOCAL int dlist_is_first(dlist_t* list, void* elem)
{
    return (list->first == (dlink_t*)elem);
}

// use is_eol when loop over list!
// ptr = dlist_fiest(list);
// while(!dlist_is_eol(ptr)) {
//    ...
//    ptr = dlist_next(ptr)
// }
DLIST_LOCAL int dlist_is_eol(void* elem)
{
    return ((dlink_t*)elem == NULL);
}

DLIST_LOCAL int dlist_is_bol(void* elem)
{
    return ((dlink_t*)elem == NULL); // FIXME?
}

DLIST_LOCAL void* dlist_next(void* elem)
{
    return (void*)(((dlink_t*)elem)->next);
}

DLIST_LOCAL void* dlist_prev(void* elem)
{
    return (void*)(((dlink_t*)elem)->prev);
}

DLIST_LOCAL void* dlist_insert_after(dlist_t* list, void* aptr, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    dlink_t* anchor = (dlink_t*) aptr;
    elem->prev = anchor;
    elem->next = anchor->next;
    elem->next->prev = elem;
    anchor->next = elem;
    if (list->last == anchor)
	list->last = elem;
    list->length++;
    return elem;
}

DLIST_LOCAL void* dlist_insert_before(dlist_t* list, void* aptr, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    dlink_t* anchor = (dlink_t*) aptr;    
    elem->next = anchor;    
    elem->prev = anchor->prev;
    elem->prev->next = elem;
    anchor->prev = elem;
    if (list->first == anchor)
	list->first = elem;
    list->length++;
    return elem;
}

DLIST_LOCAL void* dlist_insert_first(dlist_t* list, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;

    if ((elem->next = list->first) == NULL)
	list->last  = elem;
    else
	elem->next->prev = elem;
    elem->prev = NULL;
    list->first = elem;
    list->length++;
    return elem;    
}

DLIST_LOCAL void* dlist_insert_last(dlist_t* list, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;

    if ((elem->prev = list->last) == NULL)
	list->first = elem;
    else
	elem->prev->next = elem;
    elem->next = NULL;
    list->last = elem;
    list->length++;
    return elem;
}

DLIST_LOCAL void* dlist_remove(dlist_t* list, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    if (elem->prev)
	elem->prev->next = elem->next;
    else
	list->first = elem->next;
    if (elem->next)
	elem->next->prev = elem->prev;
    else
	list->last = elem->prev;
    list->length--;
    return (void*) elem;
}

// "pop" return and remove from head of list
DLIST_LOCAL void* dlist_take_first(dlist_t* list)
{
    return dlist_remove(list, list->first);
}

// "deq" return and remove from tail of list
DLIST_LOCAL void* dlist_take_last(dlist_t* list)
{
    return dlist_remove(list, list->last);
}
 
DLIST_LOCAL dlink_t* dlist_restore(dlist_t* list, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    elem->prev->next = elem;
    elem->next->prev = elem;
    list->length++;
    return elem;
}

// merge (append) element from list from last in list to
// and clear original from list to and from must be diffrent lists
//
DLIST_LOCAL void dlist_merge(dlist_t* from, dlist_t* to)
{
    if (from->length == 0)
	return;
    else if (to->length == 0) {
	to->first = from->first;
	to->last = from->last;
	to->length = from->length;
    }
    else {
	to->last->next = from->first;
	from->first->prev = to->last;
	to->last = from->last;
	to->length += from->length;
    }
    dlist_init(from);
}

#endif
