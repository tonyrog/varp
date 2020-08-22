#ifndef __DLLIST_H__
#define __DLLIST_H__

// Like dlist but without fancy stuff,
// this allow the data structure to be moved!
// The dlist have elements have pointers into the head.

#include <stdlib.h>
#include <memory.h>

typedef struct _dllink_t {
    struct _dllink_t *next;
    struct _dllink_t *prev;
} dllink_t;

typedef struct _dllist_t {
    dllink_t* first;
    dllink_t* last;
    size_t  length;    // list length
} dllist_t;

// #define LOCAL static
#define LOCAL

LOCAL void dllist_init(dllist_t* list)
{
    list->length  = 0;
    list->first = NULL;
    list->last  = NULL;
}

LOCAL dllist_t* dllist_new(void)
{
    dllist_t* list = malloc(sizeof(dllist_t));
    if (list != NULL)
	dllist_init(list);
    return list;
}

// dllist_free does not fre the list elements! only the allocated!
// list structure
LOCAL void dllist_free(dllist_t* list)
{
    free(list);
}

LOCAL size_t dllist_length(dllist_t* list)
{
    return list->length;
}

LOCAL int dllist_is_empty(dllist_t* list)
{
    return (list->length == 0);
}
 
LOCAL void* dllist_first(dllist_t* list)
{
    return list->first;
}
 
LOCAL void* dllist_last(dllist_t* list)
{
    return list->last;
}

LOCAL int dllist_is_last(dllist_t* list, void* elem)
{
    return (list->last == (dllink_t*)elem);
}

LOCAL int dllist_is_first(dllist_t* list, void* elem)
{
    return (list->first == (dllink_t*)elem);
}

// use is_eol when loop over list!
// ptr = dllist_fiest(list);
// while(!dllist_is_eol(ptr)) {
//    ...
//    ptr = dllist_next(ptr)
// }
LOCAL int dllist_is_eol(void* elem)
{
    return ((dllink_t*)elem == NULL);
}

LOCAL int dllist_is_bol(void* elem)
{
    return ((dllink_t*)elem == NULL); // FIXME?
}

LOCAL void* dllist_next(void* elem)
{
    return (void*)(((dllink_t*)elem)->next);
}

LOCAL void* dllist_prev(void* elem)
{
    return (void*)(((dllink_t*)elem)->prev);
}

LOCAL void* dllist_insert_after(dllist_t* list, void* aptr, void* ptr)
{
    dllink_t* elem = (dllink_t*) ptr;
    dllink_t* anchor = (dllink_t*) aptr;
    elem->prev = anchor;
    elem->next = anchor->next;
    elem->next->prev = elem;
    anchor->next = elem;
    if (list->last == anchor)
	list->last = elem;
    list->length++;
    return elem;
}

LOCAL void* dllist_insert_before(dllist_t* list, void* aptr, void* ptr)
{
    dllink_t* elem = (dllink_t*) ptr;
    dllink_t* anchor = (dllink_t*) aptr;    
    elem->next = anchor;    
    elem->prev = anchor->prev;
    elem->prev->next = elem;
    anchor->prev = elem;
    if (list->first == anchor)
	list->first = elem;
    list->length++;
    return elem;
}

LOCAL void* dllist_insert_first(dllist_t* list, void* ptr)
{
    dllink_t* elem = (dllink_t*) ptr;

    if ((elem->next = list->first) == NULL)
	list->last  = elem;
    else
	elem->next->prev = elem;
    elem->prev = NULL;
    list->first = elem;
    list->length++;
    return elem;    
}

LOCAL void* dllist_insert_last(dllist_t* list, void* ptr)
{
    dllink_t* elem = (dllink_t*) ptr;

    if ((elem->prev = list->last) == NULL)
	list->first = elem;
    else
	elem->prev->next = elem;
    elem->next = NULL;
    list->last = elem;
    list->length++;
    return elem;
}

LOCAL void* dllist_remove(dllist_t* list, void* ptr)
{
    dllink_t* elem = (dllink_t*) ptr;
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
LOCAL void* dllist_take_first(dllist_t* list)
{
    return dllist_remove(list, list->first);
}

// "deq" return and remove from tail of list
LOCAL void* dllist_take_last(dllist_t* list)
{
    return dllist_remove(list, list->last);
}
 
LOCAL dllink_t* dllist_restore(dllist_t* list, void* ptr)
{
    dllink_t* elem = (dllink_t*) ptr;
    elem->prev->next = elem;
    elem->next->prev = elem;
    list->length++;
    return elem;
}

// merge (append) element from list from last in list to
// and clear original from list to and from must be diffrent lists
//
LOCAL void dllist_merge(dllist_t* from, dllist_t* to)
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
    dllist_init(from);
}

#endif
