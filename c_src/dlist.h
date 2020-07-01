#ifndef __DLIST_H__
#define __DLIST_H__

#include <stdlib.h>
#include <memory.h>

typedef struct _dlink_t {
    struct _dlink_t *next;
    struct _dlink_t *prev;
} dlink_t;

typedef struct _dlist_t {
    dlink_t head;      // head link
    dlink_t tail;      // tail link
    size_t  length;    // list length
} dlist_t;

// #define LOCAL static
#define LOCAL

LOCAL void dlist_init(dlist_t* list)
{
    list->length  = 0;
    list->head.prev  = NULL;
    list->head.next  = &list->tail;

    list->tail.next  = NULL;
    list->tail.prev  = &list->head;
}

LOCAL dlist_t* dlist_new(void)
{
    dlist_t* list = malloc(sizeof(dlist_t));
    if (list != NULL)
	dlist_init(list);
    return list;
}

// dlist_free does not fre the list elements! only the allocated!
// list structure
LOCAL void dlist_free(dlist_t* list)
{
    free(list);
}

LOCAL size_t dlist_length(dlist_t* list)
{
    return list->length;
}

LOCAL int dlist_is_empty(dlist_t* list)
{
    return (list->length == 0);
}
 
LOCAL void* dlist_first(dlist_t* list)
{
    return list->head.next;
}
 
LOCAL void* dlist_last(dlist_t* list)
{
    return list->tail.prev;
}

LOCAL int dlist_is_last(dlist_t* list, void* elem)
{
    return (((dlink_t*)elem)->next == &list->tail);
}

LOCAL int dlist_is_first(dlist_t* list, void* elem)
{
    return (((dlink_t*)elem)->prev == &list->head);
}

// use is_eol when loop over list!
// ptr = dlist_first(list);
// while(!dlist_is_eol(ptr)) {
//    ...
//    ptr = dlist_next(ptr)
// }
LOCAL int dlist_is_eol(void* elem)
{
    return (((dlink_t*)elem)->next == NULL);
}

LOCAL int dlist_is_bol(void* elem)
{
    return (((dlink_t*)elem)->prev == NULL);
}

LOCAL void* dlist_next(void* elem)
{
    return (void*)(((dlink_t*)elem)->next);
}

LOCAL void* dlist_prev(void* elem)
{
    return (void*)(((dlink_t*)elem)->prev);
}

LOCAL void* dlist_insert_after(dlist_t* list, void* aptr, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    dlink_t* anchor = (dlink_t*) aptr;
    elem->prev = anchor;
    elem->next = anchor->next;
    elem->next->prev = elem;
    anchor->next = elem;
    list->length++;
    return elem;
}

LOCAL void* dlist_insert_before(dlist_t* list, void* aptr, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    dlink_t* anchor = (dlink_t*) aptr;    
    elem->next = anchor;    
    elem->prev = anchor->prev;
    elem->prev->next = elem;
    anchor->prev = elem;
    list->length++;
    return elem;    
}

LOCAL void* dlist_insert_first(dlist_t* list, void* ptr)
{
    return dlist_insert_after(list, &list->head, ptr);
}

LOCAL void* dlist_insert_last(dlist_t* list, void* ptr)
{
    return dlist_insert_before(list, &list->tail, ptr);
}

LOCAL void* dlist_remove(dlist_t* list, void* ptr)
{
    dlink_t* elem = (dlink_t*) ptr;
    elem->prev->next = elem->next;
    elem->next->prev = elem->prev;
    list->length--;
    return (void*) elem;
}

// "pop" return and remove from head of list
LOCAL void* dlist_take_first(dlist_t* list)
{
    return dlist_remove(list, list->head.next);
}

// "deq" return and remove from tail of list
LOCAL void* dlist_take_last(dlist_t* list)
{
    return dlist_remove(list, list->tail.prev);
}
 
LOCAL dlink_t* dlist_restore(dlist_t* list, void* ptr)
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
LOCAL void dlist_merge(dlist_t* from, dlist_t* to)
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
    }
    dlist_init(from);
}

#endif
