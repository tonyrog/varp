#ifndef __SLIST_H__
#define __SLIST_H__

#include <stdlib.h>
#include <memory.h>

typedef struct _slink_t {
    struct _slink_t *next;
} slink_t;

typedef struct _slist_t {
    slink_t  head;    // head link (not in list)
    slink_t* tail;    // pointer to tail
    size_t  length;   // list length
} slist_t;

// #define LOCAL static
#define LOCAL

LOCAL void slist_init(slist_t* list)
{
    list->length    = 0;
    list->head.next = NULL;
    list->tail      = &list->head;
}

LOCAL slist_t* slist_new(void)
{
    slist_t* list = malloc(sizeof(slist_t));
    if (list != NULL)
	slist_init(list);
    return list;
}

// slist_free does not fre the list elements! only the allocated!
// list structure
LOCAL void slist_free(slist_t* list)
{
    free(list);
}

LOCAL size_t slist_length(slist_t* list)
{
    return list->length;
}

LOCAL int slist_is_empty(slist_t* list)
{
    return (list->length == 0);
}
 
LOCAL void* slist_first(slist_t* list)
{
    return list->head.next;
}
 
LOCAL void* slist_last(slist_t* list)
{
    return list->tail;
}

LOCAL int slist_is_last(slist_t* list, void* elem)
{
    return (((slink_t*)elem) == list->tail);
}

LOCAL int slist_is_first(slist_t* list, void* elem)
{
    return (((slink_t*)elem) == list->head.next);
}

// use is_eol when loop over list!
// ptr = slist_first(list);
// while(!slist_is_eol(ptr)) {
//    ...
//    ptr = slist_next(ptr)
// }
LOCAL int slist_is_eol(void* elem)
{
    return (((slink_t*)elem) == NULL);
}

LOCAL void* slist_next(void* elem)
{
    return (void*)(((slink_t*)elem)->next);
}

LOCAL void* slist_insert_first(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;
    elem->next = list->head.next;
    list->head.next = elem;
    if (list->tail == &list->head)
	list->tail = elem;
    list->length++;
    return elem;
}

LOCAL void* slist_insert_last(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;
    elem->next = NULL;
    list->tail->next = elem;
    list->tail = elem;
    list->length++;
    return elem;
}

LOCAL int slist_is_member(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;
    slink_t* link = list->head.next;

    while((link != NULL) && (link != elem))
	link = link->next;
    return (elem == link);
}

LOCAL void* slist_remove(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;
    slink_t* prev = &list->head;

    while((prev != NULL) && (prev->next != ptr))
	prev = prev->next;

    if (prev != NULL) {
	prev->next = elem->next;
	if (elem == list->tail)
	    list->tail = prev;
	list->length--;
    }
    return (void*) elem;
}

// "pop" return and remove from head of list
LOCAL void* slist_take_first(slist_t* list)
{
    slink_t* elem = list->head.next;
    list->head.next = elem->next;
    if (elem == list->tail)
	list->tail = &list->head;
    list->length--;
    return elem;
}

// merge (append) element from list from last in list to
// and clear original from list to and from must be diffrent lists
//
LOCAL void slist_merge(slist_t* from, slist_t* to)
{
    if (from->length == 0)
	return;
    else if (to->length == 0) {
	to->head.next = from->head.next;
	if ((to->length = from->length) == 0)
	    to->tail = &to->head;
	else
	    to->tail = from->tail;
    }
    else {
	to->tail->next = from->head.next;
	to->tail = from->tail;
	to->length += from->length;
    }
    slist_init(from);
}

#endif
