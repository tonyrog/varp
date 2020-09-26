#ifndef __SLIST_H__
#define __SLIST_H__

#include <stdlib.h>
#include <memory.h>


typedef struct _slink_t {
    struct _slink_t *next;
} slink_t;

typedef struct _slist_t {
    slink_t* first;
    slink_t* last;
    size_t  length;
} slist_t;

typedef struct {
    slist_t* list;    // current list
    slink_t* prev;    // previous pos
    slink_t* cur;     // current pos
} slist_iter_t;
    
#ifndef SLIST_ALLOC
#define SLIST_ALLOC(n) malloc((n))
#define SLIST_RELLOC(ptr,n) realloc((ptr),(n))
#define SLIST_FREE(ptr) free((ptr))
#endif

#define SLIST_LOCAL static
#if defined(__WIN32__) || defined(_WIN32)
#define SLIST_API
#else
#define SLIST_API __attribute__ ((unused))
#endif

SLIST_LOCAL void slist_init(slist_t* list) SLIST_API;
SLIST_LOCAL slist_t* slist_new(void) SLIST_API;
SLIST_LOCAL void slist_free(slist_t* list) SLIST_API;
SLIST_LOCAL size_t slist_length(slist_t* list) SLIST_API;
SLIST_LOCAL int slist_is_empty(slist_t* list) SLIST_API;
SLIST_LOCAL void* slist_first(slist_t* list) SLIST_API;
SLIST_LOCAL void* slist_last(slist_t* list) SLIST_API;
SLIST_LOCAL int slist_is_last(slist_t* list, void* elem) SLIST_API;
SLIST_LOCAL int slist_is_first(slist_t* list, void* elem) SLIST_API;
SLIST_LOCAL void* slist_next(void* elem) SLIST_API;
SLIST_LOCAL void* slist_insert_first(slist_t* list, void* ptr) SLIST_API;
SLIST_LOCAL void* slist_insert_last(slist_t* list, void* ptr) SLIST_API;
SLIST_LOCAL int slist_is_member(slist_t* list, void* ptr) SLIST_API;
SLIST_LOCAL void* slist_remove(slist_t* list, void* ptr) SLIST_API;
SLIST_LOCAL void* slist_take_first(slist_t* list) SLIST_API;
SLIST_LOCAL void slist_merge(slist_t* from, slist_t* to) SLIST_API;
    
SLIST_LOCAL void slist_iter_init(slist_iter_t* iter, slist_t* list) SLIST_API;
SLIST_LOCAL void* slist_iter_current(slist_iter_t* iter) SLIST_API;
SLIST_LOCAL int slist_iter_eol(slist_iter_t* iter) SLIST_API;
SLIST_LOCAL void* slist_iter_next(slist_iter_t* iter) SLIST_API;
SLIST_LOCAL int slist_iter_eol(slist_iter_t* iter) SLIST_API;
SLIST_LOCAL void* slist_iter_next(slist_iter_t* iter) SLIST_API;
SLIST_LOCAL void slist_iter_remove(slist_iter_t* iter) SLIST_API;


SLIST_LOCAL void slist_init(slist_t* list)
{
    list->length = 0;
    list->first  = NULL;
    list->last   = NULL;
}

SLIST_LOCAL slist_t* slist_new(void)
{
    slist_t* list = SLIST_ALLOC(sizeof(slist_t));    
    if (list != NULL)
	slist_init(list);
    return list;
}

// slist_free does not fre the list elements! only the allocated!
// list structure
SLIST_LOCAL void slist_free(slist_t* list)
{
    SLIST_FREE(list);    
}

SLIST_LOCAL size_t slist_length(slist_t* list)
{
    return list->length;
}

SLIST_LOCAL int slist_is_empty(slist_t* list)
{
    return (list->length == 0);
}
 
SLIST_LOCAL void* slist_first(slist_t* list)
{
    return list->first;
}
 
SLIST_LOCAL void* slist_last(slist_t* list)
{
    return list->last;
}

SLIST_LOCAL int slist_is_last(slist_t* list, void* elem)
{
    return (list->last == (slink_t*)elem);
}

SLIST_LOCAL int slist_is_first(slist_t* list, void* elem)
{
    return (list->first == (slink_t*)elem);
}

SLIST_LOCAL void* slist_next(void* elem)
{
    return (void*)(((slink_t*)elem)->next);
}

SLIST_LOCAL void* slist_insert_first(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;

    if ((elem->next = list->first) == NULL)
	list->last  = elem;
    list->first = elem;    
    list->length++;
    return elem;
}

SLIST_LOCAL void* slist_insert_last(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;

    if (list->last == NULL)
	list->first = elem;
    else
	list->last->next = elem;
    list->last = elem;
    elem->next = NULL;
    list->length++;
    return elem;
}

SLIST_LOCAL int slist_is_member(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;
    slink_t* link = list->first;

    while((link != NULL) && (link != elem))
	link = link->next;
    return (elem == link);
}

SLIST_LOCAL void* slist_remove(slist_t* list, void* ptr)
{
    slink_t* elem = (slink_t*) ptr;
    slink_t* link = list->first;
    slink_t* prev = NULL;
    
    while(link && (link != elem)) {
	prev = link;
	link = link->next;
    }

    if (link) {
	if (prev)
	    prev->next = link->next;
	else
	    list->first = link->next;
	if (elem == list->last)
	    list->last = prev;
	list->length--;
    }
    return elem;
}

// "pop" return and remove from head of list
SLIST_LOCAL void* slist_take_first(slist_t* list)
{
    slink_t* elem = list->first;
    list->first = elem->next;
    if (elem == list->last)
	list->last = NULL;
    list->length--;
    return elem;
}

// merge (append) element from list from last in list to
// and clear original from list to and from must be diffrent lists
//
SLIST_LOCAL void slist_merge(slist_t* from, slist_t* to)
{
    if (from->length == 0)
	return;
    else if (to->length == 0) {
	to->first = from->first;
	if ((to->length = from->length) == 0)
	    to->last = NULL;
	else
	    to->last = from->last;
    }
    else {
	to->last->next = from->first;
	to->last = from->last;
	to->length += from->length;
    }
    slist_init(from);
}

SLIST_LOCAL void slist_iter_init(slist_iter_t* iter, slist_t* list)
{
    iter->list = list;
    iter->prev = NULL;
    iter->cur  = list->first;
}

SLIST_LOCAL void* slist_iter_current(slist_iter_t* iter)
{
    return iter->cur;
}

SLIST_LOCAL int slist_iter_eol(slist_iter_t* iter)
{
    return (iter->cur == NULL);
}

SLIST_LOCAL void* slist_iter_next(slist_iter_t* iter)
{
    slink_t* p;
    if ((p = iter->cur) != NULL) {
	iter->prev = p;
	p = p->next;
	iter->cur = p;
    }
    return p;
}

// remove current element, cur is moved to next element
SLIST_LOCAL void slist_iter_remove(slist_iter_t* iter)
{
    slink_t* cur;
    if ((cur = iter->cur)) {
	slink_t* prev = iter->prev;
	slink_t* next = cur->next;
	slist_t* list = iter->list;
	if (prev)
	    prev->next = next;
	else
	    list->first = next;
	if (cur == list->last)
	    list->last = prev;
	iter->cur = next;
	list->length--;
    }
}

#endif
