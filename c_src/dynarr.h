#ifndef __DYNARR_H__

// Grow factor
#define DYN_GROW0 2.0000f
#define DYN_GROW1 1.6180f
#define DYN_GROW2 1.2500f

// switch limit
#define DYN_GROW0_LIMIT 1024
#define DYN_GROW1_LIMIT (1024*1024)

#define DYN_ADDR(dp,i) ((void*)((intptr_t)((dp)->base) + ((i)*(dp)->width)))

#ifndef DYNARR_ALLOC
#define DYNARR_ALLOC(n) malloc((n))
#define DYNARR_REALLOC(ptr,n) realloc((ptr),(n))
#define DYNARR_FREE(ptr) free((ptr))
#endif

typedef struct _dynarray_t // :object_t
{
    size_t capacity;   // max number of elements
    size_t size;       // assigned size <= capacity
    size_t width;      // element size
    void*  base;       // array base address
} dynarray_t;

#define DYNARR_LOCAL static
#define DYNARR_API __attribute__ ((unused))

DYNARR_LOCAL int dynarray_setelement(dynarray_t* dp,int i,void* data) DYNARR_API;
DYNARR_LOCAL size_t dynarray_capacity(dynarray_t* dp) DYNARR_API;


DYNARR_LOCAL size_t dynarray_next_size(size_t cur, size_t capacity)
{
    while((cur < DYN_GROW0_LIMIT) && (cur < capacity))
	cur *= DYN_GROW0;
    while((cur < DYN_GROW1_LIMIT) && (cur < capacity))
	cur *= DYN_GROW1;
    while((cur < capacity))
	cur *= DYN_GROW2;
    return cur;
}

DYNARR_LOCAL size_t dynarray_first_size(size_t capacity)
{
    return dynarray_next_size(1, capacity);
}

DYNARR_LOCAL int dynarray_init(dynarray_t* dp,size_t initial_capacity,size_t width)
{
    void* base;
    size_t capacity;

    if (initial_capacity == 0) {
	capacity = 0;
	base = NULL;
    }
    else {
	capacity = dynarray_first_size(initial_capacity);
	if ((base = DYNARR_ALLOC(capacity*width)) == NULL)
	    return -1;
    }
    dp->capacity = capacity;
    dp->size     = 0;
    dp->width    = width;
    dp->base     = base;
    return 0;
}

DYNARR_LOCAL void dynarray_clear(dynarray_t* dp)
{
    DYNARR_FREE(dp->base);
    dp->base = NULL;
    dp->size = 0;
    dp->capacity = 0;
}


DYNARR_LOCAL size_t dynarray_capacity(dynarray_t* dp)
{
    return (dp == NULL) ? 0 : dp->capacity;
}

DYNARR_LOCAL size_t dynarray_size(dynarray_t* dp)
{
    return (dp == NULL) ? 0 : dp->size;
}

DYNARR_LOCAL int dynarray_set_capacity(dynarray_t* dp, size_t capacity)
{
    void* base;

    if ((base = DYNARR_REALLOC(dp->base, capacity*dp->width)) == NULL)
	return -1;
    dp->base = base;
    dp->capacity = capacity;
    dp->size = dp->size < capacity ? dp->size : capacity;
    return 0;
}

DYNARR_LOCAL int dynarray_resize(dynarray_t* dp, size_t size)
{
    size_t size0;
    if (size > dp->capacity) {
	size_t size0 = (dp->capacity < 1) ? 1 : dp->capacity;
	size_t capacity = dynarray_next_size(size0, size);
	if (dynarray_set_capacity(dp, capacity) < 0)
	    return -1;
    }
    if ((size0 = dp->size) < size) {
	void* ptr = (uint8_t*)dp->base + dp->size*dp->width;
	memset(ptr, 0, (size-size0)*dp->width);
    }
    dp->size = size;
    return 0;
}

DYNARR_LOCAL void* dynarray_element(dynarray_t* dp, int i)
{
    if (dp == NULL) return NULL;
    if (i == 0) return dp->base;
    if ((i < 0) || (i >= (int)dp->size)) return NULL;
    return DYN_ADDR(dp, i);
}

// copy data into dynarray resize if needed
DYNARR_LOCAL int dynarray_setelement(dynarray_t* dp,int i,void* data)
{
    if (dp == NULL || (i < 0)) return -1;
    if (i >= (int)dp->size) {
	if (dynarray_resize(dp, i+1) < 0)
	    return -1;
    }
    memcpy(DYN_ADDR(dp, i), data, dp->width);
    return 0;
}

DYNARR_LOCAL void* dynarray_add(dynarray_t* dp)
{
    size_t n;
    if (dp == NULL) return NULL;
    n = dp->size;
    if (dynarray_resize(dp, n+1) < 0)
	return NULL;
    return DYN_ADDR(dp, n);
}

// FIXME: add a swap version or a flag!
DYNARR_LOCAL void* dynarray_delete(dynarray_t* dp, int i)
{
    uint8_t* src;
    uint8_t* dst;
    size_t len;

    if ((i<0) || (dp == NULL) || (i >= (int)dp->size))
	return NULL;
    dst = DYN_ADDR(dp, i);
    src = dst + dp->width;
    if ((len = (dp->size - i -1)) > 0)
	memmove(dst, src, len*dp->width);
    dp->size--;
    return dst;
}

#endif

