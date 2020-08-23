#ifndef __DYNVAR_H__
#define __DYNVAR_H__

#define dynvar(type, name)			\
    dynarray_t name ## _dyn_;			\
    type name

#define dynvar_size(name) name ## _dyn_.size
#define dynvar_capacity(name) name ## _dyn_.capacity
#define dynvar_init(name, capacity)			\
    ((dynarray_init(&name ## _dyn_, (capacity), sizeof(name[0])) < 0) ? -1 : \
     (name = name ## _dyn_.base, 0))
#define dynvar_resize(name, size)				\
    ((dynarray_resize(&name ## _dyn_, (size)) < 0) ? -1 :	\
     (name = name ## _dyn_.base, 0))
#define dynvar_set_capacity(name, size)				\
    ((dynarray_set_capacity(&name ## _dyn_, (size)) < 0) ? -1 :	\
     (name = name ## _dyn_.base, 0))
#define dynvar_add(name)			\
    (dynarray_add(&name ## _dyn_), name = name ## _dyn_.base,		\
     (TYPEOF(name[0])*) DYN_ADDR(&name ## _dyn_, name ## _dyn_.size -1))
#define dynvar_clear(name)			\
    (dynarray_clear(&name ## _dyn_), name = NULL)

#endif
