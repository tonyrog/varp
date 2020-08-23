#ifndef __DYNVEC_H__
#define __DYNVEC_H__


#define dynvec(type,name,n)			\
    dynarray_t name ## _dyn_[n];		\
    type name[n]

#define dynvec_size(name,i) name ## _dyn_[(i)].size
#define dynvec_capacity(name,i) name ## _dyn_[(i)].capacity
#define dynvec_init(name,i,capacity)				\
    ((dynarray_init(&name ## _dyn_[(i)], (capacity),sizeof(name[(i)][0])) < 0) ? -1 : \
     (name[(i)] = name ## _dyn_[(i)].base, 0))
#define dynvec_resize(name,i,size)				\
    ((dynarray_resize(&name ## _dyn_[(i)], (size)) < 0) ? -1 :	\
     (name[(i)] = name ## _dyn_[(i)].base, 0))
#define dynvec_set_capacity(name,i,size)			\
    ((dynarray_set_capacity(&name ## _dyn_[(i)], (size)) < 0) ? -1 :	\
     (name[(i)] = name ## _dyn_[(i)].base, 0))
#define dynvec_add(name,i)				\
    (TYPEOF(name[(i)][0])*) dynarray_add(&name ## _dyn_[(i)])
#define dynvec_clear(name,i)				\
    (dynarray_clear(&name ## _dyn_[(i)]), name[(i)] = NULL)


#endif
