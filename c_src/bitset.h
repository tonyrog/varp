#ifndef __BITSET_H__
#define __BITSET_H__

#include <stdlib.h>

#define BITSET_ULONGLONG

#if defined(BITSET_ULONGLONG)
typedef unsigned long long bitset_t;
#define BITCOUNT(x) __builtin_popcountll((x))
#define PARITY(x)   __builtin_parityll((x))
#define FIRST(x)    __builtin_ffsll((x))
#elif  defined(BITSET_ULONG)
typedef unsigned long bitset_t;
#define BITCOUNT(x) __builtin_popcountl((x))
#define PARITY(x)   __builtin_parityl((x))
#define FIRST(x)    __builtin_ffsl((x))
#elif  defined(BITSET_UINT)
typedef unsigned int bitset_t;
#define BITCOUNT(x) __builtin_popcount((x))
#define PARITY(x)   __builtin_parity((x))
#define FIRST(x)    __builtin_ffs((x))
#endif

#define MAX_BITSET_SIZE ((int)(sizeof(bitset_t)*8))

#define BITSET_NBITS(n) (((bitset_t)-1) >> (MAX_BITSET_SIZE-n))

static inline void bitset_init(bitset_t* dst)
{
    *dst = 0;
}

static inline int bitset_is_empty(bitset_t* src)
{
    return *src == 0;
}

static inline int bitset_is_equal(bitset_t* src1,bitset_t* src2)
{
    return *src1 == *src2;
}

static inline void bitset_fill(bitset_t* a, int n)
{
    *a = BITSET_NBITS(n);
}

static inline void bitset_set(bitset_t* dst,bitset_t* src,int pos)
{
    *dst = *src | ((bitset_t)1 << pos);
}

static inline void bitset_nset(bitset_t* dst,bitset_t* src,int offs,int n)
{
    bitset_t t = BITSET_NBITS(n) << offs;
    *dst = *src | t;
}

static inline void bitset_clear(bitset_t* dst,bitset_t* src,int pos)
{
    *dst = *src & ~((bitset_t)1 << pos);
}

static inline void bitset_nclear(bitset_t* dst,bitset_t* src,int offs,int n)
{
    bitset_t t = BITSET_NBITS(n) << offs;
    *dst = *src & ~t;
}

static inline int bitset_is_set(bitset_t* src, int pos)
{
    return ((*src & ((bitset_t)1 << pos)) != 0);
}

static inline int bitset_is_nset(bitset_t* src,int offs,int n)
{
    bitset_t t = BITSET_NBITS(n) << offs;
    return (*src & t) == t;
}

static inline int bitset_is_clear(bitset_t* src, int pos)
{
    return ((*src & ((bitset_t)1 << pos)) == 0);
}

static inline int bitset_is_nclear(bitset_t* src,int offs,int n)
{
    bitset_t t = BITSET_NBITS(n) << offs;
    return (*src & t) == 0;
}

// = !bitset_is_empty(src)
static inline int bitset_any(bitset_t* src)
{
    return (*src != 0);
}

static inline void bitset_union(bitset_t* dst, bitset_t* a, bitset_t* b)
{
    *dst = *a | *b;
}

static inline void bitset_intersect(bitset_t* dst, bitset_t* a, bitset_t* b)
{
    *dst = *a & *b;
}

static inline void bitset_complement(bitset_t* dst, bitset_t* src)
{
    *dst = ~*src;
}

static inline int bitset_size(bitset_t* src)
{
    return BITCOUNT(*src);
}

static inline int bitset_parity(bitset_t* src)
{
    return PARITY(*src);
}

// check if bitset_count(src) == 1
static inline int bitset_is_singleton(bitset_t* src)
{
    return *src && ((*src & (*src-1)) == 0);
}

// return one pluse the index of the least significant 1-bit of src
// or 0 if *src is empty
static inline int bitset_first(bitset_t* src)
{
    return FIRST(*src);
}

// return 1 if src is singleton and return bit position in ip
// return 0 otherwise
static inline int bitset_single_pos(bitset_t* src, int* ip)
{
    if (bitset_is_singleton(src)) {
	*ip = FIRST(*src)-1;
	return 1;
    }
    return 0;
}

// return 1 if src contains a pair (two bits) and return bit positions
// *ip the lower bit and *jp the higher bit position
// return 0 otherwise
static inline int bitset_pair_pos(bitset_t* src, int* ip, int* jp)
{
    int i;
    if ((i = FIRST(*src)) > 0) { // first bit position
	int j;
	bitset_t src1;
	bitset_clear(&src1, src, i-1);
	if ((j = FIRST(src1)) > 0) { // next bit position
	    bitset_clear(&src1, &src1, j-1);
	    if (bitset_is_empty(&src1)) {
		*ip = i-1;
		*jp = j-1;
		return 1;
	    }
	}
    }
    return 0;
}

// format a bitset

static inline char* bitset_format_r(bitset_t* src, char* ptr, size_t maxsize)
{
    bitset_t t = *src;
    int i = 1;

    if (maxsize == 0)
	return NULL;
    ptr = ptr + maxsize;
    *--ptr = '\0';  // end of string

    if (!t) {
	if (i < (int)maxsize)
	    *--ptr = '0';
    }
    else {
	while(t && (i <= (int)MAX_BITSET_SIZE) && (i < (int)maxsize)) {
	    *--ptr = (t&1) ? '1' : '0';
	    t >>= 1;
	    i++;
	}
    }
    return ptr;
}

// format a bitset
// upto 4 bitsets can be formatted in one call to for example
//  printf("%s %s %s %s ...", bitset_format(a),bitset_format(b),
//     bitset_format(c),bitset_format(d))
// threading is not supported


static inline char* bitset_format(bitset_t* src)
{
    static char buf[4][MAX_BITSET_SIZE+1];
    static int select = 0;
    return bitset_format_r(src, buf[select++ & 0x3], sizeof(buf[0]));
}

#endif
