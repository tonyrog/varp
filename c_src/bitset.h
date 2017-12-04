#ifndef __BITSET_H__
#define __BITSET_H__

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

#ifdef USE_SOME_DAY
static inline int parity(uint64_t v)
{
    v ^= v >> 32;
    v ^= v >> 16;
    v ^= v >> 8;
    v ^= v >> 4;
    v &= 0xf;
    return (0x6996 >> v) & 1;
}

// a variant of above of bitset_ffs using popcount
// x = 2^r*y 
static inline int bitset_xffs(bitset_t* src)
{
    bitset_t two_r = *src - (*src & (*src-1));   //  determine 2^r
    return BITCOUNT(&two_r);
}

static inline int xm_ffs(__m128i x)
{
    int pos = _mm_movemask_epi8(_mm_cmpeq_epi8(x, _mm_setzero_si128()));
    pos = ffs((uint16_t)~pos) - 1;
    return pos < 0 ? -1
	: (pos << 3) + ffs(((unsigned char const*)&x)[pos]) - 1;
}

#endif


static inline void bitset_init(bitset_t* dst)
{
    *dst = 0;
}

static inline int bitset_is_empty(bitset_t* src)
{
    return *src == 0;
}

static inline void bitset_fill(bitset_t* a, int n)
{
    *a = ((1 << n)-1);
}

static inline void bitset_iset(bitset_t* dst, int pos)
{
    *dst |= (1 << pos);
}

static inline void bitset_set(bitset_t* dst, bitset_t* src, int pos)
{
    *dst = *src | (1 << pos);
}

static inline void bitset_nset(bitset_t* dst, bitset_t* src,int offs,int size)
{
    bitset_t t = ((1 << size)-1) << offs;
    *dst = *src | t;
}

static inline void bitset_iclear(bitset_t* dst, int pos)
{
    *dst &= ~(1 << pos);
}

static inline void bitset_clear(bitset_t* dst, bitset_t* src,int pos)
{
    *dst = *src & ~(1 << pos);
}

static inline void bitset_nclear(bitset_t* dst,bitset_t* src,int offs,int size)
{
    bitset_t t = ((1 << size)-1) << offs;
    *dst = *src & ~t;
}

static inline int bitset_is_set(bitset_t* src, int pos)
{
    return ((*src & (1 << pos)) != 0);
}

static inline int bitset_is_nset(bitset_t* src,int offs,int size)
{
    bitset_t t = ((1 << size)-1) << offs;
    return (*src &  t) == t;
}

static inline int bitset_is_clear(bitset_t* src, int pos)
{
    return ((*src & (1 << pos)) == 0);
}

static inline int bitset_is_nclear(bitset_t* src,int offs,int size)
{
    bitset_t t = ((1 << size)-1) << offs;
    return (*src &  t) == 0;
}

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

static inline int bitset_count(bitset_t* src)
{
    return BITCOUNT(*src);
}

static inline int bitset_parity(bitset_t* src)
{
    return PARITY(*src);
}

// check if bitset_count(src) == 1
static inline int bitset_count_one(bitset_t* src)
{
    return *src && ((*src & (*src-1)) == 0);
}

// return one pluse the index of the least significant 1-bit of src
// or 0 if *src is empty
static inline int bitset_first(bitset_t* src)
{
    return FIRST(*src);
}

// format a bitset

static inline char* bitset_format_r(bitset_t* src, char* ptr, size_t maxsize)
{
    bitset_t t = *src;
    char* ptr0 = ptr;
    int i = 1;
    
    if (!t) {
	if (i < (int)maxsize)
	    *ptr++ = '0';
    }
    else {
	while(t && (i <= (int)sizeof(bitset_t)*8) && (i < (int)maxsize)) {
	    *ptr++ = (t&1) ? '1' : '0';
	    t >>= 1;
	    i++;
	}
    }
    *ptr = '\0';
    return ptr0;
}

// format a bitset
// upto 4 bitsets can be formatted in one call to for example
//  printf("%s %s %s %s ...", bitset_format(a),bitset_format(b),
//     bitset_format(c),bitset_format(d))
// threading is not supported


static inline char* bitset_format(bitset_t* src)
{
    static char buf[4][sizeof(bitset_t)*8+1];
    static int select = 0;
    return bitset_format_r(src, buf[select++ & 0x3], sizeof(buf[0]));
}

#endif
