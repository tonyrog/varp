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
