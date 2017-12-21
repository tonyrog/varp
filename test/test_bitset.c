//
// Test bitset implementation
//

#include <stdio.h>

#include "../c_src/bitset.h"

#define FAIL(fmt,...) \
    fprintf(stderr,"%s:%d "fmt "\n",__FILE__,__LINE__, __VA_ARGS__)

int main(int argc, char** argv)
{
    bitset_t bs[MAX_BITSET_SIZE];
    bitset_t dst;
    bitset_t cmp;
    int i, n, offs;

    for (i=0; i < MAX_BITSET_SIZE; i++) {
	bitset_init(&bs[i]);
	bitset_set(&bs[i],&bs[i],i);
    }
    bitset_init(&dst);

    for (i = 0; i < MAX_BITSET_SIZE; i++) {
	int f;
	if (bitset_size(&bs[i]) != 1) {
	    FAIL("bitset count should be = 1 %s",
		 bitset_format(&bs[i]));
	}
	if (bitset_parity(&bs[i]) != 1) {
	    FAIL("bitset parity should be = 1 %s",
		 bitset_format(&bs[i]));
	}
	if (!bitset_is_singleton(&bs[i])) {
	    FAIL("bitset should be singleton %s",
		 bitset_format(&bs[i]));
	}
	if ((f=bitset_first(&bs[i])) != i+1) {
	    FAIL("bitset first %d, should be %d %s",
		 f, i+1, bitset_format(&bs[i]));
	}

	bitset_union(&dst, &dst, &bs[i]);

	if (bitset_size(&dst) != (i+1)) {
	    FAIL("bitset count should be = %d %s",
		 (i+1), bitset_format(&dst));
	}
	if (bitset_parity(&dst) != ((i+1)&1)) {
	    FAIL("bitset parity should be = %d %s",
		    ((i+1)&1), bitset_format(&dst));
	}	
    }

    bitset_fill(&cmp, MAX_BITSET_SIZE);
    if (!bitset_is_equal(&dst, &cmp)) {
	FAIL("bitset union %s not equal to %s",
	     bitset_format(&dst), bitset_format(&cmp));
    }

    if (bitset_size(&cmp) != MAX_BITSET_SIZE) {
	FAIL("bitset size should be %d", MAX_BITSET_SIZE);
    }

    for (i = 0; i < MAX_BITSET_SIZE; i++) {    
	bitset_clear(&bs[i],&bs[i],i);
	if (!bitset_is_empty(&bs[i])) {
	    FAIL("bitset should be empty %s",
		 bitset_format(&bs[i]));
	}
	if (!bitset_is_clear(&bs[i],i)) {
	    FAIL("bit %d should be clear %s",
		 i, bitset_format(&bs[i]));
	}	
    }

    // do intersect
    for (i=0; i < MAX_BITSET_SIZE; i++) {
	bitset_init(&bs[i]);
	bitset_set(&bs[i],&bs[i],i);
    }
    
    for (i = 0; i < MAX_BITSET_SIZE; i++) {
	int sz;
	bitset_t a, b;
	
	bitset_intersect(&a, &dst, &bs[i]);

	if ((sz=bitset_size(&a)) != 1) {
	    FAIL("bitset size %d should be %d, %s",
		 sz, 1, bitset_format(&a));
	}

	bitset_complement(&b, &a);

	if ((sz=bitset_size(&b)) != MAX_BITSET_SIZE-1) {
	    FAIL("bitset size %d should be %d, %s",
		 sz, MAX_BITSET_SIZE-1, bitset_format(&b));
	}
    }

    bitset_init(&dst);
    bitset_nset(&dst, &dst, 0, MAX_BITSET_SIZE);
    if (bitset_size(&dst) != MAX_BITSET_SIZE) {
	FAIL("bitset size should be = %d %s",
	     MAX_BITSET_SIZE, bitset_format(&dst));
    }
    bitset_nclear(&dst, &dst, 0, MAX_BITSET_SIZE);
    if (bitset_size(&dst) != 0) {
	FAIL("bitset size should be = %d %s",
	     0, bitset_format(&dst));
    }
    
    for (n = 2; n < MAX_BITSET_SIZE; n++) {
	for (offs = 0; offs < MAX_BITSET_SIZE-n; offs++) {
	    bitset_t ns;
	    bitset_init(&ns);
	    bitset_nset(&ns, &ns, offs, n);
	    if (bitset_size(&ns) != n) {
		FAIL("bitset size should be = %d %s",
		     n, bitset_format(&ns));
	    }
	    if (!bitset_is_nset(&ns,offs,n)) {
		FAIL("bitset should have n set = %d %s",
		     n, bitset_format(&ns));
	    }
	    bitset_nclear(&ns, &ns, offs, n);
	    if (!bitset_is_empty(&ns)) {
		FAIL("bitset should be empty, %s",
		     bitset_format(&ns));
	    }
	}
    }

    exit(0);
}
