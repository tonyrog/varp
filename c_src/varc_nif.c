//
// NIF library for running watched literals clauses
//

#ifdef __linux__
#define _GNU_SOURCE
#endif

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <errno.h>
#include <unistd.h>
#include <memory.h>
#include <limits.h>
#include <sys/time.h>
#include "erl_nif.h"

// #define NDEBUG
#include <assert.h>

#define ASSERTIONS
// #define DEBUG
// #define DEBUG_MEM
#define PACKED_VALUE 4         // 1 or 4 values are packed in each byte
// #define USE_CLAUSE_SHUFFLE  // shuffle literals after cleanup
// #define USE_CLAUSE_FIND     // avoid install clauses multiple times

#define UNDEF   0
#define FALSE  -1
#define TRUE    1
#define BOUND   2

#define NEGATE(x) (-(x))

// packed values are stored like
// |--------|xx|  1 value  xx=3 BOUND, 2=TRUE, 0=UNDEF, 1=FALSE
// |xx|xx|xx|xx|  4 values
#define PACKED_BYTES(x) (((x)+PACKED_VALUE-1)/PACKED_VALUE)

// Dirty optional since 2.7 and mandatory since 2.12
#if (ERL_NIF_MAJOR_VERSION > 2) || ((ERL_NIF_MAJOR_VERSION == 2) && (ERL_NIF_MINOR_VERSION >= 7))
#ifdef USE_DIRTY_SCHEDULER
#define NIF_FUNC(name,arity,fptr) {(name),(arity),(fptr),(ERL_NIF_DIRTY_JOB_CPU_BOUND)}
#define NIF_DIRTY_FUNC(name,arity,fptr) {(name),(arity),(fptr),(ERL_NIF_DIRTY_JOB_CPU_BOUND)}
#else
#define NIF_FUNC(name,arity,fptr) {(name),(arity),(fptr),(0)}
#define NIF_DIRTY_FUNC(name,arity,fptr) {(name),(arity),(fptr),(ERL_NIF_DIRTY_JOB_CPU_BOUND)}
#endif
#else
#define NIF_FUNC(name,arity,fptr) {(name),(arity),(fptr)}
#define NIF_DIRTY_FUNC(name,arity,fptr) {(name),(arity),(fptr)}
#endif

#ifdef DEBUG
#define DBG(args...) printf(args)
#else
#define DBG(args...)
#endif

#define UNUSED(x) (void)(x)

static int varp_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varp_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
                         ERL_NIF_TERM load_info);
static void varp_unload(ErlNifEnv* env, void* priv_data);

static ERL_NIF_TERM varp_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_clause_flags(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_queue_first(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_queue_next(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_del_unused_clauses(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_config(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_get(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_put(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_subst(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_is_variable(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_implication_clause(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_conflicting_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_is_equal(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_set_level(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_keep_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_undo_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_move_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_eval(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_order_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_order_sort_first(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_order_sort_last(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_add_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_find_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_use_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);


#define MAX_UINT32 0xffffffff
#define MAX_CLAUSE_LENGTH  0xffffff
#define MAX_CONFLICTING    1024

#define DEFAULT_MAP_SIZE  1024
#define DEFAULT_MAP_GROW  1024
#define DEFAULT_UNDO_SIZE 1024

#define MAX_MAP_SIZE       (1024*1024)   // max inital size
#define MAX_MAP_EXPAND     (256*1024)    // max expand

#define HEAP_BLOCK_SIZE      4096
#define MAX_HEAP_ALLOC_SIZE  (HEAP_BLOCK_SIZE - sizeof(heap_t))
#define HEAP_ALIGN           sizeof(void*)

#define AMASK(ptr,align) (((intptr_t)(ptr)) & ((align)-1))
#define ALIGN(ptr,align) ((((intptr_t) (ptr))+(align)-1) & ~((align)-1))
#define PAD(ptr,align)   (((align)-AMASK(ptr,align)) & ((align)-1))

#define ABS(x) (((x)<0) ? (-(x)) : (x))

#define	RANDOMDEV	"/dev/urandom"

typedef struct _heap_t
{
    struct _heap_t* next;       // next heap block
    uint8_t* current;           // must be aligned
    uint8_t* end;
    uint8_t base[0];
} heap_t;

typedef struct _object_t
{
    struct _object_t* next;
    uint8_t data[];
} object_t;

typedef struct _allocator_t
{
    size_t size;             // object size
    heap_t* heap_list;       // heaps of data
    object_t* free_list;     // list of free objects
} allocator_t;

typedef struct _literal_t
{
    int sign;                  // -1=negative,  1=positive
    struct _variable_t* var;
    struct _wlink_t* wlist;    // list of watch positions
    struct _literal_t* qlink;  // unit propagation queue
} literal_t;

typedef struct _xref_t // :object_t
{
    struct _xref_t* next;
    int  cix;
    long p;
} xref_t;

typedef struct _lqueue_t
{
    size_t size;
    literal_t* head;
    literal_t** tail;
} lqueue_t;

#define VAR_FLAG_MARK         0x01
#define VAR_FLAG_ATOM         0x02

#define LIT_POS 0
#define LIT_NEG 1

typedef struct _variable_t     // :object_t
{
    struct _variable_t* next;  // free list/undo list
    unsigned flags;            // MARK ...
    literal_t* bound;          // if bound/subst this is the bound literal
#ifndef PACKED_VALUE
    int  value;                // -1=false 0=unassigned 1=true 2=bound
#endif
    // int uvalue;             // undo value
    int vix;                   // variable index
    int pkey[3];               // sort keys for positive literals
    int nkey[3];               // sort keys for negative literals    
    int map_index;             // order_map index
    int implication_clause;    // implication clause index -1 = none
    int literal_pos;           // position in implication clause
    int  level;                // implication clause level
    char* strname;             // string formated name or NULL
    struct _symbol_t* names;   // list of aliases
    literal_t lit[2];          // literal containers LIT_POS=0 LIT_NEG=1
    struct _xref_t* xfirst;    // cross ref clauses, falling cix!
    struct _xref_t** xlast;    // cross ref clauses, falling cix!
} variable_t;

typedef struct _symbol_t // :object_t
{
    struct _symbol_t* next;   // next symbol in hash slot or free list
    struct _symbol_t* anext;  // alias link
    uint32_t hash;            // symbol hash
    int is_term;              // either name is a term or name is binary string
    ERL_NIF_TERM term;        // binary or term(as binary)
    uint8_t* data;            // raw data
    size_t   size;            // raw len
    variable_t*  var;
} symbol_t;

// p > 0   p increase
// p < 0   p decrease
// trunc (wlink) to get clause_t* pointer
typedef struct _wlink_t
{
    struct _wlink_t* next;
    long p;
} wlink_t;

#define CLAUSE_FLAG_INQUEUE  0x0001
#define CLAUSE_FLAG_DEAD     0x0002
#define CLAUSE_FLAG_CONFLICT 0x0004

// sizeof wlink should be 8 on 32 bit machine or 16 on 64 bit machine
// 32 bit machine alignement should be 2*8 = 16 bytes
// 64 bit machine alignement should be 2*16 = 32 bytes
#define CLAUSE_ALIGNMENT (2*sizeof(wlink_t))


// typedef literal_t *lit_t;

#define LIT_INTEGER
typedef int32_t lit_t;

typedef struct _clause_t
{
    wlink_t    wl[2];        // ALIGNED watch point 1&2+links (DO NOT MOVE!)
    struct _clause_t* next;  // clause list
    uint64_t stamp;          // last used time (eval_counter clock)
    int cix;                 // clause id (index) 1..N
    size_t size;             // number of literals in lit
    uint8_t  flags;          // INQUEUE ...
    lit_t lit[];             // literal array
} clause_t;

typedef struct _undo_t
{
    size_t bs_size;      // count of all elements in bs
    variable_t* bs;      // list of bound variables
} undo_t;

typedef struct arc4_stream_t {
    uint8_t i;
    uint8_t j;
    uint8_t s[256];
} arc4_stream_t;

typedef struct _varp_t {
    lit_t ltrue;
    lit_t lfalse;
    size_t vnext;       // next free variable number
    size_t vsize;       // allocated size of value map
    size_t vnum;        // number of variables
    size_t cnext;       // next clause number
    size_t csize;       // allocated size of clause map
    size_t cnum;        // number of clauses
    size_t cpermanent;  // number of permanent clauses
    
    size_t ssize;             // size of symbol hash table
    size_t snum;              // number of symbols in symbol hash table
    int num_conflicting;      // number of conflicting clauses saved
    int max_conflicting;      // max number of conflicting <= MAX_CONFLICTING
    int conflicting_clauses[MAX_CONFLICTING];
    size_t grow;              // how much to expand value map
    variable_t** var_map;     // variable map
#ifdef PACKED_VALUE
    uint8_t*     var_value;   // values are stored 8 bit/2 bit packed
#endif
    symbol_t**   sym_map;     // symbol hash table
    int*         order_map;   // literal order table
    int          sort_key[2]; // sort order -1,-2,1,2
    clause_t**   clause_map;  // array of clauses, entries may be null
    size_t       keep;        // number of clauses to keep

    size_t       unum;        // number of levels allocated
    undo_t*      undo;        // array of undo block, one for each level
    size_t       stack_size;  // number of element in undo stack
    size_t       num_bound;   // number of bound variables
    int level;                // current undo level (mark)
    int fifo;                 // literal queue is queue/stack 
    lqueue_t     q;           // literal queue for propagation

    uint64_t  clause_eval_counter[5]; // performance counter 2-clause,3-clause,n-clause
    uint64_t  eval_counter;        // performance counter

    variable_t undef;
    variable_t constant;

    arc4_stream_t as;              // random stream

    allocator_t var_allocator;     // heap storage for variable_t
    allocator_t sym_allocator;     // heap storage for symbols_t
    allocator_t xref_allocator;    // heap storage for xref_t
} varp_t;

#define VARP_TRUE(vp)  ((vp)->ltrue)
#define VARP_FALSE(vp) ((vp)->lfalse)
#define LL_TRUE(vp)    (&(vp)->constant.lit[LIT_POS])
#define LL_FALSE(vp)   (&(vp)->constant.lit[LIT_NEG])

#define MAX(a,b) (((a)>(b)) ? (a) : (b))
#define SWAP_INT(a,b) do { \
	int _t = (a); a=(b); b=(_t);		\
    } while(0)

ErlNifResourceType* varp_res;

ErlNifFunc varp_funcs[] = 
{
    NIF_FUNC( "new",                 1,  varp_new ),
    NIF_FUNC( "info",                2,  varp_info ),
    NIF_FUNC( "config",              3,  varp_config ),    
    NIF_FUNC( "add_variable",        2,  varp_add_variable ),
    NIF_FUNC( "get",                 2,  varp_get ),
    NIF_FUNC( "put",                 3,  varp_put ),
    NIF_FUNC( "put",                 4,  varp_put ),
    NIF_FUNC( "subst",               3,  varp_subst ),
    NIF_FUNC( "key",                 3,  varp_key ),
    NIF_FUNC( "implication_clause",  2,  varp_implication_clause ),
    NIF_FUNC( "conflicting_clause",  2,  varp_conflicting_clause ),
    NIF_FUNC( "is_variable",         2,  varp_is_variable ),
    NIF_FUNC( "is_bound",            2,  varp_is_bound ),
    NIF_FUNC( "is_equal",            3,  varp_is_equal ),
    NIF_FUNC( "set_level",           2,  varp_set_level ),
    NIF_FUNC( "keep_level",          2,  varp_keep_level ),
    NIF_FUNC( "move_level",          3,  varp_move_level ),
    NIF_FUNC( "undo_level",          2,  varp_undo_level ),
    NIF_FUNC( "eval",                1,  varp_eval ),
    NIF_FUNC( "add_clause",          2,  varp_add_clause ),
    NIF_FUNC( "add_clause",          3,  varp_add_clause ),
    NIF_FUNC( "add_clause",          4,  varp_add_clause ),
    NIF_FUNC( "add_clause",          5,  varp_add_clause ),
    NIF_FUNC( "add_clause",          6,  varp_add_clause ),
    NIF_FUNC( "add_clause",          7,  varp_add_clause ),
    NIF_FUNC( "get_clause",          4,  varp_get_clause ),
    NIF_FUNC( "get_clause_flags",    2,  varp_get_clause_flags ),
    NIF_FUNC( "del_clause",          2,  varp_del_clause ),
    NIF_FUNC( "del_unused_clauses",  1,  varp_del_unused_clauses ),
    NIF_FUNC( "get_clauses",         3,  varp_get_clauses ),
    NIF_FUNC( "get_queue_first",     1,  varp_get_queue_first ),
    NIF_FUNC( "get_queue_next",      2,  varp_get_queue_next ),    
    NIF_FUNC( "get_bindings",        3,  varp_get_bindings ),
    NIF_FUNC( "get_nbindings",       3,  varp_get_nbindings ),
    NIF_FUNC( "order_first",         1,  varp_order_first ),
    NIF_FUNC( "order_next",          3,  varp_order_next ),
    NIF_FUNC( "order_sort",          4,  varp_order_sort ),
    NIF_FUNC( "order_sort_first",    2,  varp_order_sort_first ),
    NIF_FUNC( "order_sort_last",     2,  varp_order_sort_last ),
    NIF_FUNC( "add_symbol",          3,  varp_add_symbol),
    NIF_FUNC( "get_symbol",          2,  varp_get_symbol ),
    NIF_FUNC( "find_symbol",         2,  varp_find_symbol ),
    NIF_FUNC( "use_clause",          2,  varp_use_clause ),
};

// Atom macros
#define ATOM(name) atm_##name

#define DECL_ATOM(name) \
    ERL_NIF_TERM atm_##name = 0

// require env in context (ugly)
#define LOAD_ATOM(name)			\
    atm_##name = enif_make_atom(env,#name)

#define LOAD_ATOM_STRING(name,string)			\
    atm_##name = enif_make_atom(env,string)

DECL_ATOM(ok);
DECL_ATOM(true);
DECL_ATOM(false);
DECL_ATOM(default);
DECL_ATOM(grow);
DECL_ATOM(size);
DECL_ATOM(error);
DECL_ATOM(or);
DECL_ATOM(xor);
DECL_ATOM(inqueue);
DECL_ATOM(dead);
DECL_ATOM(watch);
DECL_ATOM(literal);
DECL_ATOM(variable);
DECL_ATOM(flags);
DECL_ATOM(mask);
DECL_ATOM(undefined);
DECL_ATOM(identity);
DECL_ATOM(random);
DECL_ATOM(occur);
DECL_ATOM(plus_occur);
DECL_ATOM(minus_occur);

// info
DECL_ATOM(max_clause_length);
DECL_ATOM(max_conflicting);
DECL_ATOM(num_conflicting);
DECL_ATOM(number_of_clauses);
DECL_ATOM(number_of_learned_clauses);
DECL_ATOM(number_of_variables);
DECL_ATOM(number_of_bound_variables);
DECL_ATOM(number_of_unbound_variables);
DECL_ATOM(clause_eval_counter);
DECL_ATOM(clause2_eval_counter);
DECL_ATOM(clause3_eval_counter);
DECL_ATOM(eval_counter);
DECL_ATOM(undo_stack_size);
DECL_ATOM(value_stack_size);
DECL_ATOM(unit);
DECL_ATOM(use);
DECL_ATOM(reset);
DECL_ATOM(permanent);
DECL_ATOM(keep);
DECL_ATOM(level);
DECL_ATOM(fifo);
DECL_ATOM(lifo);


#ifdef DEBUG_MEM
#define VARP_ALLOC(n)       debug_alloc((n))
#define VARP_REALLOC(ptr,n) debug_realloc((ptr),(n))
#define VARP_FREE(ptr)      debug_free((ptr))
#else
#define VARP_ALLOC(n)       enif_alloc((n))
#define VARP_REALLOC(ptr,n) enif_realloc((ptr),(n))
#define VARP_FREE(ptr)      enif_free((ptr))
#endif

size_t varp_allocated = 0;

void* debug_alloc(size_t n)
{
    void* ptr;

    if ((ptr = enif_alloc(sizeof(size_t) + n)) != NULL) {
	*((size_t*)ptr) = n;
	varp_allocated += n;
	return ptr+sizeof(size_t);
    }
    return NULL;
}

void* debug_realloc(void* ptr, size_t n)
{
    if (ptr == NULL)
	return debug_alloc(n);
    else {
	void* pptr = ptr - sizeof(size_t);
	size_t m = *((size_t*)pptr);
	varp_allocated -= m;
	if ((ptr = enif_realloc(pptr, sizeof(size_t) + n)) != NULL) {
	    *((size_t*)ptr) = n;
	    varp_allocated += n;
	    return ptr+sizeof(size_t);
	}
	return NULL;
    }
}

void debug_free(void* ptr)
{
    if (ptr != NULL) {
	void* pptr = ptr - sizeof(size_t);
	size_t m = *((size_t*)pptr);
	varp_allocated -= m;
	enif_free(pptr);
    }
}

#define EXT  0x80
#define SIGN 0x40
#define MASK0 0x3f
#define MASK  0x7f

// NB  MAXLEN
// 1   6  |0|s| b6..b0|
// 2   13 |1|s| b6..b0||0|b7..b0|
// 3   20 |1|s| b6..b0||1|b7..b0||0|b7..b0|
// 4   27 |1|s| b6..b0||1|b7..b0||1|b7..b0||0|b7..b0|
// 5   34 |1|s| b6..b0||1|b7..b0||1|b7..b0||1|b7..b0||0|b7..b0|
#ifdef NOT_USED
static int compress_int(int li, uint8_t* ptr)
{
    uint8_t sign = 0;
    uint8_t ext  = 0;
    int len, nb;
    
    if (li < 0) {
	sign = SIGN;
	li = -li;
    }
    
    if (li <= MASK0) {
	len = 6;
	nb  = 1;
    }
    else {
	len = sizeof(int)*8 - __builtin_clz(li);
	nb = 1 + (((len - 6) + 6) / 7);
    }
    ptr = ptr + nb;
    while(len > 6) {
	*--ptr = (li & MASK) | ext;
	ext = EXT;
	li >>= 7;
	len -= 7;
    }
    *--ptr = (li & MASK0) | ext | sign;
    return nb;
}

static int decompress_int(uint8_t* ptr)
{
    uint8_t code = *ptr++;
    int li = code & MASK0;
    int sign = code & SIGN;

    while(code & EXT) {
	code = *ptr++;
	li = (li << 7) | (code & MASK);
    }
    if (sign)
	li = -li;
    return li;
}
#endif
static uint32_t djb_hash(uint8_t* ptr, size_t len)
{
    uint32_t h = 5381;
    while(len--)
	h = ((h << 5) + h) + (*ptr++);
    return h;
}

// Clause point from wlink_t pointer
static clause_t* clause_pointer(wlink_t* wl)
{
    intptr_t w = (intptr_t) wl;
    return (clause_t*) (w & ~(CLAUSE_ALIGNMENT-1));
}

static int wlink_index(wlink_t* wl)
{
    intptr_t w = (intptr_t) wl;
    return (w & (CLAUSE_ALIGNMENT-1)) / sizeof(wlink_t);
}

// primitive negate a literal
static inline literal_t* neg_ll(literal_t* lp)
{
    return (lp->sign < 0) ? &lp->var->lit[LIT_POS] : &lp->var->lit[LIT_NEG];
}

static inline literal_t* vix_ll(varp_t* vp, int vix)
{
    return (vix < 0) ? &vp->var_map[-vix]->lit[LIT_NEG] :
	&vp->var_map[vix]->lit[LIT_POS];
}

static inline lit_t vix_l(varp_t* vp, int vix)
{
#ifdef LIT_INTEGER
    UNUSED(vp);    
    return (lit_t) vix;
#else
    return (lit_t) vix_ll(vp, vix);
#endif
}

static inline int index_ll(literal_t* lp)
{
    return (lp->sign < 0) ? -lp->var->vix : lp->var->vix;
}

static inline int is_neg_l(lit_t l)
{
#ifdef LIT_INTEGER
    return l < 0;
#else
    return (l->sign < 0);
#endif
}

static inline int is_constant(int x)
{
    return ((x == TRUE) || (x == FALSE));
}

static inline int is_constant_l(varp_t* vp, lit_t l)
{
    return ((l == VARP_TRUE(vp)) || (l == VARP_FALSE(vp)));
}

static inline int index_l(lit_t l)
{
#ifdef LIT_INTEGER
    return l;
#else
    return index_ll(l);
#endif
}

static inline lit_t neg_l(lit_t l)
{
#ifdef LIT_INTEGER
    return -l;
#else
    return neg_ll(l);
#endif
}

static inline literal_t* l2ll(varp_t* vp, lit_t l)
{
#ifdef LIT_INTEGER
    return vix_ll(vp, l);
#else
    UNUSED(vp);
    return (literal_t*) l;
#endif
}

static inline lit_t ll2l(varp_t* vp, literal_t* lp)
{
    UNUSED(vp);    
#ifdef LIT_INTEGER
    return index_ll(lp);
#else
    UNUSED(vp);
    return (lit_t) lp;
#endif
}

// access variable from lit_t
static inline variable_t* var_l(varp_t* vp, lit_t lp)
{
    literal_t* lit = l2ll(vp,lp);
    return lit->var;
}

// primitiv get variable value
static inline int get_vv(varp_t* vp, variable_t* var)
{
#ifdef PACKED_VALUE
    
#if PACKED_VALUE == 1
    int i = var->vix;
    return ((int)vp->var_value[i])-1;
#elif PACKED_VALUE == 4
    int i = var->vix >> 2;    
    int j = ((var->vix) & 0x3) << 1;  // shift 0,2,4,6
    return ((vp->var_value[i] >> j) & 0x3)-1;
#endif
    
#else
    UNUSED(vp);
    return var->value;
#endif
}

static inline void set_vv(varp_t* vp, variable_t* var, int value)
{
#ifdef PACKED_VALUE
    
#if PACKED_VALUE == 1
    int i = var->vix;
    vp->var_value[i] = (value+1)&0x3;
#elif PACKED_VALUE == 4
    int i = var->vix >> 2;
    int j = ((var->vix)&0x3) << 1;  // shift 0,2,4,6
    vp->var_value[i] = (vp->var_value[i] & ~(0x3<<j)) |
	(((value+1)&0x3) << j);
#endif

#else
    UNUSED(vp);
    var->value = value;
#endif
}

// primitiv get literal value
static inline int get_ll(varp_t* vp, literal_t* lp)
{
    return (lp->sign < 0) ? NEGATE(get_vv(vp,lp->var)) : get_vv(vp,lp->var);
}

// primitive get lit value
static inline int get_l(varp_t* vp, lit_t l)
{
    return get_ll(vp, l2ll(vp, l));
}

// primitive set literal value
static inline void set_ll(varp_t* vp, literal_t* lp, int value)
{
    if (lp->sign < 0)
	set_vv(vp,lp->var,NEGATE(value));
    else
	set_vv(vp,lp->var,value);
}

// given a literal pointer, return the susbstituted literal value
static inline literal_t* lookup_literal(literal_t* lp)
{
    while (lp->var->bound) { // resolve literal
	if (lp->sign > 0)
	    lp = lp->var->bound;
	else // negate literal
	    lp = neg_ll(lp->var->bound);
    }
    return lp;
}

static inline int get_literal_value(varp_t* vp, literal_t* lp)
{
    lp = lookup_literal(lp);
    return get_ll(vp, lp);
}

static inline void set_literal_value(varp_t* vp, literal_t* lp, int value)
{
    while (lp->var->bound) { // resolve literal
	if (lp->sign < 0) value = NEGATE(value);
	lp = lp->var->bound;
    }
    set_ll(vp, lp, value);
}

static inline int lit_value(varp_t* vp, lit_t l)
{
    literal_t* lp = l2ll(vp, l);
    return get_literal_value(vp, lp);
}


static inline int get_variable_value(varp_t* vp, variable_t* var)
{
    if (var->bound)
	return get_literal_value(vp, var->bound);
    else
	return get_vv(vp, var);
}

static inline void set_variable_value(varp_t* vp, variable_t* var, int value)
{
    if (var->bound)
	set_literal_value(vp, var->bound, value);
    else
	set_vv(vp, var, value);
}

// return true if variable is constant or bound to other variable
// vix is a variable index or the negation of the same
static int vis_bound(varp_t* vp, int vix)
{
    variable_t* var = vp->var_map[ABS(vix)];
    return get_vv(vp, var) != UNDEF;
}


char* format_variable(variable_t* var)
{
    static char vn1[32];
    static char vn2[32];
    static char* varname = vn2;

    varname = (varname == vn1) ? vn2 : vn1;
    
    if (var->strname != NULL)
	snprintf(varname, sizeof(vn1), "%s", var->strname);	
    else
	snprintf(varname, sizeof(vn1), "%d", var->vix);
    return varname;
}

char* format_literal(varp_t* vp, literal_t* lp)
{
    static char ln1[32];
    static char ln2[32];
    static char* litname = ln2;
    char* n = (lp->sign < 0) ? "!" : "";
    UNUSED(vp);
    // alternate to allow to printf arguments!!
    litname = (litname == ln1) ? ln2 : ln1; 

    if (lp->var->strname != NULL)
	snprintf(litname, sizeof(ln1), "%s%s", n, lp->var->strname);
    else
	snprintf(litname, sizeof(ln1), "%s%d", n, lp->var->vix);
    return litname;
}

char* format_lit(varp_t* vp, lit_t l)
{
    return format_literal(vp, l2ll(vp, l));
}

static heap_t* new_heap_block(heap_t* next)
{
    heap_t* hp;

    if ((hp = VARP_ALLOC(HEAP_BLOCK_SIZE + HEAP_ALIGN - 1)) == NULL)
	return NULL;
    hp->next    = next;
    hp->current = hp->base + PAD(hp->base,HEAP_ALIGN);
    hp->end     = hp->current + MAX_HEAP_ALLOC_SIZE;
    return hp;
}

static void* heap_alloc(heap_t** pool, size_t size)
{
    heap_t* hp;
    heap_t* hq;
    void* ptr;

    if (size > MAX_HEAP_ALLOC_SIZE)
	return NULL;
    hp = *pool;
    if ((hp == NULL) || (hp->current + size >= hp->end)) {
	if ((hq = new_heap_block(hp)) == NULL)
	    return NULL;
	*pool = hq;
	hp = hq;
    }
    ptr = hp->current;
    hp->current += size;
    return ptr;
}

static void cleanup_heap(heap_t* hp)
{
    while(hp != NULL) {
	heap_t* hp_next = hp->next;
	VARP_FREE(hp);
	hp = hp_next;
    }
}

static int init_allocator(allocator_t* ap, size_t size)
{
    ap->size = ALIGN(size, HEAP_ALIGN);
    ap->heap_list = NULL;
    ap->free_list = NULL;
    return 0;
}

static void cleanup_allocator(allocator_t* ap)
{
    cleanup_heap(ap->heap_list);
    ap->heap_list = NULL;
    ap->free_list = NULL;
}

static void* varp_alloc(allocator_t* ap)
{
    object_t* ptr;
    if ((ptr = ap->free_list) == NULL)
	return heap_alloc(&ap->heap_list, ap->size);
    ap->free_list = ptr->next;
    return ptr;
}

static void varp_free(allocator_t* ap, void* ptr)
{
    ((object_t*)ptr)->next = ap->free_list;
    ap->free_list = (object_t*)ptr;
}

static void arc4_init(arc4_stream_t *as)
{
    int n;

    for (n = 0; n < 256; n++)
	as->s[n] = n;
    as->i = 0;
    as->j = 0;
}

static void arc4_add_random(arc4_stream_t* as, uint8_t* dat, int datlen)
{
    int     n;
    uint8_t si;

    as->i--;
    for (n = 0; n < 256; n++) {
	as->i = (as->i + 1);
	si = as->s[as->i];
	as->j = (as->j + si + dat[n % datlen]);
	as->s[as->i] = as->s[as->j];
	as->s[as->j] = si;
    }
}

static inline uint8_t arc4_getbyte(arc4_stream_t* as)
{
    uint8_t si, sj;

    as->i = (as->i + 1);
    si = as->s[as->i];
    as->j = (as->j + si);
    sj = as->s[as->j];
    as->s[as->i] = sj;
    as->s[as->j] = si;
    return as->s[(si + sj) & 0xff];
}

static uint32_t arc4_random(arc4_stream_t* as)
{
    uint32_t val;

    val = arc4_getbyte(as) << 24;
    val |= arc4_getbyte(as) << 16;
    val |= arc4_getbyte(as) << 8;
    val |= arc4_getbyte(as);
    return val;
}

static void arc4_stir(arc4_stream_t* as)
{
    FILE* f;
    int i;
    struct {
	struct timeval tv;
	pid_t pid;
	uint8_t rnd[128 - sizeof(struct timeval) - sizeof(pid_t)];
    } rdat;

    gettimeofday(&rdat.tv, NULL);
    rdat.pid = getpid();
    if ((f = fopen(RANDOMDEV, "r")) != NULL) {
	int r = fread(rdat.rnd, 1, sizeof(rdat.rnd), f);
	(void) r;
	fclose(f);
    }
    arc4_add_random(as, (void *) &rdat, sizeof(rdat));
    for (i = 0; i < 1024; i++)
	arc4_getbyte(as);
}

static uint32_t arc4_random_uniform(arc4_stream_t* as, uint32_t upper_bound)
{
    uint32_t r, min;

    if (upper_bound < 2)
	return 0;
    if (upper_bound > 0x80000000)
	min = 1 + ~upper_bound;	// 2**32 - upper_bound
    else
	// (2**32 - (x * 2)) % x == 2**32 % x when x <= 2**31 
	min = ((0xffffffff - (upper_bound * 2)) + 1) % upper_bound;
    while(1) {
	r = arc4_random(as);
	if (r >= min)
	    break;
    }
    return r % upper_bound;
}

static inline void clear_wlink(wlink_t* wlp)
{
    wlp->p = -1;
    wlp->next = NULL;   // mark dead for debug
}

static inline void link_wlink(wlink_t* wlp, literal_t* lp)
{
    wlp->next = lp->wlist;  // link literal
    lp->wlist = wlp;
}

static void set_wlink(wlink_t* wlp, long p, literal_t* lp)
{
    wlp->p = p;   // new watch point
    link_wlink(wlp, lp);
}

static void unwatch(varp_t* vp, clause_t* cp, lit_t l)
{
    literal_t* lp = l2ll(vp, l);
    wlink_t** wlp = &lp->wlist;
    wlink_t* wl;

    DBG("UNWATCH cix=%d lit=%d wl=%p\r\n", cp->cix, index_l(l), *wlp);

    while((wl = *wlp) && (clause_pointer(wl) != cp))
	wlp = &(wl->next);
    if (wl != NULL) {
	*wlp = wl->next;  // unlink
	wl->p = -1;       // mark as not used
    }
}

// remove the TWO watch points
static void unwatch_clause(varp_t* vp, clause_t* cp)
{
    long p;
    if ((p = cp->wl[0].p) > 0) unwatch(vp, cp, cp->lit[p]);
    if ((p = cp->wl[1].p) > 0) unwatch(vp, cp, cp->lit[p]);
}

// FIXME clauses should really be heap allocated?
// except we need to garbage collect in that case when
// deleting clauses...or

static clause_t* clause_alloc(varp_t* vp, int size)
{
    UNUSED(vp);
    clause_t* cp;
    int r;
    
    if (size < 2)
	return NULL;

    if ((r=posix_memalign((void**)&cp, CLAUSE_ALIGNMENT,
			  sizeof(clause_t) + sizeof(lit_t)*size)) != 0) {
	errno = r;
	return NULL;
    }
    clear_wlink(&cp->wl[0]);
    clear_wlink(&cp->wl[1]);
    cp->next = NULL;
    cp->size  = size;
    cp->flags = 0;
    return cp;
}

static void clause_free(varp_t* vp, clause_t* cp)
{
    int i = cp->cix;
    if (i >= 0) {
	vp->clause_map[i] = NULL;
	vp->cnum--;
    }
    free(cp);
}

static void lqueue_init(lqueue_t* q)
{
    q->head = NULL;
    q->tail = &q->head;
    q->size = 0;    
}

static void lqueue_clear(lqueue_t* q)
{
    lqueue_init(q);
}

static void lqueue_put(varp_t* vp, lit_t lp)
{
    lqueue_t* q = &vp->q;
    literal_t* mp;
    DBG("ENQ %s qsize=%ld\r\n", format_lit(vp, lp), q->size);
    assert(!is_constant_l(vp, lp));
    mp = l2ll(vp, lp);
    if (vp->fifo) { // put element last
	mp->qlink = NULL;
	*q->tail = mp;
	q->tail = &(mp->qlink);
    }
    else {  // put element first
	mp->qlink = q->head;
	q->head = mp;
	if (mp->qlink == NULL)
	    q->tail = &(mp->qlink);
    }
    q->size++;
}

// always get from head of list(queue)
static literal_t* lqueue_get(varp_t* vp)
{
    lqueue_t* q = &vp->q;
    literal_t* lp;
    
    if ((lp = q->head) == NULL)
	return NULL;
    if ((q->head = lp->qlink) == NULL)
	q->tail = &q->head;
    q->size--;
    DBG("DEQ %s(%d,%d) qsize=%ld\r\n", format_literal(vp,lp),
	lp->var->vix, lp->var->literal_pos,  q->size);
    return lp;
}

static void push_variable(varp_t* vp, variable_t* var, int level)
{
    assert(get_vv(vp, var) == UNDEF);
    DBG("PUSH VARIABLE: var=%s, level=%d, value=%d\r\n",
	format_variable(var), level, get_vv(vp, var));
    // var->uvalue = get_vv(vp, var);
    var->next = vp->undo[level].bs;
    vp->undo[level].bs = var;
    vp->undo[level].bs_size++;
    vp->stack_size++;
    vp->num_bound++;
}

//
// FIXME: log_permanent
// send message to process(es) interested in permanent assignments
// of variables.
//
static inline void log_permanent(varp_t* vp, variable_t* var, int level)
{
#if LOG_ASSIGN_ATOM    
    if ((level == 0) && (var->flags & VAR_FLAG_ATOM)) {
	// fixme: send message monitor variables...
	printf("PERMANENT(ATOM) %s=%d\r\n",format_variable(var),(get_vv(vp,var)+1)>>1);
    }
#else
    UNUSED(vp);
    UNUSED(var);
    UNUSED(level);
#endif
}


static inline void set_literal(varp_t* vp,lit_t lp,int value,
			       long li,int cix, int level)
{
    variable_t* var = var_l(vp, lp);
    DBG("SET_LITERAL %d = %d\r\n", index_l(lp), value);
    assert(!is_constant(get_variable_value(vp, var)));
    assert(var->bound == NULL);
    set_vv(vp, var, is_neg_l(lp) ? NEGATE(value) : value);
    // set_variable_value(vp, var, is_neg_l(lp) ? -value : value);
    var->implication_clause = cix;
    var->literal_pos = li;
    var->level = level;
    log_permanent(vp, var, level);
}

// put value set_literal and push the correct literal on queue
// put (X, TRUE)   => enq(!X)   1  1  negate(X)
// put (X, FALSE)  => enq(X)    1 -1  X
// put (!X, TRUE)  == enq(X)   -1  1  negate(X)
// put (!X, FALSE) == enq(!X)  -1 -1  X
//
static void put_literal(varp_t* vp,lit_t lp,int value,long li,int cix,int level)
{
    variable_t* var = var_l(vp, lp);
    if (level < 0) level = vp->level;
    push_variable(vp, var, level);
    if (is_constant(value))
	lqueue_put(vp, (value==TRUE) ? neg_l(lp) : lp);
    set_literal(vp, lp, value, li, cix, level);
}

static void undo_init(varp_t* vp)
{
    vp->unum = DEFAULT_UNDO_SIZE;
    vp->undo = VARP_ALLOC(DEFAULT_UNDO_SIZE * sizeof(undo_t));
    memset(vp->undo, 0, DEFAULT_UNDO_SIZE * sizeof(undo_t));
    vp->stack_size = 0;
    vp->num_bound = 0;
    vp->level = 0;
}

// set current bindings level
static int set_level(varp_t* vp, int level)
{
    if (level >= (int)vp->unum) {
	unsigned int n = vp->unum;
	vp->unum *= 2;
	vp->undo = VARP_REALLOC(vp->undo, vp->unum*sizeof(undo_t));
	memset(vp->undo+n, 0, n*sizeof(undo_t));
    }
    vp->level = level;
    DBG("SET LEVEL: level=%d\r\n", level);
#ifdef ASSERTIONS
    {
	int i;
	for (i = level+1; i < (int)vp->unum; i++) {
	    assert(vp->undo[i].bs == NULL);
	    assert(vp->undo[i].bs_size == 0);
	}
    }
#endif
    return 0;
}

static void undo_level(varp_t* vp, int level)
{
    variable_t* bp = vp->undo[level].bs;
    int nbound = vp->undo[level].bs_size;

    while(bp != NULL) {
	DBG("POP VARIABLE %s value=%d\r\n",
	    format_variable(bp), get_variable_value(vp, bp));
	assert(bp->bound == NULL);
	set_vv(vp, bp, UNDEF);
	// set_variable_value(vp, bp, bp->uvalue);
	bp = bp->next;
    }
    vp->stack_size -= nbound;
    vp->num_bound  -= nbound;
    vp->undo[level].bs = NULL;
    vp->undo[level].bs_size = 0;
    // must clear queue
    lqueue_clear(&vp->q);
}

// move bindings from src level to dst level
// the bindings are moved last into dst level
static void move_level(varp_t* vp, int src, int dst)
{
    variable_t* var = vp->undo[src].bs;

    if (var) {
	log_permanent(vp, var, dst);
	// find last binding
	while(var->next) {	    
	    var = var->next;
	    log_permanent(vp, var, dst);
	}
	var->next = vp->undo[dst].bs;
	vp->undo[dst].bs = vp->undo[src].bs;
	vp->undo[dst].bs_size += vp->undo[src].bs_size;
	vp->undo[src].bs = NULL;
	vp->undo[src].bs_size = 0;
    }
}

// clear but do not undo a level (keep the bindings)
static void keep_level(varp_t* vp, int level)
{
    int bound = vp->undo[level].bs_size;
    vp->stack_size -= bound;
    vp->undo[level].bs = NULL;
    vp->undo[level].bs_size = 0;
}

static void init_literal(literal_t* lp, variable_t* var, int sign)
{
    lp->sign = sign;
    lp->var  = var;
    lp->wlist = NULL;
    lp->qlink = NULL;
}

static void init_variable(varp_t* vp, variable_t* var, int value, int vix)
{
    var->vix   = vix;
    var->next = NULL;    
    var->flags = 0;
    var->bound = NULL;
    var->pkey[0] = var->pkey[1] = var->pkey[2] = 0;
    var->nkey[0] = var->nkey[1] = var->nkey[2] = 0;    

    var->map_index = vix;
    var->implication_clause  = -1;
    var->literal_pos = -1;
    var->level = -1;
    var->strname = NULL;
    var->names = NULL;

    var->xfirst = NULL;
    var->xlast  = &var->xfirst;    

    set_vv(vp, var, value);  // may use var->vix!!!

    init_literal(&var->lit[LIT_POS], var, TRUE);
    init_literal(&var->lit[LIT_NEG], var, FALSE);
}

// return 1 if a is equal to b, return 0 otherwise
static int clause_is_equal(lit_t* a, lit_t* b, int size)
{
    int i = 0;
    while((i<size) && (a[i] == b[i]))
	i++;
    return (i == size);
}

// return 1 if a is subclause of b, return 0 otherwise
// assume both clauses are sorted in falling order
// (C D E)   (A B C D E F)
int clause_is_subclause(lit_t* a, lit_t* b, int size_a, int size_b)
{
    if (size_a == size_b)
	return clause_is_equal(a, b, size_a);
    else if (size_a < size_b) {
	int i = 0;
	int j = 0;

	while(i < size_a) {
	    while((j < size_b) && (a[i] > b[j]))
		j++;
	    if (j == size_b) return 0;
	    if (a[i] < b[j]) return 0;
	    i++;
	    j++;
	}
	return (i == size_a);
    }
    else
	return 0;
}

// see if clause is already installed return index to installed clause if success
// return -1 otherwise
int clause_find(varp_t* vp, lit_t* lit, size_t size)
{
    int i;

    // slow version just to get stats!!!
    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	if ((cp->size == size) && clause_is_equal(lit, cp->lit, size))
	    return cp->cix;
    }
    return -1;
}

static int clause_insert(varp_t* vp, clause_t* cp)
{
    int i = vp->cnext++;

    cp->cix = i;
    cp->stamp = vp->eval_counter;
    
    if (vp->cnext == vp->csize) {
	unsigned int new_csize = vp->csize + vp->grow;
	clause_t** cpp;
	
	if (!(cpp = VARP_REALLOC(vp->clause_map, new_csize*sizeof(clause_t**))))
	    return -1;
	vp->clause_map = cpp;
	vp->csize = new_csize;
    }
    vp->cnum++;
    vp->clause_map[i] = cp;
    return i;
}

static int get_boolean(ErlNifEnv* env, ERL_NIF_TERM term, int* bool)
{
    (void) env;
    if (term == ATOM(true))
	*bool = 1;
    else if (term == ATOM(false))
	*bool = 0;
    else
	return 0;
    return 1;
}

static ERL_NIF_TERM make_boolean(ErlNifEnv* env, int value)
{
    (void) env;
    return value ? ATOM(true) : ATOM(false);
}

// get primitive literal value
static int vif_get_ll(ErlNifEnv* env,varp_t* vp,ERL_NIF_TERM arg,
		      literal_t** lpp)
{
    int x;
    if (!enif_get_int(env, arg, &x))
	return 0;
    if (x == 0) x = FALSE;
    else if (ABS(x) >= (int)vp->vnext) {
	DBG("literal %d out of range\r\n", x);
	return 0;
    }
    *lpp = vix_ll(vp, x);
    return 1;
}

// get primitive lit value
static int vif_get_l(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, lit_t* l)
{
    int x;
    if (!enif_get_int(env, arg, &x))
	return 0;
    if (x == 0) x = FALSE;
    else if (ABS(x) >= (int)vp->vnext) {
	DBG("literal %d out of range\r\n", x);
	return 0;
    }
    *l = vix_l(vp, x);
    return 1;
}

static int vif_get_v(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg,
		     variable_t** vpp)
{
    lit_t xp;
    if (!vif_get_l(env, vp, arg, &xp)) return 0;
    *vpp = var_l(vp, xp);
    return 1;
}

// Expect a literal from term input, and lookup the literal
// for substitution 
static int vif_get_lit(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, lit_t* xp)
{
    literal_t* lp;
    if (!vif_get_ll(env, vp, arg, &lp))
	return 0;
    lp = lookup_literal(lp);
    *xp = ll2l(vp, lp);
    return 1;
}

static int vif_get_literal(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg,
			   literal_t** lpp)
{
    if (!vif_get_ll(env, vp, arg, lpp))
	return 0;
    *lpp = lookup_literal(*lpp);
    return 1;
}

static int vif_get_variable(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg,
			    variable_t** vpp)
{
    variable_t* var;
    if (!vif_get_v(env, vp, arg, &var))
	return 0;
    while(var->bound)
	var = var->bound->var;
    *vpp = var;
    return 1;
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, literal_t* lp)
{
    return enif_make_int(env, index_ll(lp));
}

static void cleanup(varp_t* vp)
{
    if (vp->sym_map) {
	int i;
	for (i = 0; i < (int)vp->ssize; i++) {
	    symbol_t* sp = vp->sym_map[i];
	    while(sp) {
		VARP_FREE(sp->data);
		sp = sp->next;
	    }
	}
	VARP_FREE(vp->sym_map);
	vp->sym_map = NULL;		    
    }
    
    if (vp->var_map) {
	VARP_FREE(vp->var_map);
	vp->var_map = NULL;
    }
#ifdef PACKED_VALUE
    if (vp->var_value) {
	VARP_FREE(vp->var_value);
	vp->var_value = NULL;
    }
#endif    
    if (vp->order_map) {
	VARP_FREE(vp->order_map);
	vp->order_map = NULL;
    }
    
    if (vp->clause_map) {
	int i;
	for (i = 0; i < (int)vp->cnext; i++) {	
	    clause_t* cp = vp->clause_map[i];
	    clause_free(vp, cp);
	}
	VARP_FREE(vp->clause_map);
	vp->clause_map = NULL;
    }

    if (vp->undo) {
	VARP_FREE(vp->undo);
	vp->undo = NULL;
    }
    
    cleanup_allocator(&vp->var_allocator);
    cleanup_allocator(&vp->sym_allocator);
    cleanup_allocator(&vp->xref_allocator);
}

static void varp_dtor(ErlNifEnv* env, void* obj)
{
    (void) env;
#ifdef DEBUG_MEM
    printf("allocated memory before dtor = %ld\r\n",
	   varp_allocated);
#endif    
    cleanup((varp_t*) obj);
#ifdef DEBUG_MEM
    printf("allocated memory after dtor = %ld\r\n",
	   varp_allocated);
#endif
}

static ERL_NIF_TERM varp_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int grow   = DEFAULT_MAP_GROW;
    unsigned int vsize  = DEFAULT_MAP_SIZE;
    unsigned int csize  = DEFAULT_MAP_SIZE;
    unsigned int ssize;
    ERL_NIF_TERM t;
    ERL_NIF_TERM list = argv[0];
    ERL_NIF_TERM head, tail;
    int fifo = 0;
	
    while (enif_get_list_cell(env, list, &head, &tail)) {
	const ERL_NIF_TERM* elem;
	int arity;
	if (!enif_get_tuple(env, head, &arity, &elem) || (arity != 2))
	    return enif_make_badarg(env);
	if (elem[0] == ATOM(grow)) {
	    if (elem[1] == ATOM(default))
		grow = DEFAULT_MAP_GROW;
	    else if (!enif_get_uint(env, elem[1], &grow))
		return enif_make_badarg(env);
	    else if ((grow <= 0) || (grow >  MAX_MAP_EXPAND))
		return enif_make_badarg(env);
	}
	else if (elem[0] == ATOM(size)) {
	    if (elem[1] == ATOM(default))
		vsize = DEFAULT_MAP_SIZE;
	    else if (!enif_get_uint(env, elem[1], &vsize))
		return enif_make_badarg(env);
	    else if ((vsize < 2) || (vsize > MAX_MAP_SIZE))
		return enif_make_badarg(env);
	}
	else if (elem[0] == ATOM(fifo)) {
	    fifo = 1;
	}
	else if (elem[0] == ATOM(lifo)) {
	    fifo = 0;
	}
	else
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    
    if (!(vp = enif_alloc_resource(varp_res, sizeof(varp_t))))
	goto error;
    memset(vp, 0, sizeof(varp_t));

    vp->fifo = fifo;
    vp->vnext = 2;
    vp->vsize = vsize;
    vp->vnum  = 0;

    vp->grow = grow;
    if (!(vp->var_map = VARP_ALLOC(vsize*sizeof(variable_t**))))
	goto error;
#ifdef PACKED_VALUE
    if (!(vp->var_value = VARP_ALLOC(PACKED_BYTES(vsize)*sizeof(uint8_t))))
	goto error;
#endif
    ssize = 1;
    while(ssize < vsize) ssize *= 2;
    if (!(vp->sym_map = VARP_ALLOC(ssize*sizeof(symbol_t**))))
	goto error;
    memset(vp->sym_map, 0, ssize*sizeof(symbol_t**));
    vp->ssize = ssize;
    vp->snum = 0;
    
    if (!(vp->order_map = VARP_ALLOC(vsize*sizeof(int))))
	goto error;
    vp->cnext = 0;
    vp->csize = csize;
    vp->cnum = 0;
    vp->cpermanent = 0;
    vp->keep = 0;
    
    if (!(vp->clause_map = VARP_ALLOC(csize*sizeof(clause_t**))))
	goto error;

    if (init_allocator(&vp->var_allocator, sizeof(variable_t)) < 0)
	goto error;
    if (init_allocator(&vp->sym_allocator, sizeof(symbol_t)) < 0)
	goto error;
    if (init_allocator(&vp->xref_allocator, sizeof(xref_t)) < 0)
	goto error;    

    lqueue_init(&vp->q);
    undo_init(vp);

    vp->max_conflicting = MAX_CONFLICTING;
    vp->eval_counter = 0;
    vp->clause_eval_counter[0] = 0;    // overall counter
    vp->clause_eval_counter[1] = 0;    // not-used
    vp->clause_eval_counter[2] = 0;    // not used
    vp->clause_eval_counter[3] = 0;    // 2-clauses
    vp->clause_eval_counter[4] = 0;    // 3-clauses

    vp->order_map[0] = 0;
    init_variable(vp, &vp->undef, UNDEF, 0);
    vp->var_map[0] = &vp->undef;
    vp->order_map[1] = 1;
    init_variable(vp, &vp->constant, TRUE, 1);
    vp->var_map[1] = &vp->constant;
#ifdef LIT_INTEGER
    vp->ltrue = TRUE;
    vp->lfalse = FALSE;
#else
    vp->ltrue = &vp->constant.lit[LIT_POS];
    vp->lfalse = &vp->constant.lit[LIT_NEG];
#endif
    
    arc4_init(&vp->as);

    t = enif_make_resource(env,vp);
    enif_release_resource(vp);
    return t;

error:
    if (vp) {
	cleanup(vp);
	enif_release_resource(vp);
    }
    return enif_make_badarg(env);
}

// varc:add_variable(Vp:varc()) -> integer()
static ERL_NIF_TERM varp_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int vix;
    variable_t* var;
    int is_atom;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!get_boolean(env, argv[1], &is_atom))
	return enif_make_badarg(env);	
    
    if ((var = varp_alloc(&vp->var_allocator)) == NULL)
	return enif_make_badarg(env);

    vix = vp->vnext++;
    if (vp->vnext == vp->vsize) {
	unsigned int new_vsize = vp->vsize + vp->grow;
	void* ptr;

	if (!(ptr = VARP_REALLOC(vp->var_map, new_vsize*sizeof(variable_t*))))
	    return enif_make_badarg(env);
	vp->var_map = ptr;
	
	if (!(ptr = VARP_REALLOC(vp->order_map, new_vsize*sizeof(int))))
	    return enif_make_badarg(env);
	vp->order_map = ptr;
#ifdef PACKED_VALUE
	if (!(ptr = VARP_REALLOC(vp->var_value,
				 PACKED_BYTES(new_vsize)*sizeof(uint8_t))))
	    return enif_make_badarg(env);
	vp->var_value = ptr;
#endif
	vp->vsize = new_vsize;
    }
    vp->vnum++;
    vp->order_map[vix] = vix;
    init_variable(vp, var, UNDEF, vix);
    vp->var_map[vix] = var;
    if (is_atom) var->flags |= VAR_FLAG_ATOM;
    return enif_make_int(env, vix);
}

// varc:add_symbol(Vp:varc(),integer(),term()) -> ok | error
static ERL_NIF_TERM varp_add_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    ErlNifBinary bin;
    uint32_t hash;
    int hix;
    int is_term = 0;
    symbol_t* sp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);

    if (!enif_inspect_iolist_as_binary(env, argv[2], &bin)) {
	if (!enif_term_to_binary(env, argv[2], &bin))
	    return enif_make_badarg(env);
	is_term = 1;
    }

    hash = djb_hash(bin.data, bin.size);
    hix  = hash & (vp->ssize - 1);
    sp = vp->sym_map[hix];
    while(sp != NULL) {
	if ((sp->hash == hash) &&
	    (sp->size == bin.size) &&
	    (sp->is_term == is_term) &&
	    (memcmp(sp->data, bin.data, bin.size) == 0)) {
	    // already defined
	    if (is_term) enif_release_binary(&bin);
	    return ATOM(error);
	}
	sp = sp->next;
    }
    // not found allocate new
    if ((sp = varp_alloc(&vp->sym_allocator)) == NULL)
	return enif_make_badarg(env);
    sp->is_term = is_term;
    sp->hash = hash;
    sp->var  = var;    
    // copy term or binary
    if (is_term) {
	sp->data = VARP_ALLOC(bin.size);
	memcpy(sp->data, bin.data, bin.size);
	sp->size = bin.size;	
    }
    else {
	sp->data = VARP_ALLOC(bin.size+1);
	memcpy(sp->data, bin.data, bin.size);
	sp->data[bin.size] = '\0';
	sp->size = bin.size;
	if (var->strname == NULL)
	    var->strname = (char*) sp->data;
    }
    // link alias list
    sp->anext = var->names;
    var->names = sp;
    vp->snum++;
    
    if (vp->snum >= vp->ssize) { // rehash	
	unsigned int ssize1 = vp->ssize*2;
	int i;
	symbol_t** sym_map1 = VARP_ALLOC(ssize1*sizeof(symbol_t**));

	memset(sym_map1, 0, ssize1*sizeof(symbol_t**));
	for (i = 0; i < (int)vp->ssize; i++) {
	    symbol_t* sp1 = vp->sym_map[i];
	    while(sp1 != NULL) {
		symbol_t* spn = sp1->next;		
		int hjx = sp1->hash & (ssize1 - 1);
		sp1->next = sym_map1[hjx];
		sp1 = spn;
	    }
	    vp->sym_map[i] = NULL;
	}
	VARP_FREE(vp->sym_map);
	vp->sym_map = sym_map1;
	vp->ssize = ssize1;
	hix  = hash & (ssize1-1);  // hash index for new element
    }
    // link hash bucket list
    sp->next = vp->sym_map[hix];
    vp->sym_map[hix] = sp;

    return ATOM(ok);
}

// varc:get_variable_name(Vp:varc(),integer()) -> [term()].
static ERL_NIF_TERM varp_get_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    symbol_t* sp;
    ERL_NIF_TERM list;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);

    list = enif_make_list(env, 0);
    sp = var->names;
    while(sp != NULL) {
	ERL_NIF_TERM term;
	if (sp->is_term)
	    enif_binary_to_term(env,sp->data,sp->size,&term,0);
	else {
	    uint8_t* data = enif_make_new_binary(env, sp->size, &term);
	    memcpy(data, sp->data, sp->size);
	}
	list = enif_make_list_cell(env, term, list);
	sp = sp->anext;
    }
    return list;
}

// varc:find_variable(Vp:varc(),term()) -> false | integer().
static ERL_NIF_TERM varp_find_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);    
    varp_t* vp;
    ErlNifBinary bin;
    uint32_t hash;    
    int hix;
    int is_term = 0;
    symbol_t* sp;    
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    
    if (!enif_inspect_iolist_as_binary(env, argv[1], &bin)) {
	if (!enif_term_to_binary(env, argv[1], &bin))
	    return enif_make_badarg(env);
	is_term = 1;
    }
    hash = djb_hash(bin.data, bin.size);
    hix  = hash & (vp->ssize - 1);
    sp = vp->sym_map[hix];

    while(sp != NULL) {
	if ((sp->hash == hash) &&
	    (sp->size == bin.size) &&
	    (sp->is_term == is_term) &&
	    (memcmp(sp->data, bin.data, bin.size) == 0)) {
	    // found
	    if (is_term) enif_release_binary(&bin);
	    return enif_make_int(env, sp->var->vix);
	}
	sp = sp->next;
    } 
    if (is_term) enif_release_binary(&bin);
    return ATOM(false);
}

static ERL_NIF_TERM varp_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    for (i = 2; i < (int)vp->vnext; i++) {
	int vix = vp->order_map[i];
	if (!vis_bound(vp, vix))
	    return enif_make_tuple2(env,enif_make_int(env, i),
				    enif_make_int(env, vix));
    }
    return ATOM(false);
}

// next unbound variable in current sort order
static ERL_NIF_TERM varp_order_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    int skip;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &i) || (i < 1))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &skip) || (skip < 0))
	return enif_make_badarg(env);

    for (i=i+1; i < (int)vp->vnext; i++) {
	int vix = vp->order_map[i];
	if (!vis_bound(vp, vix)) {
	    if (!skip)
		return enif_make_tuple2(env,enif_make_int(env, i),
					enif_make_int(env, vix));
	    skip--;
	}
    }
    return ATOM(false);
}

// install variables as:
// bound-variables 0,1,...b  unbound-variables u....n
// return u (first unbound index)
//
static int order_reset(varp_t* vp)
{
    int i, u, b;

    vp->order_map[0] = 0;
    vp->var_map[0]->map_index = 0;
    vp->order_map[1] = 1;
    vp->var_map[1]->map_index = 1;
    b = 1;
    u = vp->vnext;

    for (i = 2; i < (int)vp->vnext; i++) {
	if (vis_bound(vp, i)) {
	    b++;
	    vp->order_map[b] = i;
	    vp->var_map[i]->map_index = b;
	}
	else {
	    u--;
	    vp->order_map[u] = i;
	    vp->var_map[i]->map_index = u;
	}
    }
    return u;
}


static void order_k_identity(varp_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i]->pkey[k] = i;
	vp->var_map[i]->nkey[k] = i;	
    }
}

static void order_k_random(varp_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	int v1 = arc4_random_uniform(&vp->as, 0x7fffffff);
	int v2 = arc4_random_uniform(&vp->as, 0x7fffffff);	
	vp->var_map[i]->pkey[k] = v1;
	vp->var_map[i]->nkey[k] = v2;
    }
}

static void order_k_undefined(varp_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i]->pkey[k] = 0;
	vp->var_map[i]->nkey[k] = 0;
    }
}

// scan through all variables and calculate the occur count, pkey[k]/nkey[k]
static void order_k_occur(varp_t* vp, int k)
{
    int i;
    
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i]->pkey[k] = 0;
	vp->var_map[i]->nkey[k] = 0;
    }

    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	int j;
	for (j = 0; j < (int)cp->size; j++) {
	    int x = index_l(cp->lit[j]);
	    if (x < 1)
		vp->var_map[-x]->nkey[k]++;
	    else if (x > 1)
		vp->var_map[x]->pkey[k]++;
	}
    }
}

// this is INSANE!!!
#if defined(_GNU_SOURCE)
#define QSORT_R(base,nmemb,size,compar,arg) \
    qsort_r((base),(nmemb),(size),(compar),(arg))
#define QSORT_R_ARGS(a,b,arg) (a, b, arg)
 
#elif defined(__APPLE__)
#define QSORT_R(base,nmemb,size,compar,arg) \
    qsort_r((base),(nmemb),(size),(arg),(compar))
#define QSORT_R_ARGS(a,b,arg) (arg, a, b)
#endif

static int cmpk(variable_t* ap, variable_t* bp, int k)
{
    int a = (ap->pkey[k] >= ap->nkey[k]) ? ap->pkey[k] : ap->nkey[k];
    int b = (bp->pkey[k] >= bp->nkey[k]) ? bp->pkey[k] : bp->nkey[k];
    return a - b;
}

static int cmp_keys QSORT_R_ARGS(const void* a, const void* b,void* arg)
{
    varp_t* vp = (varp_t*) arg;
    int k1 = vp->sort_key[0];
    int k2 = vp->sort_key[1];
    variable_t* ap = vp->var_map[*((int*)a)];
    variable_t* bp = vp->var_map[*((int*)b)];
    int r = 0;

    // k1=0 means key[k1] is undefined, k2=0 means key[k2] is undefined
    if (k1 > 0) {
	if ((r = cmpk(ap, bp, k1)) != 0)
	    return r;
    }
    else if (k1 < 0) {
	if ((r = cmpk(bp, ap, -k1)) != 0)
	    return r;
    }
    if (k2 > 0)
	r = cmpk(ap, bp, k2);
    else if (k2 < 0)
	r = cmpk(bp, ap, -k2);
    return r;
}

static ERL_NIF_TERM varp_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    (void) argc;
    varp_t* vp;
    int arg = 0;
    int u;
    int i;
    int k1, k2;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[3], &arg))
	return enif_make_badarg(env);

    if ((argv[1] == ATOM(random)) || (argv[2] == ATOM(random))) {
	if (!arg)
	    arc4_stir(&vp->as);
	else {
	    arc4_init(&vp->as);
	    arc4_add_random(&vp->as, (uint8_t*)&arg, sizeof(arg));
	}
    }

    // generate the sort keys 1 and 2
    for (i = 1; i < 3; i++) {
	int k = i;
	if (argv[i] == ATOM(identity))
	    order_k_identity(vp, k);
	else if (argv[i] == ATOM(undefined))
	    order_k_undefined(vp, k);	
	else if (argv[i] == ATOM(random))
	    order_k_random(vp, k);
	else if ((argv[i] == ATOM(occur)) || (argv[i] == ATOM(plus_occur))) {
	    order_k_occur(vp, k);
	}
	else if (argv[i] == ATOM(minus_occur)) {
	    order_k_occur(vp, k);
	    k = -k;
	}
	else
	    return enif_make_badarg(env);
	vp->sort_key[i-1] = k;
    }
    // install identity order
    u = order_reset(vp);
    // sort unbound variables according to sort_keys
    QSORT_R(vp->order_map+u, vp->vnext-u, sizeof(int), cmp_keys, vp);

    k1 = ABS(vp->sort_key[0]);
    k2 = ABS(vp->sort_key[1]);
    // update map_index of sorted variables also update the sign
    for (i = u; i < (int)vp->vnext; i++) {
	int v = vp->order_map[i];
	variable_t* var = vp->var_map[v];
	int r;

	var->map_index = i;
	if ((r = (var->pkey[k1] - var->nkey[k1])) == 0)
	    r = (var->pkey[k2] - var->nkey[k2]);
	if (r < 0)
	    vp->order_map[i] = -v;
    }
    return ATOM(ok);
}

// move the list of variables first among the unbound variables
// and keep the order of the other variables.
// this is done through by copy the various part into a new
// array.
static ERL_NIF_TERM varp_order_sort_first(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    (void) argc;
    varp_t* vp;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;
    int* map;
    unsigned int i, ui, mi;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    // validate list
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	lit_t xp;
	if (!vif_get_lit(env, vp, head, &xp))
	    return enif_make_badarg(env);
	if (is_constant_l(vp, xp))
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    if (!(map = VARP_ALLOC(vp->vsize*sizeof(int))))
	return enif_make_badarg(env);

    // clear moved mark
    for (i = 0; i < vp->vnext; i++)
	vp->var_map[i]->flags &= ~VAR_FLAG_MARK;

    map[0] = 0;
    vp->var_map[0]->flags |= VAR_FLAG_MARK;
    map[1] = 1;
    vp->var_map[1]->flags |= VAR_FLAG_MARK;
    mi = 2;
    // copy all bound variables
    while ((mi < vp->vnext) && vis_bound(vp, vp->order_map[mi])) {
	int x = vp->order_map[mi];
	vp->var_map[ABS(x)]->flags |= VAR_FLAG_MARK;
	map[mi++] = x;
    }
    ui = mi;  // save the position for the first unbound variabel
    // copy/move variables in the list (not already copied)
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	literal_t* lp;
	if (!vif_get_literal(env, vp, head, &lp))
	    return enif_make_badarg(env);	    
	if (!(lp->var->flags & VAR_FLAG_MARK)) { // not moved
	    lp->var->flags |= VAR_FLAG_MARK;     // mark as moved
	    lp->var->map_index = mi;
	    map[mi++] = index_ll(lp);
	}
	list = tail;
    }
    // move rest of the varaibles not already moved
    while(ui < vp->vnext) {
	int x = vp->order_map[ui];
	int xi = ABS(x);
	if (!(vp->var_map[xi]->flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[xi]->flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[xi]->map_index = mi;
	    map[mi++] = x;
	}
	ui++;
    }
    VARP_FREE(vp->order_map);
    vp->order_map = map;
    return ATOM(ok);
}

// move the list of variables last (REVERSED) among the unbound variables
// and keep the order of the other variables.
// this is done through by copy the various part into a new
// array.

static ERL_NIF_TERM varp_order_sort_last(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    (void) argc;
    varp_t* vp;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;
    int* map;
    unsigned int i, ui, mi;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    // validate list
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	lit_t xp;
	if (!vif_get_lit(env, vp, head, &xp))
	    return enif_make_badarg(env);
	if (is_constant_l(vp, xp)) // constant TRUE|FALSE
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    if (!(map = VARP_ALLOC(vp->vsize*sizeof(int))))
	return enif_make_badarg(env);

    // clear moved mark
    for (i = 0; i < vp->vnext; i++)
	vp->var_map[i]->flags &= ~VAR_FLAG_MARK;

    map[0] = 0;
    vp->var_map[0]->flags |= VAR_FLAG_MARK;
    map[1] = 1;
    vp->var_map[1]->flags |= VAR_FLAG_MARK;
    mi = 2;
    // copy all bound variables
    while ((mi < vp->vnext) && vis_bound(vp, vp->order_map[mi])) {
	int x = vp->order_map[mi];
	vp->var_map[ABS(x)]->flags |= VAR_FLAG_MARK;
	map[mi++] = x;
    }
    ui = mi;  // save the position for the first unbound variabel
    mi = vp->vnext;  // last position(+1)
    // copy/move variables in the list (not already copied)
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	literal_t* lp;
	if (!vif_get_literal(env, vp, head, &lp))
	    return enif_make_badarg(env);
	if (!(lp->var->flags & VAR_FLAG_MARK)) { // not moved
	    lp->var->flags |= VAR_FLAG_MARK;     // mark as moved
	    lp->var->map_index = --mi;
	    map[mi] = index_ll(lp);
	}
	list = tail;
    }

    mi = ui;
    // move rest of the varaibles not already moved
    while(ui < vp->vnext) {
	int x = vp->order_map[ui];
	int xi = ABS(x);
	if (!(vp->var_map[xi]->flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[xi]->flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[xi]->map_index = mi;
	    map[mi++] = x;
	}
	ui++;
    }
    VARP_FREE(vp->order_map);
    vp->order_map = map;
    return ATOM(ok);
}

//
// get(Vct,X) -> Value.
// value of a literal X
//
static ERL_NIF_TERM varp_get(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    literal_t* lp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);
    return enif_make_int(env, get_ll(vp, lp));
}

static ERL_NIF_TERM varp_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;    
    int k;
    variable_t* var;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &k))
	return enif_make_badarg(env);
    if ((k < 0) || (k > 2))
	return enif_make_badarg(env);
    return enif_make_int(env, var->nkey[k]);
}

// retrieve implication clause
// return {ClauseIndex, LiteralPosition, Level}
static ERL_NIF_TERM varp_implication_clause(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    variable_t* var;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return enif_make_tuple3(env,
			    enif_make_int(env, var->implication_clause),
			    enif_make_int(env, var->literal_pos),
			    enif_make_int(env, var->level));
}

static ERL_NIF_TERM varp_is_variable(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    return make_boolean(env, !is_constant_l(vp, xp));
}

// Get conflicting clause index and clear clause conflict flag!
static ERL_NIF_TERM varp_conflicting_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i, cix;
    clause_t* cp;
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &i) || (i < 0) || (i > vp->num_conflicting))
	return enif_make_badarg(env);
    if ((cix = vp->conflicting_clauses[i]) >= (int)vp->cnext)
	return enif_make_badarg(env);
    // maybe clear all conflicting flags in one call?
    cp = vp->clause_map[cix];
    cp->flags &= ~CLAUSE_FLAG_CONFLICT;
    return enif_make_int(env, cix);
}

static ERL_NIF_TERM varp_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    variable_t* var;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_variable(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return make_boolean(env, get_vv(vp, var) != UNDEF);
}

static ERL_NIF_TERM varp_is_equal(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp, yp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);
    return make_boolean(env, (xp == yp));
}

//
// Set variable value
//
static ERL_NIF_TERM varp_put(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp, yp;
    int x, y;
    varp_t* vp;
    int level = -1;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);
    if (argc == 4) {
	if (!enif_get_int(env, argv[3], &level) || (level < 0) ||
	    (level >= (int)vp->unum))
	    return enif_make_badarg(env);
    }
    if (level < 0) level = vp->level;
    y = get_l(vp, yp);
    if (!is_constant(y))
        return enif_make_badarg(env);
    x = get_l(vp, xp);
    if (!is_constant(x)) {
	put_literal(vp, xp, y, -1, -1, level);
    }
    else if (x != y)
	return ATOM(false);
    return ATOM(true);
}

// insert sort literal level 'l' into la
// while keeping track on position 'p' and literal index 'v'
void insert_sort3(int v, int l, int p, int va[3], int la[3], int pa[3])
{
    if (l >= la[0]) {
	la[2] = la[1]; la[1] = la[0]; la[0] = l;
	pa[2] = pa[1]; pa[1] = pa[0]; pa[0] = p;
	va[2] = va[1]; va[1] = va[0]; va[0] = v;
    }
    else if (l >= la[1]) {
	la[2] = la[1]; la[1] = l;
	pa[2] = pa[1]; pa[1] = p;
	va[2] = va[1]; va[1] = v;
    }
    else if (l >= la[2]) {
	la[2] = l;
	pa[2] = p;
	va[2] = v;
    }
}

// (lp0,level0) track the literal that is bounded
// on the latest level, (lp1,level1) the next highest after
// (lp0,level0)
// setup TWL structure for a clause

static int watch_clause(varp_t* vp, clause_t* cp)
{
    int va[3], la[3], pa[3];
    long p;
    int dead = 0;
    int nfalse = 0;
    int lev;
    
    la[0] = la[1] = la[2] = -1;
    pa[0] = pa[1] = pa[2] = -1;

    for (p = 1; p < (int)cp->size; p++) {
	lit_t lp = cp->lit[p];
	switch(lit_value(vp,lp)) {
	case TRUE:
	    dead = 1;
	    lev = var_l(vp,lp)->level;
	    break;
	case FALSE:
	    nfalse++;
	    lev = var_l(vp,lp)->level;
	    break;
	case UNDEF:
	default:
	    lev = INT_MAX;
	    break;
	}
	insert_sort3(index_l(lp),lev,p,va,la,pa);
    }

    DBG("la[0]=%d,la[1]=%d,la[2]=%d,"
	"va[0]=%d,va[1]=%d,va[2]=%d,"
	"pa[0]=%d,pa[1]=%d,pa[2]=%d\r\n",
	la[0], la[1], la[2],
	va[0], va[1], va[2],
	pa[0], pa[1], pa[2]);

    if ((pa[0] < 0) || (pa[1] < 0)) {
	printf("Could not set TWL\r\n");
	return -1;
    }

    // setup watch
    set_wlink(&cp->wl[0], pa[1], l2ll(vp, cp->lit[pa[1]]));
    set_wlink(&cp->wl[1], pa[0], l2ll(vp, cp->lit[pa[0]]));
    
    if ((la[0] == INT_MAX) && (la[1] != INT_MAX)) {
	if (!dead) {
	    // printf("Set UNIT\r\n");
	    put_literal(vp, cp->lit[pa[0]], TRUE, pa[0], cp->cix, -1);
	}
	return 1;
    }
    if (nfalse == (int)(cp->size-1)) // currently in conflict!
	return 0;
    return 1;
}

//
// Substitute one literal for an other
// subst(Vp, X, Y)   apply [X/Y]
// Y is removed and replaced by X
//
//  [X/Y]    (A Y B)  =>  (A X B)
//  [!X/Y]   (A Y B)  =>  (A !X B)
//  [X/!Y]   (A Y B)  =>  (A !X B)
//  [!X/!Y]  (A Y B)  =>  (A X B)
//
//  [X/Y]    (A X Y B)  =>  (A X X B)    => (A X f B)
//  [!X/Y]   (A X Y B)  =>  (A X !X B)   => (A X t B)
//  [X/!Y]   (A X Y B)  =>  (A X !X B)   => (A X t B)
//  [!X/!Y]  (A X Y B)  =>  (A X X B)    => (A X f B)
//
//

static void subst(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* xp = l2ll(vp, xl);
    literal_t* yp = l2ll(vp, yl);
    variable_t* x = xp->var;
    variable_t* y = yp->var;
    xref_t** xpp  = &x->xfirst;
    xref_t* yptr = y->xfirst;

    assert (yp != xp);
    assert(get_vv(vp, y) == UNDEF);

#if LOG_ASSIGN_ATOM
    if (y->flags & VAR_FLAG_ATOM) {
	printf("PERMANENT(ATOM) %s -> %s\r\n",
	       format_literal(vp, yp),
	       format_literal(vp, xp));
    }
#endif
    // reset y xref
    y->xfirst = NULL;
    y->xlast  = &y->xfirst;

    // scan and rewrite all y's into x's
    while(yptr) {
	xref_t* xptr = *xpp;

	if ((xptr==NULL) || (yptr->cix < xptr->cix)) { // Y only
	    xref_t* yptr1 = yptr->next;
	    clause_t* cp = vp->clause_map[yptr->cix];
	    lit_t yyl = cp->lit[yptr->p];
	    int rewatch = 0;

	    // check if Y was TWL then update
	    if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
		unwatch_clause(vp, cp);
		rewatch = 1;
	    }
	    
	    if (yl == yyl)  // same sign as x
		cp->lit[yptr->p] = xl;
	    else
		cp->lit[yptr->p] = neg_l(xl);

	    if (rewatch) {
		int r = watch_clause(vp, cp);
		assert(r > 0);		
	    }
	    
	    *xpp = yptr;
	    yptr->next = xptr;
	    xpp = &(yptr->next);
	    yptr = yptr1;
	}
	else if (yptr->cix == xptr->cix) { // X and Y case
	    xref_t* yptr1 = yptr->next;
	    clause_t* cp = vp->clause_map[yptr->cix];
	    lit_t yyl = cp->lit[yptr->p];
	    lit_t xxl = cp->lit[xptr->p];
	    int rewatch = 0;
	
	    // check if Y was TWL then update
	    if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
		unwatch_clause(vp, cp);
		rewatch = 1;
	    }

	    // ((a=b)&&(c!=d))||((a!=b)&&(c=d)) -> !((a=b)=(c=d))
	    if ((yl == yyl) == (xl == xxl))
		cp->lit[yptr->p] = VARP_FALSE(vp);
	    else {
		cp->lit[yptr->p] = VARP_TRUE(vp);
		cp->flags |= CLAUSE_FLAG_DEAD;
		rewatch = 0;
	    }

	    if (rewatch) {
		int r = watch_clause(vp, cp);
		assert(r > 0);
	    }
	    varp_free(&vp->xref_allocator, yptr);
	    yptr = yptr1;
	}
	else { // X only
	    xpp = &(xptr->next);
	}
    }

    // all the way and update xlast just in case
    while(*xpp != NULL) {
	xref_t* xptr = *xpp;	
	xpp = &(xptr->next);
    }
    // the new last x
    x->xlast = xpp;
    
    // mark Y as bound (to X)
    set_vv(vp, y, BOUND);
    if (is_neg_l(yl))
	y->bound = l2ll(vp, neg_l(xl));
    else
	y->bound = xp;
    vp->num_bound++;    
}

static ERL_NIF_TERM varp_subst(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp, yp;
    int x, y;
    varp_t* vp;
    variable_t* xv;
    variable_t* yv;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);

    y = get_l(vp, yp);
    if (is_constant(y)) return enif_make_badarg(env);

    x = get_l(vp, xp);
    if (is_constant(x)) return enif_make_badarg(env);

    xv = var_l(vp, xp);
    yv = var_l(vp, yp);

    if (xv != yv) {
	if (!(xv->flags & VAR_FLAG_ATOM) && (yv->flags & VAR_FLAG_ATOM))
	    subst(vp, yp, xp);
	else
	    subst(vp, xp, yp);
    }
    return ATOM(true);
}


static ERL_NIF_TERM varp_set_level(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int level;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &level))
	return enif_make_badarg(env);
    set_level(vp, level);
    return ATOM(true);
}

//
// Undo bindings on a level
//
static ERL_NIF_TERM varp_undo_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level < 0))
	return enif_make_badarg(env);
    if (level < (int)vp->unum)
	undo_level(vp, level);
    return ATOM(ok);
}

//
// keep bindings on a level remove undo information
//
static ERL_NIF_TERM varp_keep_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level < 0))
	return enif_make_badarg(env);
    if (level < (int)vp->unum)
	keep_level(vp, level);
    return ATOM(ok);
}

//
// move bindings from one level to an other
//
static ERL_NIF_TERM varp_move_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int src, dst;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &src) ||
	(src < 0) || (src >= (int)vp->unum))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &dst) ||
	(dst < 0) || (src >= (int)vp->unum))
	return enif_make_badarg(env);

    if (src != dst) {
	// dst should be less to make sense - but goahead anyway!
	if (dst > src) printf("warning move_level to higher level!\r\n");
	move_level(vp, src, dst);
    }
    return ATOM(ok);
}

#ifdef DEBUG
#define PRINT_LIT_ARRAY(msg,lit,size) print_lit_array((msg),(lit),(size))
#define PRINT_CLAUSE(vp,msg,cp) print_clause((vp),(msg),(cp))
#else
#define PRINT_LIT_ARRAY(msg,lit,size)
#define PRINT_CLAUSE(vp,msg,cp)
#endif

#ifdef DEBUG
static void print_lit_array(char* label, lit_t* lit, size_t size)
{
    if (size == 0)
	printf("%s={}", label);
    else {
	unsigned k;
	printf("%s={%d", label, index_l(lit[0]));
	for (k=1; k<size; k++)
	    printf(",%d",index_l(lit[k]));
	printf("}\r\n");
    }
}

static void print_clause(varp_t* vp, char* label, clause_t* cp)
{
    unsigned k;
    printf("%s id=%d,[%ld:%ld] {%d/%d",
	   label, cp->cix, cp->wl[0].p, cp->wl[1].p,
	   index_l(cp->lit[0]),lit_value(vp,cp->lit[0]));
    for (k=1; k<cp->size; k++)
	printf(",%d/%d",index_l(cp->lit[k]),lit_value(vp,cp->lit[k]));
    printf("}\r\n");
}
#endif

// eval clause
// return 0 non conclusive
// return -1 conflict
//
static int eval_clause(varp_t* vp, clause_t* cp, int wi, wlink_t** wlp)
{
    wlink_t* wl0 = &cp->wl[0];
    wlink_t* wl1 = &cp->wl[1];
    int wp0 = wl0->p;
    int wp1 = wl1->p;
    long p;
    int lw;

    PRINT_CLAUSE(vp,"ev: ",cp);

    if ((wp0 < 0) || (wp1 < 0)) // clause is dead?
	return 0;

    if (wi==0) {  // watch point 0
	if ((lw = get_l(vp, cp->lit[wp1])) == TRUE)
	    return 0;
	vp->clause_eval_counter[0]++;
	if (cp->size <= 4) vp->clause_eval_counter[cp->size]++;
	
	// find a new watch point
	for (p = 1; p < (int)cp->size; p++) {
	    int lv = get_l(vp, cp->lit[p]);
	    if (lv != FALSE) {  // TRUE | UNDEF
		if (p != wp1) {  // skip other watch point
		    if (lv == TRUE)
			return 0;
		    break;  // new watch point found
		}
	    }
	}
	DBG("  wp0: %s %d=>%ld\r\n", format_lit(vp, cp->lit[wp0]), wp0, p);
	if (p == (int)cp->size) {  // no new watch point found
	    if (lw == FALSE)
		return -1; // all are false
	    else {
		put_literal(vp, cp->lit[wp1], TRUE, wp1, cp->cix, -1);
	    }
	}
	else {  // move watch
	    literal_t* mp = l2ll(vp, cp->lit[p]);
	    *wlp = wl0->next;
	    set_wlink(wl0, p, mp);
	}
    }
    else { // watch point 1
	if ((lw = get_l(vp, cp->lit[wp0])) == TRUE)
	    return 0;
	vp->clause_eval_counter[0]++;
	if (cp->size <= 4) vp->clause_eval_counter[cp->size]++;	

	// find a new watch point
	for (p = 1; p < (int)cp->size; p++) {
	    int lv = get_l(vp, cp->lit[p]);	    
	    if (lv != FALSE) {  // TRUE | UNDEF
		if (p != wp0) {  // skip other watch point
		    if (lv == TRUE)
			return 0;
		    break;  // new watch point found
		}
	    }
	}
	DBG("  wp1: %s %d=>%ld\r\n", format_lit(vp, cp->lit[wp1]), wp1, p);
	if (p == (int)cp->size) {  // no new watch point found
	    if (lw == FALSE) // contradiction
		return -1;
	    else {
		put_literal(vp, cp->lit[wp0], TRUE, wp0, cp->cix, -1);
	    }
	}
	else {  // move watch
	    literal_t* mp = l2ll(vp, cp->lit[p]);
	    *wlp = wl1->next;
	    set_wlink(wl1, p, mp);
	}
    }
    return 0;
}


// eval:
//  return false  when conflict is found
//         true   when no conflict is found
//
static ERL_NIF_TERM varp_eval(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;
    int ci = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    vp->eval_counter++;
    vp->num_conflicting = 0;

    DBG("EVAL %ld\r\n", vp->eval_counter);

    while((lp = lqueue_get(vp)) != NULL) {
	wlink_t** wlp = &lp->wlist;
	wlink_t*  wl;
	
	while((wl = *wlp) != NULL) {
	    clause_t* cp = clause_pointer(wl);
	    if (!(cp->flags & (CLAUSE_FLAG_CONFLICT|CLAUSE_FLAG_DEAD))) {
		if (eval_clause(vp, cp, wlink_index(wl), wlp) < 0) {
		    if (vp->max_conflicting == 1) {
			vp->conflicting_clauses[ci++] = cp->cix;
			goto done_conflict;
		    }
		    else if (ci < vp->max_conflicting) {
			vp->conflicting_clauses[ci++] = cp->cix;
			cp->flags |= CLAUSE_FLAG_CONFLICT;
		    }
		    else
			goto done_conflict;
		}
	    }
	    if (*wlp == wl)
		wlp = &wl->next;
	}
    }
done_conflict:
    if (ci) {
	lqueue_clear(&vp->q);
	vp->num_conflicting = ci;
	DBG("num conflicts = %d\n", ci);
	return ATOM(false);
    }
    return ATOM(true);
}


// get information
static ERL_NIF_TERM varp_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (argv[1] == ATOM(max_clause_length)) {
	return enif_make_int(env, MAX_CLAUSE_LENGTH);
    }
    else if (argv[1] == ATOM(max_conflicting)) {
	return enif_make_int(env, vp->max_conflicting);
    }
    else if (argv[1] == ATOM(num_conflicting)) {
	return enif_make_int(env, vp->num_conflicting);
    } 
    else if (argv[1] == ATOM(number_of_variables)) {
	return enif_make_int(env, vp->vnum);
    }
    else if (argv[1] == ATOM(number_of_clauses)) {
	return enif_make_int(env, vp->cnum);
    }
    else if (argv[1] == ATOM(number_of_learned_clauses)) {
	return enif_make_int(env, vp->cnext - vp->cpermanent);
    }    
    else if (argv[1] == ATOM(number_of_bound_variables)) {
	return enif_make_int(env, vp->num_bound);
    }
    else if (argv[1] == ATOM(number_of_unbound_variables)) {
	return enif_make_int(env, vp->vnum - vp->num_bound);
    }
    else if (argv[1] == ATOM(clause_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter[0]);
    }
    else if (argv[1] == ATOM(clause2_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter[3]);
    }
    else if (argv[1] == ATOM(clause3_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter[4]);
    }        
    else if (argv[1] == ATOM(eval_counter)) {
	return enif_make_uint64(env, vp->eval_counter);
    }
    else if (argv[1] == ATOM(undo_stack_size)) {
	return enif_make_uint64(env, vp->stack_size);
    }
    else if (argv[1] == ATOM(value_stack_size)) {
	return enif_make_uint64(env, vp->stack_size);
    }
    else if (argv[1] == ATOM(grow)) {
	return enif_make_uint(env, vp->grow);
    }
    else if (argv[1] == ATOM(size)) {
	return enif_make_uint(env, vp->vsize);
    }
    else if (argv[1] == ATOM(permanent)) {
	return enif_make_uint(env, vp->cpermanent);
    }
    else if (argv[1] == ATOM(keep)) {
	return enif_make_uint(env, vp->keep);
    }
    else if (argv[1] == ATOM(level)) {
	return enif_make_uint(env, vp->level);
    }        
    return enif_make_badarg(env);
}


// set config
// set permanent - number of permanent clauses
//   conflict clauses use the rest
//
static ERL_NIF_TERM varp_config(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (argv[1] == ATOM(permanent)) {
	unsigned int value;
	if (!enif_get_uint(env, argv[2], &value))
	    return enif_make_badarg(env);
	if (value == 0)
	    vp->cpermanent = vp->cnext;
	else
	    vp->cpermanent = value;
	return ATOM(ok);
    }
    if (argv[1] == ATOM(keep)) {
	unsigned int value;
	if (!enif_get_uint(env, argv[2], &value))
	    return enif_make_badarg(env);
	vp->keep = value;
	return ATOM(ok);
    }
    if (argv[1] == ATOM(max_conflicting)) {
	int value;
	if (!enif_get_int(env, argv[2], &value) || (value < 0))
	    return enif_make_badarg(env);
	if ((value == 0) || (value > MAX_CONFLICTING))
	    vp->max_conflicting = MAX_CONFLICTING;
	else
	    vp->max_conflicting = value;
	return ATOM(ok);
    }
    return enif_make_badarg(env);
}

//
// add clause (and normalize, remove literals)
//
static int cmp_rev_abs_lit QSORT_R_ARGS(const void* ap,const void* bp,void* arg)
{
    (void) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);

    if (a == b) return 0;
#ifdef LIT_INTEGER
    if (ABS(a) == ABS(b)) {
	if (a < 0) return -1;
	return 1;
    }
    return ABS(b) - ABS(a);
#else
    if (a->var == b->var) {
	if (a->sign < 0) return -1;
	else return 1;
    }
    return b->var->vix - a->var->vix;
#endif
}

#ifdef USE_CLAUSE_SHUFFLE

typedef struct
{
    lit_t lit;
    int32_t key;
} shuffle_key_t;

static int cmp_shuffle QSORT_R_ARGS(const void* a, const void* b,void* arg)
{
    UNUSED(arg);
    return ((shuffle_key_t*)a)->key - ((shuffle_key_t*)b)->key;
}

#endif

//
// add a clause to the system and normalise contents
// first SORT (reversed) the literals according to abs(lit[i]) then lit[i]
// this means that high numbered literals comes first and lastly
// the constants will appear, FALSE last
//   x6 x3 F x3 x2 T x5 x3 F x1 -x3 => x6 x5 x3 x3 x3 -x3 x2 T F F
// after sort, normalise start with to remove the FALSE literals
//   x6 x5 x3 x3 x3 -x3 x2 T F F => x6 x5 x3 x3 x3 -x3 x2 T
// TRUE literals are removed and remembered (Tc=1)
//   x6 x5 x3 x3 x3 -x3 x2 T => x6 x5 x3 x3 x3 -x3 x2
// duplicate elements are removed / reduced  (for XOR even number are removed)
//   x6 x5 x3 x3 x3 -x3 x2 => x6 x5 x3 -x3 x2
// negated pairs are removed and Tc is updated
//   x6 x5 x2  ( Tc=2 )
// check Tc
//   OR:
//      x6 x5 x2 T
//
// OR:
//   X (Tc=0,Fc>0) => X -1
//   X (Tc>0) => X => X  1
//

// la[0] >= la[1] >= la[2]


static void add_xref(varp_t* vp, clause_t* cp, long p)
{
    variable_t* var = var_l(vp, cp->lit[p]);
    xref_t*    xp = varp_alloc(&vp->xref_allocator);

    xp->cix  = cp->cix;
    xp->p    = p;
    xp->next = NULL;

    *var->xlast = xp;
    var->xlast = &(xp->next);
}

static void del_xref(varp_t* vp, clause_t* cp, long p)
{
    variable_t* var = var_l(vp, cp->lit[p]);
    xref_t* xp;
    xref_t** xpp = &var->xfirst;
    // locate and remove xref link

    while((xp = *xpp)) {
	if ((xp->cix == cp->cix) && (xp->p == p)) {
	    if (var->xlast == &xp->next)
		var->xlast = xpp;
	    *xpp = xp->next;
	    varp_free(&vp->xref_allocator, xp);
	    return;
	}
	xpp = &(xp->next);
    }
    DBG("xref not found for clause %d pos = %ld\r\n", cp->cix, p);
}


static ERL_NIF_TERM add_clause_array(ErlNifEnv* env, varp_t* vp,
				     lit_t* lit, size_t size)
{
    clause_t* cp;
    int cix;
    unsigned i;
    long p;
    unsigned Tc=0, Fc=0;

    PRINT_LIT_ARRAY("   src", lit, size);

    // replace level 0 variables with constants
    for (i = 1; i < size; i++) {
	if ((lit[i] == VARP_TRUE(vp)) || (lit[i] == VARP_FALSE(vp)))
	    ;
	else {
	    literal_t* lp = l2ll(vp, lit[i]);
	    if (lp->var->level == 0) {
		switch(get_literal_value(vp,lp)) {
		case TRUE: lit[i] = VARP_TRUE(vp); break;
		case FALSE: lit[i] = VARP_FALSE(vp); break;
		default: break;
		}
	    }
	}
    }
    PRINT_LIT_ARRAY("   filt0", lit, size);
    
    // sort all literals by absolute value
    QSORT_R(lit+1, size-1, sizeof(lit_t), cmp_rev_abs_lit, vp);

    PRINT_LIT_ARRAY(" sorted", lit, size);

    // remove TRUE literals
    i = size-1;
    while((i > 0) && (lit[i] == VARP_TRUE(vp))) { i--; size--; Tc++; }
    // PRINT_LIT_ARRAY("  del-T", lit, size);

    // remove FALSE literals
    while((i > 0) && (lit[i] == VARP_FALSE(vp))) { i--; size--; Fc++; }
    // PRINT_LIT_ARRAY("  del-F", lit, size);

    // remove duplicates
    {
	unsigned u=1,v=1,w=1;
	while(v < size) {
	    while((w < size) && (lit[v] == lit[w])) w++;
	    if ((u > 1) && (lit[u-1] == neg_l(lit[v]))) {
		u--;
		Tc++;
	    }
	    else
		lit[u++] = lit[v];
	    v = w;
	}
	size = u;
    }

    // PRINT_LIT_ARRAY("del-dup", lit, size);
    if (size == 1) {
	if ((Tc==0) && (Fc>0))
	    lit[size++] = VARP_FALSE(vp);
    }
    if (Tc>0) // add the T constant to the gate
	lit[size++] = VARP_TRUE(vp);

    PRINT_LIT_ARRAY("   dest", lit, size);

    // set watch points

    if (lit[size-1] == VARP_TRUE(vp))
	return ATOM(true);

    if (size == 2) {  // unit
	if (lit[1] == VARP_FALSE(vp))
	    return ATOM(false);
	put_literal(vp, lit[1], VARP_TRUE(vp), -1, -1, 0);
	// report as unit clause!?
	return ATOM(true);
    }
    
#ifdef USE_CLAUSE_FIND
    // check if clause is already installed!!!
    if ((cix = clause_find(vp, lit, size)) >= 0) {
	printf("Found clause %d size=%ld\r\n", cix, size-1);
	return enif_make_tuple2(env, ATOM(true), enif_make_int(env, cix));
    }
#endif

    // shuffle literals - possibly make watch literal chains shorter?
#ifdef USE_CLAUSE_SHUFFLE
    {
	shuffle_key_t skey[size];
	for (i = 1; i < size; i++) {
	    skey[i].lit = lit[i];
	    skey[i].key = arc4_random(&vp->as);
	}
	QSORT_R(skey+1, size-1, sizeof(shuffle_key_t), cmp_shuffle, 0);
	for (i = 1; i < size; i++)
	    lit[i] = skey[i].lit;
    }
    PRINT_LIT_ARRAY("shuffle", lit, size);
#endif
    

    if ((cp = clause_alloc(vp, size)) == NULL)
	goto error;
    if ((cix = clause_insert(vp, cp)) < 0)
	goto error;

    memcpy(cp->lit, lit, sizeof(lit_t)*size);

    for (p = 1; p < (int)size; p++)
	add_xref(vp, cp, p);
    
    switch (watch_clause(vp, cp)) {
    case -1:
	goto error;
    case 0:
	return enif_make_tuple2(env, ATOM(false), enif_make_int(env, cix));
    case 1:
	return enif_make_tuple2(env, ATOM(true), enif_make_int(env, cix));
    default:
	goto error;
    }

error:
    if (cp != NULL) clause_free(vp, cp);
    return enif_make_badarg(env);
}

//
// add_clause(vp, x1, ..., xn)
// add_clause(vp, [x1, ..., xn])
//
static ERL_NIF_TERM varp_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    varp_t* vp;
    int size = 0;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (argc == 2) {   // argv[1] is a list of literals
	ERL_NIF_TERM list = argv[1];
	ERL_NIF_TERM head, tail;

	while(enif_get_list_cell(env, list, &head, &tail)) {
	    size++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);	
	else {
	    lit_t literals[size+1];
	    lit_t* lpp = &literals[1];

	    literals[0] = VARP_TRUE(vp);  // dummy FIXME remove this
	    list = argv[1];
	    while(enif_get_list_cell(env, list, &head, &tail)) {
		if (!vif_get_lit(env, vp, head, lpp))
		    return enif_make_badarg(env);
		lpp++;
		list = tail;
	    }
	    return add_clause_array(env, vp, literals, size+1);
	}
    }
    else if ((size = (argc-1)) > 0) {  // size = 2,3,4,5,6
	lit_t literals[size+1];
	lit_t* lpp = &literals[1];
	int j;

	literals[0] = VARP_TRUE(vp);  // dummy FIXME remove this	
	for (j = 1; j < argc; j++) {
	    if (!vif_get_lit(env, vp, argv[j], lpp))
		return enif_make_badarg(env);
	    lpp++;
	}
	return add_clause_array(env, vp, literals, size+1);
    }
    return enif_make_badarg(env);    
}

// may only delete clauses on level 0!
static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    clause_t* cp;
    long p;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &i) || (i < 0) || (i >= (int)vp->cnext))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_make_badarg(env);
    cp = vp->clause_map[i];
    vp->clause_map[i] = NULL;

    unwatch_clause(vp, cp);      // remove watched literals

    // remove xref
    for (p = 1; p < (int)cp->size; p++)
	del_xref(vp, cp, p);
    
    clause_free(vp, cp);
    // fixme now we leave a hole, maybe garbage collect?
#if 0
    {
	int k;
	// fixme check if permanent is set the !
	k = (int)vp->cnext - 1;  // index of last element
	if (i < k) {  // swap in last element
	    vp->clause_map[i] = vp->clause_map[k];
	    vp->clause_map[i]->cix = i;
	}
	vp->cnext--;
    }
#endif
    return ATOM(ok);
}

// del unused clauses is used for garbage collection and may
// only be called during a restart. i.e no bindings may be present
// so level must be = 0
// cmp_use sort according to falling eval_counter stamp
// so that thew newest and recently used clauses are sorted
// first.
//
static int cmp_stamp QSORT_R_ARGS(const void* a, const void* b,void* arg)
{
    UNUSED(arg);
    clause_t* ca = *(clause_t**)a;
    clause_t* cb = *(clause_t**)b;
    if (cb->stamp < ca->stamp) return -1;
    else if (cb->stamp > ca->stamp) return 1;
    return 0;
}

static ERL_NIF_TERM varp_del_unused_clauses(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    size_t k;
    int i;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_make_badarg(env);
    if ((vp->keep == 0) || (vp->cpermanent == 0))
	return ATOM(ok);

    // sort the upper part of clause, the conflict clause
    // k elements
    k = vp->cnext - vp->cpermanent; // number of conflict clauses
    
    QSORT_R(vp->clause_map+vp->cpermanent, k, sizeof(clause_t*), cmp_stamp, vp);

    // update all cix after sort
    for (i = vp->cpermanent; i < (int)vp->cnext; i++)
	vp->clause_map[i]->cix = i;

    // remove all clauses from vp->cpermanent+vp->keep
    for (i = vp->cpermanent+vp->keep; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	unwatch_clause(vp, cp);      // remove watched literals
	clause_free(vp, cp);
    }
    vp->cnext = vp->cpermanent+vp->keep;
    return ATOM(ok);
}

//
// get_clause(vp,ClauseIndex::integer(),SkipLiteral::literl(),Raw::boolean())->
//  {Type, Clause}
//
static ERL_NIF_TERM varp_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varp_t* vp;
    unsigned int cix;
    ERL_NIF_TERM list;
    int i;
    int raw;
    literal_t* lp;
    int skip_lit;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix) || (cix >= vp->cnext))
	return enif_make_badarg(env);
    if (argv[2] == ATOM(undefined))
	skip_lit = 0;
    else if (!vif_get_literal(env, vp, argv[2], &lp))
	return enif_make_badarg(env);
    else
	skip_lit = index_ll(lp);
    if (!get_boolean(env, argv[3], &raw))
	return enif_make_badarg(env);

    cp = vp->clause_map[cix];
    list = enif_make_list(env, 0);
    for (i = cp->size-1; i >= 1; i--) {
	int lit = index_l(cp->lit[i]);
	ERL_NIF_TERM elem;
	if (lit != skip_lit) {
	    if (raw) {
		elem = enif_make_int(env, lit);
		list = enif_make_list_cell(env, elem, list);	    
	    }
	    else {
		literal_t* lp = l2ll(vp, cp->lit[i]);
		if (lp->var->level <= 0) {  // constant level
		    switch(get_ll(vp,lp)) {
		    case TRUE:
			list = enif_make_list(env, 0);
			goto done;
		    case FALSE:  // skip FALSE constants
			break;
		    case UNDEF:
		    default:
			elem = enif_make_int(env, lit);
			list = enif_make_list_cell(env, elem, list);
			break;
		    }
		}
		else {
		    elem = enif_make_int(env, lit);
		    list = enif_make_list_cell(env, elem, list);		
		}
	    }
	}
    }
done:
    return list;
}

static ERL_NIF_TERM varp_get_clause_flags(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varp_t* vp;
    unsigned int cix;
    ERL_NIF_TERM list;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    if (cix >= vp->cnext)
	return enif_make_badarg(env);
    
    cp = vp->clause_map[cix];
    list = enif_make_list(env, 0);
    if (cp->flags & CLAUSE_FLAG_INQUEUE)
	list = enif_make_list_cell(env, ATOM(inqueue), list);
    if ((cp->flags & CLAUSE_FLAG_DEAD) ||
	((cp->wl[0].p == -1) || (cp->wl[1].p == -1)))
	list = enif_make_list_cell(env, ATOM(dead), list);
    else {
	ERL_NIF_TERM w1;
	ERL_NIF_TERM w2;

	w1 = enif_make_tuple2(env,
			      enif_make_long(env,cp->wl[0].p),
			      enif_make_long(env,cp->wl[1].p));
	w2 =  enif_make_tuple2(env, ATOM(watch), w1);
	list = enif_make_list_cell(env, w2, list);
    }
    return list;
}

static ERL_NIF_TERM varp_use_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varp_t* vp;
    int i;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &i) || (i < 0) || (i >= (int)vp->cnext))
	return enif_make_badarg(env);
    cp = vp->clause_map[i];
    if (cp->cix >= (int)vp->cpermanent)
	cp->stamp = vp->eval_counter;
    return ATOM(ok);
}

static ERL_NIF_TERM varp_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM list;
    lit_t l;
    literal_t* lp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_l(env, vp, argv[1], &l))
	return enif_make_badarg(env);

    lp = l2ll(vp, l);
    list = enif_make_list(env, 0);

    if (argv[2] == ATOM(watch)) {
	wlink_t* wl = lp->wlist;
	while(wl != NULL) {
	    clause_t* cp = clause_pointer(wl);
	    ERL_NIF_TERM elem = enif_make_uint(env, cp->cix);
	    list = enif_make_list_cell(env, elem, list);
	    wl = wl->next;
	}
    }
    else if (argv[2] == ATOM(literal)) {
	variable_t* var = lp->var;
	xref_t* xp = var->xfirst;
	while(xp) {
	    clause_t* cp = vp->clause_map[xp->cix];
	    if (l == cp->lit[xp->p]) {
		ERL_NIF_TERM elem = enif_make_uint(env, xp->cix);
		list = enif_make_list_cell(env, elem, list);
	    }
	    xp = xp->next;
	}
    }
    else if (argv[2] == ATOM(variable)) {
	variable_t* var = lp->var;
	xref_t* xp;

	xp = var->xfirst;
	while(xp) {
	    ERL_NIF_TERM elem = enif_make_uint(env, xp->cix);
	    list = enif_make_list_cell(env, elem, list);
	    xp = xp->next;
	}
    }
    else
	return enif_make_badarg(env);
    return list;
}

// REMOVE?
// Get index to the first literal in queue
static ERL_NIF_TERM varp_get_queue_first(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);    
    if ((lp = vp->q.head) != NULL)
	return make_literal(env, lp);
    return ATOM(false);
}

// REMOVE?
static ERL_NIF_TERM varp_get_queue_next(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);
    if (vp->q.head == NULL)
	return ATOM(false);
    if (lp->qlink != NULL) 
	return make_literal(env, lp->qlink);
    return ATOM(false);
}

static ERL_NIF_TERM make_clause_info(ErlNifEnv* env, varp_t* vp, variable_t* v)
{
    return enif_make_tuple4(env,
			    enif_make_int(env, v->vix),
			    enif_make_int(env, get_variable_value(vp, v)),
			    enif_make_int(env, v->literal_pos),
			    enif_make_int(env, v->implication_clause));
}


static ERL_NIF_TERM make_binding(ErlNifEnv* env, varp_t*vp, variable_t* v)
{
    return enif_make_tuple2(env,
			    enif_make_int(env, v->vix),
			    enif_make_int(env, get_variable_value(vp, v)));
}

// get_bindings(Vp, Level, ClauseInfo)
// return bindings on Level

static ERL_NIF_TERM varp_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM list;
    int level;
    int clause_info = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0))
	return enif_make_badarg(env);
    if (!get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    list = enif_make_list(env, 0);
    if (level <= vp->level) {
	variable_t* bp = vp->undo[level].bs;
	while(bp != NULL) {
	    ERL_NIF_TERM elem;
	    if (clause_info)
		elem = make_clause_info(env,vp,bp);
	    else
		elem = make_binding(env,vp,bp);
	    list = enif_make_list_cell(env, elem, list);
	    bp = bp->next;
	}
    }
    return list;
}

// get_nbindings(Vp, Count, ClauseInfo)
// Count >= 0 get at most Count bindings
//
// returned list [{Var,Value}]
// or            [{Var,Value,LiteralPos,ClauseIndex}]
//
static ERL_NIF_TERM varp_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM list;
    int level;
    int count = 0;
    int clause_info = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &count) || (count < 0))
	return enif_make_badarg(env);
    if (!get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    
    list = enif_make_list(env, 0);
    level = vp->level;
    while((level >= 0) && count) {
	variable_t* bp = vp->undo[level].bs;
	while((bp != NULL) && count) {
	    ERL_NIF_TERM elem;
	    if (clause_info)
		elem = make_clause_info(env,vp,bp);
	    else
		elem = make_binding(env,vp,bp);
	    list = enif_make_list_cell(env, elem, list);
	    count--;
	    bp = bp->next;
	}
	level--;
    }
    return list;
}

static void load_atoms(ErlNifEnv* env)
{
    // Load atoms
    LOAD_ATOM(ok);
    LOAD_ATOM(true);
    LOAD_ATOM(false);
    LOAD_ATOM(undefined);
    LOAD_ATOM(default);
    LOAD_ATOM(grow);
    LOAD_ATOM(size);
    LOAD_ATOM(error);
    LOAD_ATOM(or);
    LOAD_ATOM(xor);
    LOAD_ATOM(inqueue);
    LOAD_ATOM(dead);
    LOAD_ATOM(watch);
    LOAD_ATOM(literal);
    LOAD_ATOM(variable);
    LOAD_ATOM(flags);
    LOAD_ATOM(mask);
    LOAD_ATOM(identity);
    LOAD_ATOM(random);
    LOAD_ATOM(occur);
    LOAD_ATOM_STRING(plus_occur, "+occur");
    LOAD_ATOM_STRING(minus_occur,"-occur");
    
    // info
    LOAD_ATOM(max_clause_length);
    LOAD_ATOM(max_conflicting);
    LOAD_ATOM(num_conflicting);
    LOAD_ATOM(number_of_clauses);
    LOAD_ATOM(number_of_learned_clauses);    
    LOAD_ATOM(number_of_variables);
    LOAD_ATOM(number_of_bound_variables);
    LOAD_ATOM(number_of_unbound_variables);
    LOAD_ATOM(clause_eval_counter);
    LOAD_ATOM(clause2_eval_counter);
    LOAD_ATOM(clause3_eval_counter);    
    LOAD_ATOM(eval_counter);
    LOAD_ATOM(undo_stack_size);
    LOAD_ATOM(value_stack_size);
    LOAD_ATOM(unit);
    LOAD_ATOM(use);
    LOAD_ATOM(reset);
    LOAD_ATOM(permanent);
    LOAD_ATOM(keep);
    LOAD_ATOM(level);
// misc
    LOAD_ATOM(fifo);
    LOAD_ATOM(lifo);
}

static int varp_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    UNUSED(env);
    UNUSED(load_info);

    // Create resource types
    varp_res = enif_open_resource_type(env, 0, "varp", varp_dtor,
				       ERL_NIF_RT_CREATE, &tried);
    load_atoms(env);
    *priv_data = 0;
    return 0;
}

static int varp_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
			ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    UNUSED(load_info);

    varp_res = enif_open_resource_type(env, 0, "varp", varp_dtor,
				       ERL_NIF_RT_CREATE | ERL_NIF_RT_TAKEOVER,
				       &tried);
    load_atoms(env);

    *priv_data = *old_priv_data;
    return 0;
}

static void varp_unload(ErlNifEnv* env, void* priv_data)
{
    UNUSED(env);
    UNUSED(priv_data);
}

ERL_NIF_INIT(varc, varp_funcs,
	     varp_load, NULL,
	     varp_upgrade, varp_unload)
