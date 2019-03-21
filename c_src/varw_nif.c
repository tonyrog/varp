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
#include <sys/time.h>
#include "erl_nif.h"

//#define NDEBUG
#include <assert.h>

// #define DEBUG

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
static ERL_NIF_TERM varp_clear_queue(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_enqueue_all(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_put(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_is_variable(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_implication_clause(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_conflicting_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_is_equal(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_remove_mark(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_undo(ErlNifEnv* env, int argc,
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

#define UNSAT  -1
#define OK     0
#define ERROR  1

#define UNDEF 0
#define FALSE -1
#define TRUE  1

#define MAX_CLAUSE_LENGTH  0xffffff

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

// #define TRACE(f,va...) fprintf(stderr, (f), va)
#define TRACE(f,va...)

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

typedef struct _lqueue_t
{
    size_t size;
    literal_t* head;
    literal_t** tail;
} lqueue_t;

#define VAR_FLAG_INQUEUE      0x01
#define VAR_FLAG_MARK         0x02

typedef struct _variable_t  // :object_t
{
    struct _variable_t* next; // free list/undo list
    struct _variable_t* qnext; // free list/undo list
    unsigned flags;           // VAR_FLAG_INQUEUE ...
    int  value;               // -1=false  0=unassigned  1=true
    int vix;                  // variable index
    unsigned  key[3];         // sort keys
    int  map_index;           // order_map index        
    int implication_clause;   // implication clause index -1 = none
    int literal_pos;          // position in implication clause
    int  level;               // implication clause level
    char* strname;            // string formated name or NULL
    struct _symbol_t* names;  // list of aliases
    literal_t lit[2];         // literal containers pos=0 neg=1
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

#define OR_CLAUSE 0
#define OR_GATE   1
#define XOR_GATE  2

#define CLAUSE_FLAG_INQUEUE 0x0001
#define CLAUSE_FLAG_DEAD    0x0002

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
    int cix;                 // clause id (index) 1..N
    unsigned long size;      // number of literals in lit
    unsigned  key[1];        // sort values
    uint16_t flags;          // INQUEUE ...    
    uint16_t op;             // OR|XOR    
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
    unsigned int vnext;       // next free variable number
    unsigned int vsize;       // allocated size of value/class map
    unsigned int vnum;        // number of variables
    unsigned int cnext;       // next clause number
    unsigned int csize;       // allocated size of value/class map
    unsigned int cnum;        // number of clauses
    unsigned int ssize;       // size of symbol hash table
    unsigned int snum;        // number of symbols in symbol hash table
    int bcp;                  // boolean constraint propagation
    int conflicting_clause;   // conflict clause from last eval
    unsigned int grow;        // how much to expand value/class map
    variable_t** var_map;     // variable map
    symbol_t**   sym_map;     // symbol hash table
    int*         order_map;   // variable order table
    int          sort_key[2]; // sort order -1,-2,1,2
    clause_t**   clause_map;  // clause_map[v] = class chain of variable v

    unsigned int unum;        // number of levels allocated
    undo_t*      undo;        // array of undo block, one for each level
    size_t stack_size;        // number of element in undo stack
    int level;                // current undo level (mark)
    
    lqueue_t     q;            // literal queue for propagation

    unsigned long num_variables;
    unsigned long num_clauses;    

    uint64_t  clause_eval_counter; // performance counter
    uint64_t  eval_counter;        // performance counter

    variable_t* var_queue_hd;      // var queue head
    variable_t* var_queue_tl;      // var queue tail

    variable_t undef;
    variable_t constant;

    arc4_stream_t as;              // random stream

    allocator_t var_allocator;     // heap storage for variable_t
    allocator_t sym_allocator;     // heap storage for symbols_t
} varp_t;

#define VARP_TRUE(vp)  ((vp)->ltrue)
#define VARP_FALSE(vp) ((vp)->lfalse)

ErlNifResourceType* varp_res;

ErlNifFunc varp_funcs[] = 
{
    NIF_FUNC( "new",                 0,  varp_new ),
    NIF_FUNC( "new",                 1,  varp_new ),
    NIF_FUNC( "info",                2,  varp_info ),
    NIF_FUNC( "add_variable",        1,  varp_add_variable ),
    NIF_FUNC( "get",                 2,  varp_get ),
    NIF_FUNC( "put",                 3,  varp_put ),
    NIF_FUNC( "put",                 4,  varp_put ),    
    NIF_FUNC( "class",               2,  varp_class ),
    NIF_FUNC( "key",                 3,  varp_key ),
    NIF_FUNC( "implication_clause",  2,  varp_implication_clause ),
    NIF_FUNC( "conflicting_clause",     1,  varp_conflicting_clause ),
    NIF_FUNC( "is_variable",         2,  varp_is_variable ),
    NIF_FUNC( "is_bound",            2,  varp_is_bound ),
    NIF_FUNC( "class_next",          2,  varp_class_next ),
    NIF_FUNC( "is_equal",            3,  varp_is_equal ),
    NIF_FUNC( "mark",                2,  varp_mark ),
    NIF_FUNC( "remove_mark",         2,  varp_remove_mark ),
    NIF_FUNC( "undo",                1,  varp_undo ),
    NIF_FUNC( "undo",                2,  varp_undo ),
    NIF_FUNC( "eval",                1,  varp_eval ),
    NIF_FUNC( "add_clause",          3,  varp_add_clause ),
    NIF_FUNC( "add_clause",          4,  varp_add_clause ),
    NIF_FUNC( "add_clause",          5,  varp_add_clause ),
    NIF_FUNC( "add_clause",          6,  varp_add_clause ),
    NIF_FUNC( "add_clause",          7,  varp_add_clause ),
    NIF_FUNC( "add_clause",          8,  varp_add_clause ),
    NIF_FUNC( "get_clause",          2,  varp_get_clause ),
    NIF_FUNC( "get_clause_flags",    2,  varp_get_clause_flags ),
    NIF_FUNC( "del_clause",          2,  varp_del_clause ),
    NIF_FUNC( "get_clauses",         3,  varp_get_clauses ),
    NIF_FUNC( "get_queue_first",     1,  varp_get_queue_first ),
    NIF_FUNC( "get_queue_next",      2,  varp_get_queue_next ),    
    NIF_FUNC( "clear_queue",         1,  varp_clear_queue ),
    NIF_FUNC( "enqueue_all",         1,  varp_enqueue_all ),
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
DECL_ATOM(bcp);
DECL_ATOM(qv);
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
DECL_ATOM(depth);
DECL_ATOM(plus_depth);
DECL_ATOM(minus_depth);

// info
DECL_ATOM(max_clause_length);
DECL_ATOM(number_of_clauses);
DECL_ATOM(number_of_variables);
DECL_ATOM(number_of_bound_variables);
DECL_ATOM(number_of_unbound_variables);
DECL_ATOM(clause_eval_counter);
DECL_ATOM(eval_counter);
DECL_ATOM(undo_stack_size);
DECL_ATOM(value_stack_size);
DECL_ATOM(class_stack_size);
DECL_ATOM(mark);

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

static inline int lit_index(lit_t lp)
{
#ifdef LIT_INTEGER
    return lp;
#else
    return (lp->sign < 0) ? -lp->var->vix : lp->var->vix;
#endif
}

static inline int lit_value(varp_t* vp, lit_t lp)
{
#ifdef LIT_INTEGER
    return (lp < 0) ? -vp->var_map[-lp]->value : vp->var_map[lp]->value;
#else
    UNUSED(vp);
    return (lp->sign < 0) ? -lp->var->value : lp->var->value;
#endif
}

static inline lit_t lit_negate(lit_t lp)
{
#ifdef LIT_INTEGER
    return -lp;
#else
    return (lp->sign < 0) ? &lp->var->lit[0] : &lp->var->lit[1];
#endif
}

static inline literal_t* lit_literal(varp_t* vp, lit_t lp)
{
#ifdef LIT_INTEGER
    return (lp<0) ? &vp->var_map[-lp]->lit[1] : &vp->var_map[lp]->lit[0];
#else
    UNUSED(vp);
    return (literal_t*) lp;
#endif
}

static inline variable_t* lit_variable(varp_t* vp, lit_t lp)
{
#ifdef LIT_INTEGER
    return (lp<0) ? vp->var_map[-lp] : vp->var_map[lp];
#else
    UNUSED(vp);
    return lp->var;
#endif
}


#ifdef DEBUG

static char* format_variable(variable_t* var)
{
    static char varname[32];
    
    if (var->strname != NULL)
	return var->strname;
    else {
	snprintf(varname, sizeof(varname), "%d", var->vix);
	return varname;
    }
}

static char* lit_format(varp_t* vp, lit_t lp)
{
    static char varname[32];    
#ifdef LIT_INTEGER
    char* n = (lp < 0) ? "!" : "";
    variable_t* var = (lp < 0) ? vp->var_map[-lp] : vp->var_map[lp];
    if (var->strname != NULL)
	snprintf(varname, sizeof(varname), "%s%s", n, var->strname);
    else
	snprintf(varname, sizeof(varname), "%s%d", n, var->vix);
#else
    UNUSED(vp);
    char* n = (lp->sign < 0) ? "!" : "";
    if (lp->var->strname != NULL)
	snprintf(varname, sizeof(varname), "%s%s", n, lp->var->strname);
    else
	snprintf(varname, sizeof(varname), "%s%d", n, lp->var->vix);
#endif
    return varname;
}

static char* literal_format(varp_t* vp, literal_t* lp)
{
    static char varname[32];    
    UNUSED(vp);
    char* n = (lp->sign < 0) ? "!" : "";
    if (lp->var->strname != NULL)
	snprintf(varname, sizeof(varname), "%s%s", n, lp->var->strname);
    else
	snprintf(varname, sizeof(varname), "%s%d", n, lp->var->vix);
    return varname;
}
#endif


static heap_t* new_heap_block(heap_t* next)
{
    heap_t* hp;

    if ((hp = enif_alloc(HEAP_BLOCK_SIZE + HEAP_ALIGN - 1)) == NULL)
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
	enif_free(hp);
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

static void unwatch(varp_t* vp, clause_t* cp, lit_t lp)
{
    literal_t* mp = lit_literal(vp, lp);
    wlink_t** wlp = &mp->wlist;
    wlink_t* wl;

    DBG("UNWATCH cix=%d lit=%d wl=%p\r\n", cp->cix, lit_index(lp), *wlp);

    while((wl = *wlp) && (clause_pointer(wl) != cp))
	wlp = &(wl->next);
    if (wl != NULL) {
	*wlp = wl->next;  // unlink
	wl->p = -1;       // mark as not used
    }
}

static clause_t* clause_alloc(varp_t* vp, uint16_t op, int size)
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
    cp->key[0] = 0;
    cp->flags = 0;
    cp->op = op;
    return cp;
}

static void clause_free(varp_t* vp, clause_t* cp)
{
    UNUSED(vp);
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

static void lqueue_enq(varp_t* vp, lit_t lp)
{
    lqueue_t* q = &vp->q;
    literal_t* mp;
    DBG("ENQ %s qsize=%ld\r\n", lit_format(vp, lp), q->size);
    assert(lit_value(vp, lp) == UNDEF);
    mp = lit_literal(vp, lp);
    mp->qlink = NULL;
    *q->tail = mp;
    q->tail = &(mp->qlink);
    q->size++;
}

static literal_t* lqueue_deq(varp_t* vp)
{
    lqueue_t* q = &vp->q;
    literal_t* lp;
    
    if ((lp = q->head) == NULL)
	return NULL;
    if ((q->head = lp->qlink) == NULL)
	q->tail = &q->head;
    q->size--;
    DBG("DEQ %s(%d,%ld) qsize=%ld\r\n", literal_format(vp,lp),
	lp->var->vix, lp->var->li,  q->size);
    return lp;
}

// assume literal is unassigned!
static inline void set_literal_level(varp_t* vp,lit_t lp,int value,
				     long li,int cix, int level)
{
    variable_t* var = lit_variable(vp, lp);
    DBG("SET_LITERAL %d = %d\r\n", lit_index(lp), value);
    assert(var->value == UNDEF);
#ifdef LIT_INTEGER
    var->value = (lp < 0) ? -value : value;
#else
    var->value = (lp->sign < 0) ? -value : value;
#endif
    var->implication_clause = cix;
    var->literal_pos = li;
    var->level = level;
}

static void set_literal(varp_t* vp,lit_t lp,int value,long li,int cix)
{
    set_literal_level(vp, lp, value, li, cix, vp->level);
}


// put value set_literal and push the correct literal on queue
// put (X, TRUE)   => enq(!X)   1  1  negate(X)
// put (X, FALSE)  => enq(X)    1 -1  X
// put (!X, TRUE)  == enq(X)   -1  1  negate(X)
// put (!X, FALSE) == enq(!X)  -1 -1  X
//
static void put_literal_level(varp_t* vp,lit_t lp,int value,
			      long li,int cix, int level)
{
    // this order lqueue_enq expect literal value = UNDEF
    lqueue_enq(vp, (value==TRUE) ? lit_negate(lp) : lp);
    set_literal_level(vp, lp, value, li, cix, level);
}

static inline void put_literal(varp_t* vp,lit_t lp,int value,long li,int cix)
{
    put_literal_level(vp, lp, value, li, cix, vp->level);
}

static inline int is_constant(int x)
{
    return ((x == TRUE) || (x == FALSE));
}

// none constant
static inline int is_literal(int x)
{
    return !((x == TRUE) || (x == FALSE));
}

// return true if variable is constant or bound to other variable
static int is_bound(varp_t* vp, int x)
{
    return (vp->var_map[ABS(x)]->value != UNDEF);
}

static void undo_init(varp_t* vp)
{
    vp->unum = DEFAULT_UNDO_SIZE;
    vp->undo = enif_alloc(DEFAULT_UNDO_SIZE * sizeof(undo_t));
    memset(vp->undo, 0, DEFAULT_UNDO_SIZE * sizeof(undo_t));
    vp->stack_size = 0;
    vp->level = 0;
}

// push undo mark
static int push_level(varp_t* vp, int level)
{
    if (level >= (int)vp->unum) {
	unsigned int n = vp->unum;
	vp->unum *= 2;
	vp->undo = enif_realloc(vp->undo, vp->unum*sizeof(undo_t));
	memset(vp->undo+n, 0, n*sizeof(undo_t));
    }
    vp->level = level;
    DBG("PUSH MARK: level=%d\r\n", level);
    return 0;
}

static void push_variable_level(varp_t* vp, variable_t* var, int level)
{
    DBG("PUSH VARIABLE: var=%s, level=%d, value=%d\r\n",
	format_variable(var), level, var->value);
    var->next = vp->undo[level].bs;
    vp->undo[level].bs = var;
    vp->undo[level].bs_size++;
    vp->stack_size++;
}

static inline void push_variable(varp_t* vp, variable_t* var)
{
    push_variable_level(vp, var, vp->level);
}

static void undo_level(varp_t* vp, int level)
{
    variable_t* bp = vp->undo[level].bs;
    vp->stack_size -= vp->undo[level].bs_size;
    while(bp != NULL) {
	DBG("POP VARIABLE %s value=%d\r\n",
	    format_variable(bp->var), bp->value);
	bp->value = UNDEF;
	bp = bp->next;
    }
    vp->undo[level].bs = NULL;
    vp->undo[level].bs_size = 0;
}

// undo all levels including ilevel or count
static int pop_to_level(varp_t* vp, int count, int ilevel)
{
    int level = vp->level;
    while(level > 0) {
	undo_level(vp, level);
	if (count) count--;
	if ((level == ilevel) || ((ilevel < 0) && (count == 0)))
	    return level;
	level--;
    }
    return 0;
}

static void forget_bindings(varp_t* vp, int level)
{
    vp->stack_size -= vp->undo[level].bs_size;
    vp->undo[level].bs = NULL;
    vp->undo[level].bs_size = 0;
}

// permanent bindings includeing mark level or count
static int forget_to_level(varp_t* vp, int count, int ilevel)
{
    int level = vp->level;

    // use level 0 as special place
    while(level > 0) {
	forget_bindings(vp, level);
	if (count) count--;
	if ((level == ilevel) || ((ilevel < 0) && (count == 0)))
	    return level;
	level--;
    }
    return 0;
}

static void init_literal(literal_t* lp, variable_t* var, int sign)
{
    lp->sign = sign;
    lp->var  = var;
    lp->wlist = NULL;
    lp->qlink = NULL;
}

static void init_variable(variable_t* var, int value, int vix)
{
    var->next = NULL;
    var->flags = 0;    
    var->value = value;
    var->vix   = vix;
    
    var->key[0] = 0;
    var->key[1] = 0;
    var->key[2] = 0;

    var->map_index = vix;
    var->implication_clause  = -1;
    var->literal_pos = -1;
    var->level = -1;
    var->strname = NULL;
    var->names = NULL;

    init_literal(&var->lit[0], var, 1);
    init_literal(&var->lit[1], var, -1);
}


#if 0
static void clear_variable_queue(varp_t* vp)
{
    variable_t* vptr;

    vptr = vp->var_queue_hd;
    while(vptr) {
	variable_t* vptrn = vptr->qnext;
	vptr->qnext = NULL;
	vptr->flags &= ~VAR_FLAG_INQUEUE;
	vptr = vptrn;
    }
    vp->var_queue_hd = NULL;
    vp->var_queue_tl = NULL;
}

static int enqueue_variable(varp_t* vp, variable_t* vptr)
{
    if (vptr->flags & VAR_FLAG_INQUEUE)
	return 0;
    vptr->qnext = NULL;
    if (vp->var_queue_tl == NULL)
	vp->var_queue_hd = vptr;
    else
	vp->var_queue_tl->qnext = vptr;
    vp->var_queue_tl = vptr;
    vptr->flags |= VAR_FLAG_INQUEUE;
    return 1;
}

static variable_t* dequeue_variable(varp_t* vp)
{
    variable_t* vptr;

    if ((vptr = vp->var_queue_hd) != NULL) {
	if ((vp->var_queue_hd = vptr->qnext) == NULL)
	    vp->var_queue_tl = NULL;
	vptr->qnext = NULL;
	vptr->flags &= ~VAR_FLAG_INQUEUE;
    }
    return vptr;
}

#endif

static int clause_insert(ErlNifEnv* env, varp_t* vp, clause_t* cp)
{
    (void) env;
    int cix = vp->cnext++;

    cp->cix = cix;

    if (vp->cnext == vp->csize) {
	unsigned int new_csize = vp->csize + vp->grow;
	clause_t** cpp;

	if (!(cpp = enif_realloc(vp->clause_map, new_csize*sizeof(clause_t**))))
	    return -1;
	vp->clause_map = cpp;
	vp->csize = new_csize;
    }
    vp->cnum++;
    vp->clause_map[cix] = cp;
    return cix;
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

static int get_lit(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, lit_t* xp)
{
    int x;

    if (!enif_get_int(env, arg, &x))
	return 0;

    if (x < 0) {
	if (-x >= (int)vp->vnext) {
	    DBG("literal %d out of range\r\n", x);
	    return 0;
	}
#ifdef LIT_INTEGER
	*xp = x;
#else
	*xp = &(vp->var_map[-x]->lit[1]);
#endif
	return 1;
    }
    else if (x > 0) {
	if (x >= (int)vp->vnext) {
	    DBG("literal %d out of range\r\n", x);
	    return 0;
	}
#ifdef LIT_INTEGER
	*xp = x;
#else
	*xp = &(vp->var_map[x]->lit[0]);
#endif	
	return 1;
    }
    else { // t == 0  => allow 0 as FALSE!
	*xp = vp->lfalse;
	return 1;
    }
}

static int get_literal(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg,
		       literal_t** lpp)
{
    lit_t xp;
    if (!get_lit(env, vp, arg, &xp)) return 0;
    *lpp = lit_literal(vp, xp);
    return 1;
}

static int get_variable(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg,
		       variable_t** vpp)
{
    lit_t xp;
    if (!get_lit(env, vp, arg, &xp)) return 0;
    *vpp = lit_variable(vp, xp);
    return 1;
}

static ERL_NIF_TERM make_lit(ErlNifEnv* env, lit_t lp)
{
    return enif_make_int(env, lit_index(lp));
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, literal_t* lp)
{
    return enif_make_int(env,(lp->sign<0)?-lp->var->vix:lp->var->vix);
}

static void cleanup(varp_t* vp)
{
    if (vp->sym_map) {
	int i;
	for (i = 0; i < (int)vp->ssize; i++) {
	    symbol_t* sp = vp->sym_map[i];
	    while(sp) {
		enif_free(sp->data);
		sp = sp->next;
	    }
	}
	enif_free(vp->sym_map);
	vp->sym_map = NULL;		    
    }
    
    if (vp->var_map) {
	enif_free(vp->var_map);
	vp->var_map = NULL;
    }
    
    if (vp->order_map) {
	enif_free(vp->order_map);
	vp->order_map = NULL;
    }
    
    if (vp->clause_map) {
	int i;
	for (i = 0; i < (int)vp->cnext; i++) {	
	    clause_t* cp = vp->clause_map[i];
	    if (cp != NULL)
		clause_free(vp, cp);		
	}
	enif_free(vp->clause_map);
	vp->clause_map = NULL;
    }

    if (vp->undo) {
	enif_free(vp->undo);
	vp->undo = NULL;
    }
    
    cleanup_allocator(&vp->var_allocator);
    cleanup_allocator(&vp->sym_allocator);
}

static void varp_dtor(ErlNifEnv* env, void* obj)
{
    (void) env;
    TRACE("dtor called %s\r\n", "");
    cleanup((varp_t*) obj);
}

static ERL_NIF_TERM varp_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    varp_t* vp;
    unsigned int grow   = DEFAULT_MAP_GROW;
    unsigned int vsize  = DEFAULT_MAP_SIZE;
    unsigned int csize  = DEFAULT_MAP_SIZE;
    unsigned int ssize;
    int bcp = 1;
    int qv = 0;
    ERL_NIF_TERM t;

    if (argc == 1) {
	ERL_NIF_TERM list = argv[0];
	ERL_NIF_TERM head, tail;
	
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
		else if (elem[0] == ATOM(bcp)) {
		    if (elem[1] == ATOM(default))
			bcp = 1;
		    else if (!get_boolean(env, elem[1], &bcp))
			return enif_make_badarg(env);
		    bcp = 1;
		}
		else if (elem[0] == ATOM(qv)) {
		    if (elem[1] == ATOM(default))
			qv = 0;
		    else if (!get_boolean(env, elem[1], &qv))
			return enif_make_badarg(env);
		}		
		else
		    return enif_make_badarg(env);
		list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
    }
    
    if (!(vp = enif_alloc_resource(varp_res, sizeof(varp_t))))
	goto error;
    memset(vp, 0, sizeof(varp_t));

    vp->vnext = 2;
    vp->vsize = vsize;
    vp->vnum  = 0;

    vp->grow = grow;
    if (!(vp->var_map = enif_alloc(vsize*sizeof(variable_t**))))
	goto error;
    
    ssize = 1;
    while(ssize < vsize) ssize *= 2;
    if (!(vp->sym_map = enif_alloc(ssize*sizeof(symbol_t**))))
	goto error;
    memset(vp->sym_map, 0, ssize*sizeof(symbol_t**));
    vp->ssize = ssize;
    vp->snum = 0;
    
    if (!(vp->order_map = enif_alloc(vsize*sizeof(int))))
	goto error;
    vp->cnext = 0;
    vp->csize = csize;
    vp->cnum = 0;
    vp->bcp  = bcp;

    if (!(vp->clause_map = enif_alloc(csize*sizeof(clause_t**))))
	goto error;
    if (init_allocator(&vp->var_allocator, sizeof(variable_t)) < 0)
	goto error;
    if (init_allocator(&vp->sym_allocator, sizeof(symbol_t)) < 0)
	goto error;

    lqueue_init(&vp->q);

    undo_init(vp);
    
    vp->eval_counter = 0;
    vp->clause_eval_counter = 0;

    vp->order_map[0] = 0;
    init_variable(&vp->undef, UNDEF, 0);
    vp->var_map[0] = &vp->undef;
    vp->order_map[1] = 1;
    init_variable(&vp->constant, TRUE, 1);
    vp->var_map[1] = &vp->constant;
#ifdef LIT_INTEGER
    vp->ltrue = TRUE;
    vp->lfalse = FALSE;
#else
    vp->ltrue = &vp->constant.lit[0];
    vp->lfalse = &vp->constant.lit[1];
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
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if ((var = varp_alloc(&vp->var_allocator)) == NULL)
	return enif_make_badarg(env);

    vix = vp->vnext++;
    if (vp->vnext == vp->vsize) {
	unsigned int new_vsize = vp->vsize + vp->grow;
	variable_t** p;
	int* ip;

	if (!(p = enif_realloc(vp->var_map, new_vsize*sizeof(variable_t*))))
	    return enif_make_badarg(env);
	if (!(ip = enif_realloc(vp->order_map, new_vsize*sizeof(int))))
	    return enif_make_badarg(env);
	vp->var_map = p;
	vp->order_map = ip;
	vp->vsize = new_vsize;
    }
    vp->vnum++;
    vp->order_map[vix] = vix;
    init_variable(var, UNDEF, vix);
    vp->var_map[vix] = var;
    
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
    if (!get_variable(env, vp, argv[1], &var))
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
	sp->data = enif_alloc(bin.size);
	memcpy(sp->data, bin.data, bin.size);
	sp->size = bin.size;	
    }
    else {
	sp->data = enif_alloc(bin.size+1);
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
	symbol_t** sym_map1 = enif_alloc(ssize1*sizeof(symbol_t**));

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
	enif_free(vp->sym_map);
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
    if (!get_variable(env, vp, argv[1], &var))
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
	int v = vp->order_map[i];
	if (!is_bound(vp, v))
	    return enif_make_tuple2(env,enif_make_int(env, i),
				    enif_make_int(env, v));
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
	int v = vp->order_map[i];
	if (!is_bound(vp, v)) {
	    if (!skip)
		return enif_make_tuple2(env,enif_make_int(env, i),
					enif_make_int(env, v));
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
	if (is_bound(vp, i)) {
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
	vp->var_map[i]->key[k] = i;
    }
}

static void order_k_random(varp_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i]->key[k] = arc4_random_uniform(&vp->as, 0x7fffffff);
    }
}

static void order_k_undefined(varp_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i]->key[k] = 0;
    }
}

// scan through all variables and calculate the occur count, key[k]
static void order_k_occur(varp_t* vp, int k)
{
    int i;
    
    for (i = 2; i < (int)vp->vnext; i++)
	vp->var_map[i]->key[k] = 0;

    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	if (cp != NULL) {
	    int j;
	    for (j = 0; j < (int)cp->size; j++) {
		int x = lit_index(cp->lit[j]);
		if (x < 1)
		    vp->var_map[-x]->key[k]++;
		else if (x > 1)
		    vp->var_map[x]->key[k]++;
	    }
	}
    }
}

// FIXME: order variables according to "depth"
static void order_k_depth(varp_t* vp, int k)
{
    int i;
    
    for (i = 2; i < (int)vp->vnext; i++)
	vp->var_map[i]->key[k] = 0;

    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	if (cp != NULL) {
	    int j;
	    for (j = 0; j < (int)cp->size; j++) {
		int x = lit_index(cp->lit[j]);
		if (x < 1)
		    vp->var_map[-x]->key[k]++;
		else if (x > 1)
		    vp->var_map[x]->key[k]++;
	    }
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
	r = ap->key[k1] - bp->key[k1];
	if (r==0) {
	    if (k2 > 0)
		r = ap->key[k2] - bp->key[k2];
	    else if (k2 < 0)
		r = bp->key[-k2] - ap->key[-k2];
	}
    }
    else if (k1 < 0) {
	r = bp->key[-k1] - ap->key[-k1];
	if (r==0) {
	    if (k2 > 0)
		r = ap->key[k2] - bp->key[k2];
	    else if (k2 < 0)
		r = bp->key[-k2] - ap->key[-k2];
	}
    }
    else { // k1 == 0
	if (k2 > 0)
	    r = ap->key[k2] - bp->key[k2];
	else if (k2 < 0)
	    r = bp->key[-k2] - ap->key[-k2];
    }
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
	else if ((argv[i] == ATOM(depth)) || (argv[i] == ATOM(plus_depth))) {
	    order_k_depth(vp, k);
	}
	else if (argv[i] == ATOM(minus_depth)) {
	    order_k_depth(vp, k);
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
    // update map_index of sorted variables
    for (i = u; i < (int)vp->vnext; i++) {
	int v = vp->order_map[i];
	vp->var_map[v]->map_index = i;
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
	if (!get_lit(env, vp, head, &xp) || (lit_value(vp, xp) != UNDEF))
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    if (!(map = enif_alloc(vp->vsize*sizeof(int))))
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
    while ((mi < vp->vnext) && is_bound(vp, vp->order_map[mi])) {
	int x = vp->order_map[mi];
	vp->var_map[x]->flags |= VAR_FLAG_MARK;
	map[mi++] = x;
    }
    ui = mi;  // save the position for the first unbound variabel
    // copy/move variables in the list (not already copied)
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	literal_t* lp;
	if (!get_literal(env, vp, head, &lp))
	    return enif_make_badarg(env);	    
	if (!(lp->var->flags & VAR_FLAG_MARK)) { // not moved
	    lp->var->flags |= VAR_FLAG_MARK;     // mark as moved
	    lp->var->map_index = mi;
	    map[mi++] = lp->var->vix;
	}
	list = tail;
    }
    // move rest of the varaibles not already moved
    while(ui < vp->vnext) {
	int x = vp->order_map[ui];
	if (!(vp->var_map[x]->flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[x]->flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[x]->map_index = mi;
	    map[mi++] = x;
	}
	ui++;
    }
    enif_free(vp->order_map);
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
	if (!get_lit(env, vp, head, &xp) || (lit_value(vp,xp) != UNDEF))
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    if (!(map = enif_alloc(vp->vsize*sizeof(int))))
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
    while ((mi < vp->vnext) && is_bound(vp, vp->order_map[mi])) {
	int x = vp->order_map[mi];
	vp->var_map[x]->flags |= VAR_FLAG_MARK;
	map[mi++] = x;
    }
    ui = mi;  // save the position for the first unbound variabel
    mi = vp->vnext;  // last position(+1)
    // copy/move variables in the list (not already copied)
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	literal_t* lp;
	if (!get_literal(env, vp, head, &lp))
	    return enif_make_badarg(env);	    
	if (!(lp->var->flags & VAR_FLAG_MARK)) { // not moved
	    lp->var->flags |= VAR_FLAG_MARK;     // mark as moved
	    lp->var->map_index = --mi;
	    map[mi] = lp->var->vix;
	}
	list = tail;
    }

    mi = ui;
    // move rest of the varaibles not already moved
    while(ui < vp->vnext) {
	int x = vp->order_map[ui];
	if (!(vp->var_map[x]->flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[x]->flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[x]->map_index = mi;
	    map[mi++] = x;
	}
	ui++;
    }
    enif_free(vp->order_map);
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
    lit_t xp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    return enif_make_int(env, lit_value(vp, xp));
}

static ERL_NIF_TERM varp_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    int x;    
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if ((x = lit_value(vp, xp)) == UNDEF)
	return make_lit(env, xp);
    return enif_make_int(env, x);
}

static ERL_NIF_TERM varp_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    literal_t* lp;
    int k;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &k))
	return enif_make_badarg(env);
    if ((k < 0) || (k > 2))
	return enif_make_badarg(env);
    return enif_make_int(env, lp->var->key[k]);
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
    if (!get_variable(env, vp, argv[1], &var))
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
    variable_t* var;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_variable(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return make_boolean(env, var->value == UNDEF);
}

static ERL_NIF_TERM varp_conflicting_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->conflicting_clause);
}

static ERL_NIF_TERM varp_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    variable_t* var;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_variable(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return make_boolean(env, var->value != UNDEF);
}

static ERL_NIF_TERM varp_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    return enif_make_badarg(env);
}


static ERL_NIF_TERM varp_is_equal(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp, yp;
    int x, y;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if (!get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);
    if (!(x = lit_index(xp)))
	return enif_make_badarg(env);
    if (!(y = lit_index(yp)))
	return enif_make_badarg(env);
    return make_boolean(env, (x == y));
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
    if (!get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if (!get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);
    if (argc == 4) {
	if (!enif_get_int(env, argv[3], &level) || (level < 0) ||
	    (level >= (int)vp->unum))
	    return enif_make_badarg(env);
    }
    y = lit_value(vp, yp);
    if (!is_constant(y))
	return enif_make_badarg(env);
    x = lit_value(vp, xp);
    if (x == UNDEF) {
	variable_t* var = lit_variable(vp, xp);
	if (level < 0) {
	    push_variable(vp, var);
	    put_literal(vp, xp, y, -1, -1);
	}
	else {
	    push_variable_level(vp, var, level);
	    put_literal_level(vp, xp, y, -1, -1, level);
	}
    }
    else if (x != y)
	return ATOM(false);
    return ATOM(true);
}

static ERL_NIF_TERM varp_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int level;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &level) || (level == 0))
	return enif_make_badarg(env);
    push_level(vp, level);
    return ATOM(true);
}

//
// undo mark
//   undo all bindings until mark is found
//   mark must exist!
// undo count (=-mark)
//   undo count number of marks
// undo 0 = undo everything (mark can not exist)
//
static ERL_NIF_TERM varp_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    int count = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (argc == 1)
	level = 0;
    else {
	if (!enif_get_int(env, argv[1], &level))
	    return enif_make_badarg(env);
    }
    if (level < 0)
	count = -level;
    if ((count == 0) && (level != 0)) {
	if (level < (int)vp->unum)
	    goto found;	    
	return enif_make_badarg(env); // mark not found!
    }
found:
    vp->level = pop_to_level(vp, count, level);
    return enif_make_int(env, vp->level);
}

//
// remove a mark, leave bindings intact
// or remove count(-mark) number of marks
//
static ERL_NIF_TERM varp_remove_mark(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    int count = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level))
	return enif_make_badarg(env);
    if (level < 0)
	count = -level;
    if ((count == 0) && (level != 0)) {
	if (level < (int)vp->unum)
	    goto found;	    
	return enif_make_badarg(env); // mark not found!
    }
found:
    // fixme merge undo[mark] with undo[mark-1]
    vp->level = forget_to_level(vp, count, level);
    return enif_make_int(env, vp->level);
}

#ifdef DEBUG
#define PRINT_LIT(msg,lit,size) print_lit((msg),(lit),(size))
#define PRINT_CLAUSE(vp,msg,cp) print_clause((vp),(msg),(cp))
#else
#define PRINT_LIT(msg,lit,size)
#define PRINT_CLAUSE(vp,msg,cp)
#endif

static void print_lit(char* label, lit_t* lit, size_t size)
{
    if (size == 0)
	printf("%s={}", label);
    else {
	unsigned k;
	printf("%s={%d", label, lit_index(lit[0]));
	for (k=1; k<size; k++)
	    printf(",%d",lit_index(lit[k]));
	printf("}\r\n");
    }
}

static void print_clause(varp_t* vp, char* label, clause_t* cp)
{
    unsigned k;
    printf("%s id=%d,[%ld:%ld] {%d/%d",
	   label, cp->cix, cp->wl[0].p, cp->wl[1].p,
	   lit_index(cp->lit[0]),lit_value(vp,cp->lit[0]));
    for (k=1; k<cp->size; k++)
	printf(",%d/%d",lit_index(cp->lit[k]),lit_value(vp,cp->lit[k]));
    printf("}\r\n");
}

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
    vp->clause_eval_counter++;    

    if ((wp0 < 0) || (wp1 < 0)) // clause is dead?
	return 0;

    if (wi==0) {  // watch point 0
	if ((lw = lit_value(vp, cp->lit[wp1])) == TRUE)
	    return 0;
	// find a new watch point
	for (p = 1; p < (int)cp->size; p++) {
	    int lv = lit_value(vp, cp->lit[p]);
	    if (lv != FALSE) {  // TRUE | UNDEF
		if (p != wp1) {  // skip other watch point
		    if (lv == TRUE)
			return 0;
		    break;  // new watch point found
		}
	    }
	}
	DBG("  wp0: %s %d=>%ld\r\n", lit_format(vp, cp->lit[wp0]), wp0, p);
	if (p == (int)cp->size) {  // no new watch point found
	    if (lw == FALSE)
		return -1; // all are false
	    else {
		literal_t* mp = lit_literal(vp, cp->lit[wp1]);
		variable_t* var = mp->var;
		push_variable(vp, var);
		put_literal(vp, cp->lit[wp1], TRUE, wp1, cp->cix);
	    }
	}
	else {  // move watch
	    literal_t* mp = lit_literal(vp, cp->lit[p]);
	    *wlp = wl0->next;
	    set_wlink(wl0, p, mp);
//	    wl0->p = p;
//	    wl0->next = mp->wlist;
//	    mp->wlist = wl0;	    
	}
    }
    else { // watch point 1
	if ((lw = lit_value(vp, cp->lit[wp0])) == TRUE)
	    return 0;
	// find a new watch point
	for (p = 1; p < (int)cp->size; p++) {
	    int lv = lit_value(vp, cp->lit[p]);
	    if (lv != FALSE) {  // TRUE | UNDEF
		if (p != wp0) {  // skip other watch point
		    if (lv == TRUE)
			return 0;
		    break;  // new watch point found
		}
	    }
	}
	DBG("  wp1: %s %d=>%ld\r\n", lit_format(vp, cp->lit[wp1]), wp1, p);
	if (p == (int)cp->size) {  // no new watch point found
	    if (lw == FALSE) // contradiction
		return -1;
	    else {
		literal_t* mp = lit_literal(vp, cp->lit[wp0]);
		variable_t* var = mp->var;
		push_variable(vp, var);
		put_literal(vp, cp->lit[wp0], TRUE, wp0, cp->cix);
	    }
	}
	else {  // move watch
	    literal_t* mp = lit_literal(vp, cp->lit[p]);
	    *wlp = wl1->next;
	    set_wlink(wl1, p, mp);
//	    wl1->p = p;
//	    wl1->next = mp->wlist;
//	    mp->wlist = wl1;
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
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    vp->eval_counter++;
    vp->conflicting_clause = -1;

    DBG("EVAL %ld\r\n", vp->eval_counter);

    while((lp = lqueue_deq(vp)) != NULL) {
	wlink_t** wlp = &lp->wlist;
	wlink_t*  wl;
	
	while((wl = *wlp) != NULL) {
	    clause_t* cp = clause_pointer(wl);
	    if (eval_clause(vp, cp, wlink_index(wl), wlp) < 0) {
		vp->conflicting_clause = cp->cix;
		lqueue_clear(&vp->q);   
		return ATOM(false);
	    }
	    if (*wlp == wl)
		wlp = &wl->next;
	}
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
    else if (argv[1] == ATOM(number_of_variables)) {
	return enif_make_int(env, vp->vnum);
    }
    else if (argv[1] == ATOM(number_of_clauses)) {
	return enif_make_int(env, vp->cnum);
    }
    else if (argv[1] == ATOM(number_of_bound_variables)) {
	return enif_make_int(env, vp->stack_size);
    }
    else if (argv[1] == ATOM(number_of_unbound_variables)) {
	return enif_make_int(env, vp->vnum - vp->stack_size);
    }
    else if (argv[1] == ATOM(clause_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter);
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
    else if (argv[1] == ATOM(class_stack_size)) {
	return enif_make_uint64(env, 0);
    }
    else if (argv[1] == ATOM(bcp)) {
	return make_boolean(env, vp->bcp);
    }
    else if (argv[1] == ATOM(qv)) {
	return make_boolean(env, 0);
    }    
    else if (argv[1] == ATOM(grow)) {
	return enif_make_uint(env, vp->grow);
    }
    else if (argv[1] == ATOM(size)) {
	return enif_make_uint(env, vp->vsize);
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
//   XOR:
//      x6 x5 x2
//
// OR:
//   X (Tc=0,Fc>0) => X -1
//   X (Tc>0) => X => X  1
//
// XOR:
//   X (Tc=0,Fc>0) => X -1
//   X (Tc>0)      => X  1
//

static ERL_NIF_TERM add_clause_array(ErlNifEnv* env, varp_t* vp, int op,
				     lit_t* lit, size_t size)
{
    clause_t* cp;
    int cix;
    unsigned i;
    long p, wp0, wp1;
    unsigned Tc=0, Fc=0;

    PRINT_LIT("   src", lit, size);
    
    // first sort all literals by absolute value
    QSORT_R(lit+1, size-1, sizeof(lit_t), cmp_rev_abs_lit, vp);

    // PRINT_LIT(" sorted", lit, size);

    // remove TRUE literals
    i = size-1;
    while((i > 0) && (lit[i] == VARP_TRUE(vp))) { i--; size--; Tc++; }
    // PRINT_LIT("  del-T", lit, size);

    // remove FALSE literals
    while((i > 0) && (lit[i] == VARP_FALSE(vp))) { i--; size--; Fc++; }
    // PRINT_LIT("  del-F", lit, size);

    // remove duplicates
    if (op == OR_GATE) {
	unsigned u=1,v=1,w=1;
	while(v < size) {
	    while((w < size) && (lit[v] == lit[w])) w++;
	    if ((u > 1) && (lit[u-1] == lit_negate(lit[v]))) {
		u--;
		Tc++;
	    }
	    else
		lit[u++] = lit[v];
	    v = w;
	}
	size = u;
    }
    else {
	unsigned u=1,v=1,w=1;
	while(v < size) {
	    while((w < size) && (lit[v] == lit[w])) w++;
	    if ((w-v) & 1) { // odd number of duplicates save one
		if ((u > 1) && (lit[u-1] == lit_negate(lit[v]))) {
		    u--;
		    Tc++;
		}
		else
		    lit[u++] = lit[v];
	    }
	    else {  // even number of duplicates => FALSE
		Fc++;
	    }
	    v = w;
	}
	size = u;
    }
    // PRINT_LIT("del-dup", lit, size);

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
    PRINT_LIT("shuffle", lit, size);
#endif

    if (op == OR_GATE) {
	if (size == 1) {
	    if ((Tc==0) && (Fc>0)) 
		lit[size++] = VARP_FALSE(vp);
	}
	if (Tc>0) // add the T constant to the gate
	    lit[size++] = VARP_TRUE(vp);
	if (lit[0] == VARP_TRUE(vp))
	    op = OR_CLAUSE;  // it is a clause
    }
    else {  // XOR
	if (size == 1) {
	    if ((Tc==0) && (Fc>0))
		lit[size++] = VARP_FALSE(vp);
	    else if (Tc>0)
		lit[size++] = (Tc & 1) ? VARP_TRUE(vp) : VARP_FALSE(vp);
	}
	else if (Tc & 1) // T = XOR(X4,X3,X2) => T = XOR(-X4,X3,X2)
	    lit[0] = lit_negate(lit[0]);
    }
    PRINT_LIT("   dest", lit, size);

    if (op != OR_CLAUSE) // !!! 
	return enif_make_badarg(env);
    
    if ((cp = clause_alloc(vp, op, size)) == NULL) {
	DBG("unable to alloc clause\r\n");
	return enif_make_badarg(env);
    }

    memcpy(cp->lit, lit, sizeof(lit_t)*size);

    if ((cix = clause_insert(env, vp, cp)) < 0) {
	DBG("unable to clause_insert\r\n");
	return enif_make_badarg(env);
    }

    // set watch points

    if (cp->lit[size-1] == VARP_TRUE(vp))
	goto dead;

    p = 1;
    while(p < (int)cp->size) {
	switch(lit_value(vp,cp->lit[p])) {
	case FALSE: break;
	case TRUE: goto dead;
	case UNDEF:
	default: wp0 = p; goto next_wp;
	}
	p++;
    }
    // all false    
    return ATOM(false);

next_wp:
    p = wp0+1;
    while(p < (int)cp->size) {
	switch(lit_value(vp,cp->lit[p])) {
	case FALSE: break;
	case TRUE: goto dead;
	case UNDEF:
	default: wp1 = p; goto done_wp;
	}
	p++;
    }
    return ATOM(error);
    
done_wp:
    set_wlink(&cp->wl[0], wp0, lit_literal(vp, cp->lit[wp0]));
    set_wlink(&cp->wl[1], wp1, lit_literal(vp, cp->lit[wp1]));
//    if (vp->level > 1)
//	print_clause(vp,"done clause: ",cp);
    return enif_make_int(env, cix);    

dead:
    cp->wl[0].p = -1;
    cp->wl[1].p = -1;
//    if (vp->level > 1)
//	print_clause(vp,"dead clause: ", cp); 
    return enif_make_int(env, cix);
}

//
// add_clause(vp, 'or',  x1, ..., xn)
// add_clause(vp, 'xor', x1, ..., xn)
// add_clause(vp, 'or'|'xor', [x1, ..., xn])
//
static ERL_NIF_TERM varp_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    int op;
    varp_t* vp;
    int size = 0;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    
    if (argv[1] == ATOM(or))
	op = OR_GATE;
    else if (argv[1] == ATOM(xor))
	op = XOR_GATE;
    else
	return enif_make_badarg(env);

    if (argc == 3) {   // argv[2] is a list of literals
	ERL_NIF_TERM list = argv[2];
	ERL_NIF_TERM head, tail;

	while(enif_get_list_cell(env, list, &head, &tail)) {
	    size++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
	else {
	    lit_t literals[size];
	    lit_t* lpp = &literals[0];

	    list = argv[2];
	    while(enif_get_list_cell(env, list, &head, &tail)) {
		if (!get_lit(env, vp, head, lpp))
		    return enif_make_badarg(env);
		lpp++;
		list = tail;
	    }
	    return add_clause_array(env, vp, op, literals, size);	    
	}
    }
    else if ((size = (argc-2)) > 0) {
	lit_t literals[size];
	lit_t* lpp = &literals[0];
	int j;

	for (j = 2; j < argc; j++) {
	    if (!get_lit(env, vp, argv[j], lpp))
		return enif_make_badarg(env);
	    lpp++;
	}
	return add_clause_array(env, vp, op, literals, size);
    }
    return enif_make_badarg(env);    
}

static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int cix;
    clause_t* cp;
    long p;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    if (cix >= vp->cnext)
	return enif_make_badarg(env);
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);

    // remove watched literals
    if ((p = cp->wl[0].p) > 0) unwatch(vp, cp, cp->lit[p]);
    if ((p = cp->wl[1].p) > 0) unwatch(vp, cp, cp->lit[p]);
    // FIXME: remove push watch points
	
    clause_free(vp, cp);
    vp->clause_map[cix] = NULL;  // FIXME! reuse this position
    vp->cnum--;
    return ATOM(ok);
}

static ERL_NIF_TERM varp_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varp_t* vp;
    unsigned int cix;
    ERL_NIF_TERM list;
    ERL_NIF_TERM op;
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    if (cix >= vp->cnext)
	return enif_make_badarg(env);
    if ((cp = vp->clause_map[cix]) == NULL)
	return ATOM(undefined);

    list = enif_make_list(env, 0);
    for (i = cp->size-1; i >= 0; i--) {
	ERL_NIF_TERM elem = make_lit(env, cp->lit[i]);
	list = enif_make_list_cell(env, elem, list);
    }
    switch(cp->op) {
    case OR_CLAUSE: op = ATOM(or); break;	
    case OR_GATE:   op = ATOM(or); break;
    case XOR_GATE:  op = ATOM(xor); break;
    default:        op = ATOM(undefined); break;
    }
    return enif_make_tuple2(env, op, list);
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
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);

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

static ERL_NIF_TERM varp_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    ERL_NIF_TERM list;
    literal_t* lp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);

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
	for (i = 0; i < (int)vp->cnext; i++) {
	    clause_t* cp = vp->clause_map[i];
	    int j = 0;
	    while((j < (int)cp->size) && (lit_literal(vp,cp->lit[j]) != lp))
		j++;
	    if (j < (int)cp->size) { // found
		ERL_NIF_TERM elem = enif_make_uint(env, cp->cix);
		list = enif_make_list_cell(env, elem, list);
	    }
	}
    }
    else if (argv[2] == ATOM(variable)) {
	variable_t* var = lp->var;
	for (i = 0; i < (int)vp->cnext; i++) {
	    clause_t* cp = vp->clause_map[i];
	    int j = 0;
	    while((j < (int)cp->size) && (lit_variable(vp,cp->lit[j]) != var))
		j++;
	    if (j < (int)cp->size) { // found
		ERL_NIF_TERM elem = enif_make_uint(env, cp->cix);
		list = enif_make_list_cell(env, elem, list);
	    }
	}
    }
    else
	return enif_make_badarg(env);
    return list;
}

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

static ERL_NIF_TERM varp_get_queue_next(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);
    if (vp->q.head == NULL)
	return ATOM(false);
    if (lp->qlink != NULL) 
	return make_literal(env, lp->qlink);
    return ATOM(false);
}


static ERL_NIF_TERM varp_clear_queue(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    return ATOM(ok);
}

static ERL_NIF_TERM varp_enqueue_all(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int count;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    count = vp->q.size;
    return enif_make_int(env, count);
}

static ERL_NIF_TERM make_clause_info(ErlNifEnv* env, variable_t* v)
{
    return enif_make_tuple4(env,
			    enif_make_int(env, v->vix),
			    enif_make_int(env, v->value),
			    enif_make_int(env, v->literal_pos),
			    enif_make_int(env, v->implication_clause));
}


static ERL_NIF_TERM make_binding(ErlNifEnv* env, variable_t* v)
{
    return enif_make_tuple2(env,
			    enif_make_int(env, v->vix),
			    enif_make_int(env, v->value));
}


// get_bindings(Vp, Mark, ClauseInfo)
// Mark > 0  collect bindings until Mark = mark (not including)
// Mark < 0  collect bindings until number of marks N ( = -Mark )
// Mark == 0 get all bindings

static ERL_NIF_TERM varp_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM list;
    int level;
    int mark;
    int count = 0;
    int clause_info = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &mark))
	return enif_make_badarg(env);
    if (!get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    if (mark < 0)
	count = -mark;
    list = enif_make_list(env, 0);

    level = vp->level;
    while(level > 0) {
	variable_t* bp = vp->undo[level].bs;

	while(bp != NULL) {
	    ERL_NIF_TERM elem;
	    if (clause_info)
		elem = make_clause_info(env, bp);
	    else
		elem = make_binding(env, bp);
	    list = enif_make_list_cell(env, elem, list);
	    bp = bp->next;
	}
	    
	if (count) count--;
	if ((level == mark) || ((mark<0) && (count == 0)))
	    return list;
	level--;
    }
    return list;
}

// get_nbindings(Vp, Count, ClauseInfo)
// Count >= 0 get at most Count bindings
//
// returned list [{Var,Value}|{mark,Mark}]
// or            [{Var,Value,LiteralPos,ClauseIndex}|{mark,Mark}]
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
    while((level > 0) && count) {
	variable_t* bp = vp->undo[level].bs;

	while((bp != NULL) && count) {
	    ERL_NIF_TERM elem;
	    if (clause_info)
		elem = make_clause_info(env, bp);
	    else
		elem = make_binding(env, bp);
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
    LOAD_ATOM(bcp);
    LOAD_ATOM(qv);
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
    LOAD_ATOM(depth);
    LOAD_ATOM_STRING(plus_depth, "+depth");
    LOAD_ATOM_STRING(minus_depth, "-depth");
    
    // info
    LOAD_ATOM(max_clause_length);
    LOAD_ATOM(number_of_clauses);
    LOAD_ATOM(number_of_variables);
    LOAD_ATOM(number_of_bound_variables);
    LOAD_ATOM(number_of_unbound_variables);
    LOAD_ATOM(clause_eval_counter);
    LOAD_ATOM(eval_counter);
    LOAD_ATOM(undo_stack_size);
    LOAD_ATOM(value_stack_size);
    LOAD_ATOM(class_stack_size);
    LOAD_ATOM(mark);
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
