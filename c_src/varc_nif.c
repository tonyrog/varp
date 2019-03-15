//
// NIF library for managing variable classes
//

#ifdef __linux__
#define _GNU_SOURCE
#endif

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <unistd.h>
#include <memory.h>
#include <sys/time.h>
#include "erl_nif.h"

#include "bitset.h"

#define NDEBUG
#include <assert.h>

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

#define UNUSED(x) (void)(x)

static int varc_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varc_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
                         ERL_NIF_TERM load_info);
static void varc_unload(ErlNifEnv* env, void* priv_data);

static ERL_NIF_TERM varc_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varc_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_clause_flags(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_queue_first(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_queue_next(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_clear_queue(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_enqueue_all(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varc_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varc_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_put(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_is_variable(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_implication_clause(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_conflicting_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_is_equal(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_remove_mark(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_eval(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_order_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_order_sort_first(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_order_sort_last(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varc_add_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_find_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);

#define MAX_CLAUSE_LENGTH  MAX_BITSET_SIZE

#define DEFAULT_MAP_SIZE 1024
#define DEFAULT_MAP_GROW 1024

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

#define UNDEF 0
#define FALSE -1
#define TRUE  1

typedef enum {
    CLASS,
    VALUE,
    MARK
} undo_type_t;

typedef struct _undo_t {  /* : object_t */
    struct _undo_t* next; // MUST BE FIRST
    undo_type_t what;
    int x;                // variable | mark value
    int y;                // old value
} undo_t;

// maybe keep a separate mark stack?

#define OR_CLAUSE 0
#define OR_GATE   1
#define XOR_GATE  2

#define CLAUSE_FLAG_INQUEUE 0x0001
#define CLAUSE_FLAG_DEAD    0x0002

typedef struct _clause_t  /* : object_t */
{
    struct _clause_t* next;      // MUST BE FIRST
    unsigned asize;              // allocated size
    unsigned size;               // number of literals
    int      cix;                // clause index
    unsigned  key[1];            // sort values
    bitset_t mask_F;             // bit mask positions = FALSE
    bitset_t mask_T;             // bit mask positions = TRUE
    uint16_t flags;              // INQUEUE ...
    uint16_t op;                 // OR|XOR
    int      lit[0];
} clause_t;

// FIXME: maybe store multiple clause/pos per block?
typedef struct _varref_t  /* : object_t */
{
    struct _varref_t* next;   // MUST BE FIRST
    unsigned cix;             // clause index
    unsigned pos;             // literal position in clause
} varref_t;

#define VAR_FLAG_INQUEUE     0x01
#define VAR_FLAG_MARK        0x02

#define VAR_MARK_KEY  0
// sort keys are number 1 and 2

typedef struct _variable_t
{
    struct _variable_t* next; // variable list
    unsigned flags;      // VAR_FLAG_INQUEUE ...
    int value;           // current value
    int klass;           // class index
    int vix;             // variable index
    unsigned  key[3];    // sort keys
    varref_t* pref;      // reference list
    varref_t* nref;      // reference list
    int       map_index; // order_map index
    int       cix;       // implication clause, latest put
    int       li;        // position in implication clause
    int       mark;      // mark when set
    char* strname;            // string formated name or NULL
    struct _symbol_t* names;  // list of aliases    
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

typedef struct arc4_stream_t {
    uint8_t i;
    uint8_t j;
    uint8_t s[256];
} arc4_stream_t;

typedef struct _varc_t {
    unsigned int vnext;      // next free variable number
    unsigned int vsize;      // allocated size of value/class map
    unsigned int vnum;       // number of variables
    unsigned int cnext;      // next clause number
    unsigned int csize;      // allocated size of value/class map
    unsigned int cnum;       // number of clauses
    unsigned int ssize;       // size of symbol hash table
    unsigned int snum;        // number of symbols in symbol hash table    
    int bcp;                 // boolean constraint propagation
    int qv;                  // enqueue variables (instead of clauses)
    int mark;                // current mark
    int conflicting_clause;     // conflict clause from last eval
    unsigned int grow;        // how much to expand value/class map
    variable_t*  var_map;     // variable/class map
    symbol_t**   sym_map;     // symbol hash table    
    int*         order_map;   // variable order table
    int          sort_key[2]; // sort order -1,-2,1,2
    clause_t** clause_map;   // clause_map[v] = class chain of variable v
    undo_t*  undo_stack;     // undo stack
    unsigned int undo_stack_size;  // total size of undo stack
    unsigned int value_stack_size; // number of value bindings in undo stack
    unsigned int klass_stack_size; // number of class bindings in undo stack
    uint64_t  clause_eval_counter; // performance counter
    uint64_t  eval_counter;        // performance counter
    clause_t* eval_queue_hd; // eval queue head
    clause_t* eval_queue_tl; // eval queue tail
    variable_t* var_queue_hd; // var queue head
    variable_t* var_queue_tl; // var queue tail    

    arc4_stream_t as;        // random stream 

    allocator_t undo_allocator;
    allocator_t varref_allocator;
    allocator_t sym_allocator;     // heap storage for symbols
    allocator_t clause_allocator[33];
} varc_t;

// instance structure with variable elements
typedef struct _varc_var_t {  // NOT USED YET ...
    varc_t* base;

    clause_t* eval_queue_hd; // eval queue head
    clause_t* eval_queue_tl; // eval queue tail
    
    allocator_t undo_allocator;
    allocator_t varref_allocator;
} varc_var_t;

ErlNifResourceType* varc_res;

ErlNifFunc varc_funcs[] = 
{
    NIF_FUNC( "new",                 0,  varc_new ),
    NIF_FUNC( "new",                 1,  varc_new ),
    NIF_FUNC( "info",                2,  varc_info ),
    NIF_FUNC( "add_variable",        1,  varc_add_variable ),
    NIF_FUNC( "get",                 2,  varc_get ),
    NIF_FUNC( "put",                 3,  varc_put ),
    NIF_FUNC( "class",               2,  varc_class ),
    NIF_FUNC( "key",                 3,  varc_key ),
    NIF_FUNC( "implication_clause",  2,  varc_implication_clause ),
    NIF_FUNC( "conflicting_clause",     1,  varc_conflicting_clause ),
    NIF_FUNC( "is_variable",         2,  varc_is_variable ),
    NIF_FUNC( "is_bound",            2,  varc_is_bound ),
    NIF_FUNC( "class_next",          2,  varc_class_next ),
    NIF_FUNC( "is_equal",            3,  varc_is_equal ),
    NIF_FUNC( "mark",                2,  varc_mark ),
    NIF_FUNC( "remove_mark",         2,  varc_remove_mark ),
    NIF_FUNC( "undo",                1,  varc_undo ),
    NIF_FUNC( "undo",                2,  varc_undo ),
    NIF_FUNC( "eval",                1,  varc_eval ),
    NIF_FUNC( "add_clause",          3,  varc_add_clause ),
    NIF_FUNC( "add_clause",          4,  varc_add_clause ),
    NIF_FUNC( "add_clause",          5,  varc_add_clause ),
    NIF_FUNC( "add_clause",          6,  varc_add_clause ),
    NIF_FUNC( "add_clause",          7,  varc_add_clause ),
    NIF_FUNC( "add_clause",          8,  varc_add_clause ),
    NIF_FUNC( "get_clause",          2,  varc_get_clause ),
    NIF_FUNC( "get_clause_flags",    2,  varc_get_clause_flags ),
    NIF_FUNC( "del_clause",          2,  varc_del_clause ),
    NIF_FUNC( "get_clauses",         2,  varc_get_clauses ),
    NIF_FUNC( "get_queue_first",     1,  varc_get_queue_first ),
    NIF_FUNC( "get_queue_next",      2,  varc_get_queue_next ),    
    NIF_FUNC( "clear_queue",         1,  varc_clear_queue ),
    NIF_FUNC( "enqueue_all",         1,  varc_enqueue_all ),
    NIF_FUNC( "get_bindings",        3,  varc_get_bindings ),
    NIF_FUNC( "get_nbindings",       3,  varc_get_nbindings ),
    NIF_FUNC( "order_first",         1,  varc_order_first ),
    NIF_FUNC( "order_next",          3,  varc_order_next ),
    NIF_FUNC( "order_sort",          4,  varc_order_sort ),
    NIF_FUNC( "order_sort_first",    2,  varc_order_sort_first ),
    NIF_FUNC( "order_sort_last",     2,  varc_order_sort_last ),
    NIF_FUNC( "add_symbol",          3,  varc_add_symbol),
    NIF_FUNC( "get_symbol",          2,  varc_get_symbol ),
    NIF_FUNC( "find_symbol",         2,  varc_find_symbol ),
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
DECL_ATOM(flags);
DECL_ATOM(mask);
DECL_ATOM(undefined);
DECL_ATOM(identity);
DECL_ATOM(random);
DECL_ATOM(occur);
DECL_ATOM(occur_ascending);
DECL_ATOM(occur_descending);
DECL_ATOM(depth);
DECL_ATOM(depth_ascending);
DECL_ATOM(depth_descending);

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


static void* varc_alloc(allocator_t* ap)
{
    object_t* ptr;
    if ((ptr = ap->free_list) == NULL)
	return heap_alloc(&ap->heap_list, ap->size);
    ap->free_list = ptr->next;
    return ptr;
}

static void varc_free(allocator_t* ap, object_t* ptr)
{
    ptr->next = ap->free_list;
    ap->free_list = ptr;
}


static undo_t* undo_alloc(varc_t* vp)
{
    return varc_alloc(&vp->undo_allocator);
}

static void undo_free(varc_t* vp, undo_t* ptr)
{
    varc_free(&vp->undo_allocator, (object_t*) ptr);
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

uint32_t arc4_random_uniform(arc4_stream_t* as, uint32_t upper_bound)
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

static clause_t* clause_alloc(varc_t* vp, uint16_t op, int size)
{
    clause_t* cp;
    if (size < 2)
	return NULL;
    if (size > 32) {
	if ((cp = enif_alloc(sizeof(clause_t)*sizeof(int)*size)) == NULL)
	    return NULL;
    }
    else if ((cp = varc_alloc(&vp->clause_allocator[size])) == NULL)
	return NULL;

    cp->next = NULL;
    cp->asize = size;
    cp->size  = size;
    bitset_init(&cp->mask_F);
    bitset_init(&cp->mask_T);
    cp->flags = 0;
    cp->key[0] = 0;
    cp->op = op;
    return cp;
}

static void clause_free(varc_t* vp, clause_t* cp)
{
    if (cp->asize > 32)
	enif_free(cp);
    else
	varc_free(&vp->clause_allocator[cp->asize], (object_t*) cp);
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
static int is_bound(varc_t* vp, int x)
{
    return (vp->var_map[ABS(x)].value != UNDEF);
}

// Save binding on the undo stack
static undo_t* push(varc_t* vp, undo_type_t what, int x, int y)
{
    undo_t* up;

    up = undo_alloc(vp);
    up->what = what;
    up->x = x;
    up->y = y;
    up->next = vp->undo_stack;
    vp->undo_stack = up;
    vp->undo_stack_size++;
    return up;
}

// put clause on eval queue
static int enqueue_clause(varc_t* vp, clause_t* cp, int dead)
{
    TRACE("enqueue_clause %d T=%s F=%s flags=%x\r\n", 
	  cp->cix, bitset_format(&cp->mask_T), bitset_format(&cp->mask_F),
	  cp->flags);
    if (cp->flags & (CLAUSE_FLAG_INQUEUE|dead))
	return 0;
    cp->next = NULL;
    if (vp->eval_queue_tl == NULL)
	vp->eval_queue_hd = cp;
    else
	vp->eval_queue_tl->next = cp;
    vp->eval_queue_tl = cp;
    cp->flags |= CLAUSE_FLAG_INQUEUE;
    return 1;
}

static clause_t* dequeue_clause(varc_t* vp)
{
    clause_t* cp;

    if ((cp = vp->eval_queue_hd) != NULL) {
	if ((vp->eval_queue_hd = cp->next) == NULL)
	    vp->eval_queue_tl = NULL;
	cp->next = NULL;
	cp->flags &= ~CLAUSE_FLAG_INQUEUE;
	TRACE("dequeue_clause %d T=%s F=%s flags=%x\r\n", 
	      cp->cix, bitset_format(&cp->mask_T), bitset_format(&cp->mask_F),
	      cp->flags);
    }
    return cp;
}

static void init_variable(variable_t* vptr, int value, int klass, int vix)
{
    vptr->value = value;
    vptr->klass = klass;
    vptr->vix   = vix;
    vptr->key[0] = 0;
    vptr->key[1] = 0;
    vptr->key[2] = 0;
    vptr->pref = NULL;
    vptr->nref = NULL;
    vptr->map_index = vix;
    vptr->cix = -1;
    vptr->li = -1;
    vptr->mark = 0;
    vptr->next = NULL;
    vptr->flags = 0;
    vptr->strname = NULL;
}

static void clear_variable_queue(varc_t* vp)
{
    variable_t* vptr;

    vptr = vp->var_queue_hd;
    while(vptr) {
	variable_t* vptrn = vptr->next;
	vptr->next = NULL;
	vptr->flags &= ~VAR_FLAG_INQUEUE;
	vptr = vptrn;
    }
    vp->var_queue_hd = NULL;
    vp->var_queue_tl = NULL;
}

static int enqueue_variable(varc_t* vp, variable_t* vptr)
{
    if (vptr->flags & VAR_FLAG_INQUEUE)
	return 0;
    vptr->next = NULL;
    if (vp->var_queue_tl == NULL)
	vp->var_queue_hd = vptr;
    else
	vp->var_queue_tl->next = vptr;
    vp->var_queue_tl = vptr;
    vptr->flags |= VAR_FLAG_INQUEUE;
    return 1;
}

static variable_t* dequeue_variable(varc_t* vp)
{
    variable_t* vptr;

    if ((vptr = vp->var_queue_hd) != NULL) {
	if ((vp->var_queue_hd = vptr->next) == NULL)
	    vp->var_queue_tl = NULL;
	vptr->next = NULL;
	vptr->flags &= ~VAR_FLAG_INQUEUE;
    }
    return vptr;
}

static int enqueue_all_variables(varc_t* vp)
{
    int i;
    int count = 0;
    
    for (i = 2; i < (int)vp->vnext; i++) {
	variable_t* vptr;
	vptr = &vp->var_map[i];
	count += enqueue_variable(vp, vptr);
    }
    return count;
}


static void clear_clause_queue(varc_t* vp)
{
    clause_t* cp;

    cp = vp->eval_queue_hd;
    while(cp) {
	clause_t* cpn = cp->next;
	cp->next = NULL;
	cp->flags &= ~CLAUSE_FLAG_INQUEUE;
	cp = cpn;
    }
    vp->eval_queue_hd = NULL;
    vp->eval_queue_tl = NULL;
}

static int enqueue_all_clauses(varc_t* vp)
{
    int i;
    int count = 0;
    
    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp;
	if ((cp = vp->clause_map[i]) != NULL)
	    count += enqueue_clause(vp, cp, 0);
    }
    return count;
}

static void enqueue_varref(varc_t* vp,varref_t* vrp,int x,int y)
{
    while(vrp) {
	clause_t* cp = vp->clause_map[vrp->cix];
	unsigned pos = vrp->pos;
	int y1;
	assert(vrp->pos < MAX_CLAUSE_LENGTH);
	assert(x == abs(cp->lit[pos]));
	y1 = (x == -cp->lit[pos]) ? -y : y;
	TRACE("enqueue_varref: %d=%d clause=%d pos=%d\r\n",
	      x, y1, vrp->cix, pos);
	if (y1 == TRUE)
	    bitset_set(&cp->mask_T, &cp->mask_T, pos);
	else if (y1 == FALSE)
	    bitset_set(&cp->mask_F, &cp->mask_F, pos);
	enqueue_clause(vp,cp,CLAUSE_FLAG_DEAD);
	vrp = vrp->next;
    }
}

// enqueue all clauses that contains literal x
// or enqueue variable x if qv=true
static void enqueue_var(varc_t* vp,int x,int y)
{
    TRACE("enqueue_var %d=%d\r\n", x, y);
    while(x != 0) {
	variable_t* vptr;
	if (x < 0) { x = -x; y = -y; }
	vptr = &vp->var_map[x];
	if (vp->qv)
	    enqueue_variable(vp, vptr);
	else {
	    enqueue_varref(vp,vptr->pref,x,y);
	    enqueue_varref(vp,vptr->nref,x,y);
	}
	x = vp->var_map[x].klass;
    }
}

static void undo_clause(varc_t* vp,clause_t* cp)
{
    (void) vp;
    TRACE("undo_clause %d T=%s, F=%s\r\n", cp->cix,
	  bitset_format(&cp->mask_T), bitset_format(&cp->mask_F));
    cp->flags &= ~CLAUSE_FLAG_DEAD;
}

static void undo_varref(varc_t* vp,varref_t* vrp,int x,int y)
{
    while(vrp) {
	clause_t* cp = vp->clause_map[vrp->cix];
	unsigned pos = vrp->pos;
	assert(vrp->pos < MAX_CLAUSE_LENGTH);
	assert(x == abs(cp->lit[pos]));	
	int y1 = (x == -cp->lit[pos]) ? -y : y;
	if (y1 == TRUE)
	    bitset_clear(&cp->mask_T, &cp->mask_T, pos);
	else if (y1 == FALSE)
	    bitset_clear(&cp->mask_F, &cp->mask_F, pos);
	undo_clause(vp,cp);
	vrp = vrp->next;
    }
}

static void undo_var(varc_t* vp,int x,int y)
{
    TRACE("undo_var %d=%d\r\n", x, y);
    while(x != 0) {
	variable_t* vptr;
	if (x < 0) { x = -x; y = -y; }
	vptr = &vp->var_map[x];
	undo_varref(vp,vptr->pref,x,y);
	undo_varref(vp,vptr->nref,x,y);
	x = vp->var_map[x].klass;
    }
}

static int get(varc_t* vp, int x)
{
    variable_t* map = vp->var_map;
    int x0 = x;

    while(x != 0) {
	x0 = x;
	if (x0 < 0) {
	    if (x0 == FALSE)
		return FALSE;
	    x = -x0;
	    x = -map[x].value;
	}
	else {
	    if (x0 == TRUE)
		return TRUE;
	    x = map[x].value;
	}
    }
    return x0;
}

// FIXME make klass return fast if bcp is true or no classes
static int klass(varc_t* vp,int x)
{
    variable_t* map = vp->var_map;
    int x0 = x;

    while(x != 0) {
	x0 = x;
	if (x0 < 0) {
	    if (x0 == FALSE)
		return FALSE;
	    x = -x0;
	    x = -map[x].klass;
	}
	else {
	    if (x0 == TRUE)
		return TRUE;
	    x = map[x].klass;
	}
    }
    return x0;
}

static int put(varc_t* vp, int x, int y, int li, int cix)
{
    int yc;
    TRACE("%d = %d\r\n", x, y);
    x = get(vp, x);
    y = get(vp, y);
    if (x == -y) return -1; // contradictory
    if (x == y)  return 0;  // already equal

    // x and y can not both be literal
    if (is_constant(x)) { // make y the variable
	if (x < 0) { int t=-x; x=-y; y=t; }
	else { int t=x; x=y; y=t; }
    }
    else {
	if (x < 0) { x=-x; y=-y; }
    }
    // x is now a positive literal
    (void) push(vp, VALUE, x, vp->var_map[x].value);  // push old value of x
    vp->value_stack_size++;
    vp->var_map[x].cix = cix;
    vp->var_map[x].li  = li;
    vp->var_map[x].mark = vp->mark;
    
    enqueue_var(vp, x, y);
    vp->var_map[x].value = y;  // new value of x
    // if y is a literal then x and y classes are joined
    yc = klass(vp, y);
    if (yc < 0) {
	if (yc != FALSE) {
	    yc = -yc;
	    push(vp, CLASS, yc, vp->var_map[yc].klass);
	    vp->var_map[yc].klass = -x;
	    vp->klass_stack_size++;
	}
    }
    else {
	if (yc != TRUE) {
	    push(vp, CLASS, yc, vp->var_map[yc].klass);
	    vp->var_map[yc].klass = x;
	    vp->klass_stack_size++;
	}
    }
    return 0;
}

static int add_varref(varc_t* vp,int lit,clause_t* cp,unsigned pos)
{
    varref_t* vrp;
    variable_t* vptr;
    int val;

    val = get(vp, lit);

    if (val == TRUE)
	bitset_set(&cp->mask_T, &cp->mask_T, pos);
    else if (val == FALSE)
	bitset_set(&cp->mask_F, &cp->mask_F, pos);
    if ((vrp = varc_alloc(&vp->varref_allocator)) == NULL)  
	return -1;
    if (lit < 0) {
	vptr = &vp->var_map[-lit];
	vrp->next = vptr->nref;
	vptr->nref = vrp;
    }
    else {
	vptr = &vp->var_map[lit];
	vrp->next = vptr->pref;
	vptr->pref = vrp;
    }
    vrp->cix  = cp->cix;
    vrp->pos = pos;
    return 0;
}

// locate, unlink and free the variable reference
static int del_varref(varc_t* vp,varref_t** vrpp,unsigned clause,unsigned pos)
{
    varref_t* vrp;

    while((vrp = *vrpp)) {
	if ((vrp->cix == clause) && (vrp->pos == pos)) {
	    *vrpp = vrp->next;  // unlink
	    varc_free(&vp->varref_allocator, (object_t*) vrp);
	    return 0;
	}
	vrpp = &vrp->next;
    }
    return -1;
}


static int remove_clause_from_queue(varc_t* vp, clause_t* cp)
{
    if (cp->flags & CLAUSE_FLAG_INQUEUE) {
	clause_t** cpp = &vp->eval_queue_hd;
	clause_t* p;
	clause_t* lp = NULL;
	
	while((p = *cpp)) {
	    if (p == cp) {
		*cpp = cp->next;
		cp->next = NULL;
		cp->flags &= ~CLAUSE_FLAG_INQUEUE;
		if (p == vp->eval_queue_tl)
		    vp->eval_queue_tl = lp;
		return 0;
	    }
	    lp = p;
	    cpp = &p->next;
	}
    }
    return -1;
}


static int insert_clause(ErlNifEnv* env, varc_t* vp, clause_t* cp)
{
    (void) env;
    int cix = vp->cnext++;

    cp->cix = cix;

    enqueue_clause(vp,cp,0);

    if (vp->cnext == vp->csize) {
	unsigned int old_csize = vp->csize;
	unsigned int new_csize = old_csize + vp->grow;
	void* p;
	// expand
	if (!(p = enif_realloc(vp->clause_map, new_csize*sizeof(clause_t**))))
	    return -1;
	vp->clause_map = p;
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

static int get_literal(ErlNifEnv* env, varc_t* vp, ERL_NIF_TERM arg, int* xp)
{
    int x;

    if (!enif_get_int(env, arg, &x))
	return 0;
    if (x < 0) {
	if (-x >= (int)vp->vnext) return 0;
	*xp = x;
	return 1;
    }
    else if (x > 0) {
	if (x >= (int)vp->vnext) return 0;
	*xp = x;
	return 1;
    }
    else { // t == 0  => allow 0 as FALSE!
	*xp = FALSE;
	return 1;
    }
}

static int get_variable(ErlNifEnv* env, varc_t* vp, ERL_NIF_TERM arg,
			variable_t** vpp)
{
    int x;
    if (!get_literal(env, vp, arg, &x)) return 0;
    *vpp = &vp->var_map[(x < 0) ? -x : x];
    return 1;
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, int value)
{
    return enif_make_int(env, value);
}

//
// Utility to bind a literal to a value, assert that
// the setting does not fail!
//

#define PUTT(vp,x,y,i,t) do {					\
	if (put((vp),(x),(y),(i),(t)) < 0) return -1;		\
    } while(0)

//
// Return a bit mask representing the unbound literal positions
// unbound = ~(mask_T | mask_F)
//
static inline void unbound_literals(clause_t* cp, bitset_t* unbound)
{
    bitset_t x, y;
    bitset_union(&x, &cp->mask_T, &cp->mask_F);
    bitset_complement(&x, &x);
    bitset_fill(&y, cp->size);
    bitset_intersect(unbound, &x, &y);
}

//
// eval an OR clause using bitmasks mask_F and mask_T
// clause is TRUE = OR(x1,....,xn-1)
//
static int eval_or_clause(varc_t* vp, clause_t* cp)
{
    int i;

    TRACE("eval_or_gate %d T=%s F=%s\r\n", 
	  cp->cix, bitset_format(&cp->mask_T), bitset_format(&cp->mask_F));

    // the condition below should possibly be changed to
    // the condition cp->mask_T == 1, ony x0 is true
    if (bitset_is_nclear(&cp->mask_T,1,cp->size-1)) { // clause not dead
	bitset_t unbound;
	// simplify using unbound = ~mask_F & (1<<cp->size)?
	unbound_literals(cp, &unbound);
	TRACE(" lit[0]=T, unbound=%s\r\n", bitset_format(&unbound));
	if (bitset_single_pos(&unbound,&i)) {
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    PUTT(vp, cp->lit[i], TRUE, i, cp->cix);
	}
	else if (bitset_is_empty(&unbound)) {
	    if (bitset_is_nset(&cp->mask_F,1,cp->size-1))
		return -1;
	}
    }
    return 0;
}

//
// eval an OR clause using bitmasks mask_F and mask_T
// clause is x0 = OR(x1,....,xn-1)
//
static int eval_or_gate(varc_t* vp, clause_t* cp)
{
    int i;

    TRACE("eval_or_gate %d T=%s F=%s\r\n", 
	  cp->cix, bitset_format(&cp->mask_T), bitset_format(&cp->mask_F));

    if (bitset_is_set(&cp->mask_T,0)) {  // x0 == TRUE?
	// the condition below should possibly be changed to
	// the condition cp->mask_T == 1, ony x0 is true
	if (bitset_is_nclear(&cp->mask_T,1,cp->size-1)) { // clause not dead
	    bitset_t unbound;
	    // simplify using unbound = ~mask_F & (1<<cp->size)?
	    unbound_literals(cp, &unbound);
	    TRACE(" lit[0]=T, unbound=%s\r\n", bitset_format(&unbound));
	    if (bitset_single_pos(&unbound,&i)) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		PUTT(vp, cp->lit[i], TRUE, i, cp->cix);
	    }
	    else if (bitset_is_empty(&unbound)) {
		if (bitset_is_nset(&cp->mask_F,1,cp->size-1))
		    return -1;
	    }
	}
    }
    else if (bitset_is_set(&cp->mask_F,0)) { // x0 == FALSE?
	cp->flags |= CLAUSE_FLAG_DEAD;
	TRACE(" lit[i]=F%s\r\n", "");
	// LIGHTER version may set bitmask once and simplify enqueue_varref 
	for (i = 1; i < (int)cp->size; i++) {
	    PUTT(vp, cp->lit[i], FALSE, i, cp->cix);
	}
    }
    else {
	if (bitset_any(&cp->mask_T)) { // any of x1..xn is TRUE
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    TRACE(" lit[0]=T, some true%s\r\n", "");
	    PUTT(vp, cp->lit[0], TRUE, 0, cp->cix);
	}
	else if (bitset_is_nset(&cp->mask_F,1,cp->size-1)) { // x1..xn == FALSE
	    // could be written like (mask_F>>1)+1 == (1 << cp->size-1)
	    TRACE(" lit[0]=F, all false%s\r\n", "");
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    PUTT(vp, cp->lit[0], FALSE, 0, cp->cix);
	}
	else if (!vp->bcp) { // if all but one, xi, are false then x0=xi
	    // e.g  x0=0,x2,0  => x0=x2
	    bitset_t unbound;
	    unbound_literals(cp, &unbound);
	    bitset_clear(&unbound,&unbound,0);
	    if (bitset_single_pos(&unbound,&i)) {  // one of x1..xn is unbound
		cp->flags |= CLAUSE_FLAG_DEAD;
		PUTT(vp, cp->lit[0], cp->lit[i], 0, cp->cix);
	    }
	}
    }
    return 0;
}

//
// eval an XOR clause using bitmasks mask_F and mask_T
// clause is x0 = XOR(x1,....,xn-1)
//
// x0 = 1,0,1,0,xi,0,1,0  => x0=xi  (parity=0) x0=!xi (parity=1)
// 1 = 1,0,1,x1,0,1,x2    => x1=x2  (parity=1) x1=!x2 (parity=0)
// 0 = 1,0,1,x1,0,1,x2    => x1=!x2 (parity=1) x1=x2  (parity=0)
// 
static int eval_xor_gate(varc_t* vp, clause_t* cp)
{
    int i,j;

    TRACE("eval_xor_gate %d T=%s F=%s\r\n", 
	  cp->cix,  bitset_format(&cp->mask_T), bitset_format(&cp->mask_F));

    if (bitset_is_set(&cp->mask_T,0)) { // x0 = TRUE
	bitset_t unbound;
	unbound_literals(cp, &unbound);
	TRACE(" lit[0]=T, unbound=%s\r\n", bitset_format(&unbound));
	if (bitset_single_pos(&unbound, &i)) {
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (!bitset_parity(&cp->mask_T))  // x0 is counted
		PUTT(vp, cp->lit[i], FALSE, i, cp->cix);
	    else
		PUTT(vp, cp->lit[i], TRUE, i, cp->cix);
	}
	else if (bitset_is_empty(&unbound)) {
	    if (bitset_parity(&cp->mask_T))  // x0 is counted!!!
		return -1;
	}
	else if (!vp->bcp) {
	    if (bitset_pair_pos(&unbound, &i, &j)) {
		if (bitset_parity(&cp->mask_T)) // x0 is counted!!!
		    PUTT(vp, cp->lit[i], -cp->lit[j], i, cp->cix);
		else
		    PUTT(vp, cp->lit[i], cp->lit[j], i, cp->cix);
	    }
	}
    }
    else if (bitset_is_set(&cp->mask_F,0)) { // x0 = FALSE
	bitset_t unbound;
	unbound_literals(cp, &unbound);
	TRACE(" lit[0]=F, unbound=%s\r\n", bitset_format(&unbound));
	if (bitset_single_pos(&unbound,&i)) { // one unbound position
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (bitset_parity(&cp->mask_T))  // x0 is counted!!!
		PUTT(vp, cp->lit[i], TRUE, i, cp->cix);
	    else
		PUTT(vp, cp->lit[i], FALSE, i, cp->cix);
	}
	else if (bitset_is_empty(&unbound)) {
	    if (bitset_parity(&cp->mask_T))  // x0 is counted!!!
		return -1;
	}
	else if (!vp->bcp) {
	    if (bitset_pair_pos(&unbound, &i, &j)) {
		if (bitset_parity(&cp->mask_T))  // x0=0!
		    PUTT(vp, cp->lit[i], -cp->lit[j], i, cp->cix);
		else
		    PUTT(vp, cp->lit[i], cp->lit[j], i, cp->cix);
	    }
	}
    }
    else {
	bitset_t unbound;
	unbound_literals(cp, &unbound);
	TRACE(" lit[0]=X, unbound=%s\r\n", bitset_format(&unbound));
	bitset_clear(&unbound, &unbound, 0);
	if (bitset_is_empty(&unbound)) {     // x1,...,xn ALL bound
	    if (bitset_parity(&cp->mask_T))  // odd number of bits set
		PUTT(vp, cp->lit[0], TRUE, 0, cp->cix);
	    else
		PUTT(vp, cp->lit[0], FALSE, 0, cp->cix);
	}
	else if (!vp->bcp) {
	    if (bitset_single_pos(&unbound,&i)) { // one of x1..xn is unbound
		if (bitset_parity(&cp->mask_T))
		    PUTT(vp, cp->lit[0], -cp->lit[i], 0, cp->cix);
		else
		    PUTT(vp, cp->lit[0], cp->lit[i], 0, cp->cix);
	    }
	}
    }
    return 0;
}

static int eval_clause(varc_t* vp, clause_t* cp)
{
    vp->clause_eval_counter++;
    switch(cp->op) {
    case OR_CLAUSE: return eval_or_clause(vp, cp);	
    case OR_GATE:   return eval_or_gate(vp, cp);	
    case XOR_GATE:  return eval_xor_gate(vp, cp);
    default: return -1;
    }
}

static int eval_varref(varc_t* vp, varref_t* vref, int y)
{
    while(vref != NULL) {
	clause_t* cp = vp->clause_map[vref->cix];
	unsigned pos = vref->pos;
	assert(vref->pos < MAX_CLAUSE_LENGTH);
	assert(x == abs(cp->lit[pos]));
	if (y == TRUE)
	    bitset_set(&cp->mask_T, &cp->mask_T, pos);
	else if (y == FALSE)
	    bitset_set(&cp->mask_F, &cp->mask_F, pos);	

	if (cp->op == OR_CLAUSE) {
	    vp->clause_eval_counter++;
	    if (eval_or_clause(vp, cp) < 0) {
		vp->conflicting_clause = cp->cix;
		return -1;
	    }
	}
	else if (cp->op == OR_GATE) {
	    vp->clause_eval_counter++;
	    if (eval_or_gate(vp, cp) < 0) {
		vp->conflicting_clause = cp->cix;
		return -1;
	    }
	}
	else {
	    vp->clause_eval_counter++;
	    if (eval_xor_gate(vp, cp) < 0) {
		vp->conflicting_clause = cp->cix;
		return -1;
	    }
	}
	vref = vref->next;
    }
    return 0;
}

static int eval_variable(varc_t* vp, variable_t* vptr)
{
    int r = 0;
    // FIXME: loop over klass!
    if (vptr->value == FALSE)
	r = eval_varref(vp, vptr->pref, FALSE);
    else if (vptr->value == TRUE)
	r = eval_varref(vp, vptr->nref, TRUE);
    else if (vptr->value != UNDEF) {
	int value = get(vp, vptr->value);
	if (value == FALSE)
	    r = eval_varref(vp, vptr->pref, FALSE);
	else if (value == TRUE)
	    r = eval_varref(vp, vptr->nref, TRUE);
    }
    return r;
}


static void cleanup(varc_t* vp)
{
    int i;

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
	enif_free(vp->clause_map);
	vp->clause_map = NULL;
    }
    cleanup_allocator(&vp->undo_allocator);
    cleanup_allocator(&vp->varref_allocator);
    cleanup_allocator(&vp->sym_allocator);    
    for(i = 0; i <= 32; i++)
	cleanup_allocator(&vp->clause_allocator[i]);
}

static void varc_dtor(ErlNifEnv* env, void* obj)
{
    (void) env;
    TRACE("dtor called %s\r\n", "");
    cleanup((varc_t*) obj);
}

static ERL_NIF_TERM varc_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    unsigned int grow   = DEFAULT_MAP_GROW;
    unsigned int vsize  = DEFAULT_MAP_SIZE;
    unsigned int csize  = DEFAULT_MAP_SIZE;
    unsigned int ssize;    
    int bcp = 0;
    int qv = 0;
    ERL_NIF_TERM t;
    int i;

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
    
    if (!(vp = enif_alloc_resource(varc_res, sizeof(varc_t))))
	goto error;
    memset(vp, 0, sizeof(varc_t));

    vp->vnext = 2;
    vp->vsize = vsize;
    vp->vnum  = 0;

    vp->grow = grow;
    if (!(vp->var_map = enif_alloc(vsize*sizeof(variable_t))))
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
    vp->qv   = qv;

    if (!(vp->clause_map = enif_alloc(csize*sizeof(clause_t**))))
	goto error;
    if (init_allocator(&vp->undo_allocator, sizeof(undo_t)) < 0)
	goto error;
    if (init_allocator(&vp->varref_allocator, sizeof(varref_t)) < 0)
	goto error;
    if (init_allocator(&vp->sym_allocator, sizeof(symbol_t)) < 0)
	goto error;
    for (i = 0; i <= 32; i++) {
	if (init_allocator(&vp->clause_allocator[i],
			   sizeof(clause_t)+i*sizeof(int)) < 0)
	    goto error;
    }
    vp->undo_stack_size = 0;
    vp->value_stack_size = 0;
    vp->klass_stack_size = 0;
    vp->eval_counter = 0;
    vp->clause_eval_counter = 0;

    vp->order_map[0] = 0;
    init_variable(&vp->var_map[0], UNDEF, UNDEF, 0);
    vp->order_map[1] = 1;
    init_variable(&vp->var_map[1], 1, 1, 1);

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
static ERL_NIF_TERM varc_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    unsigned int vix;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);

    vix = vp->vnext++;
    if (vp->vnext == vp->vsize) {
	unsigned int old_vsize = vp->vsize;
	unsigned int new_vsize = old_vsize + vp->grow;
	variable_t* p;
	int* ip;
	// expand
	if (!(p = enif_realloc(vp->var_map, new_vsize*sizeof(variable_t))))
	    return enif_make_badarg(env);
	if (!(ip = enif_realloc(vp->order_map, new_vsize*sizeof(int))))
	    return enif_make_badarg(env);
	vp->var_map = p;
	vp->order_map = ip;
	vp->vsize = new_vsize;
    }
    vp->vnum++;
    vp->order_map[vix] = vix;
    init_variable(&vp->var_map[vix], UNDEF, UNDEF, vix);
    return enif_make_int(env, vix);
}


// varc:add_symbol(Vp:varc(),integer(),term()) -> ok | error
static ERL_NIF_TERM varc_add_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    variable_t* var;
    ErlNifBinary bin;
    uint32_t hash;
    int hix;
    int is_term = 0;
    symbol_t* sp;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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
    if ((sp = varc_alloc(&vp->sym_allocator)) == NULL)
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

// varc:get_variable_name(Vp:varc(),integer()) -> term().
static ERL_NIF_TERM varc_get_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    variable_t* var;
    symbol_t* sp;
    ERL_NIF_TERM list;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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
static ERL_NIF_TERM varc_find_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);    
    varc_t* vp;
    ErlNifBinary bin;
    uint32_t hash;    
    int hix;
    int is_term = 0;
    symbol_t* sp;    
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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

static ERL_NIF_TERM varc_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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
static ERL_NIF_TERM varc_order_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    int i;
    int skip;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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
static int order_reset(varc_t* vp)
{
    int i, u, b;

    vp->order_map[0] = 0;
    vp->var_map[0].map_index = 0;
    vp->order_map[1] = 1;
    vp->var_map[1].map_index = 1;
    b = 1;
    u = vp->vnext;

    for (i = 2; i < (int)vp->vnext; i++) {
	if (is_bound(vp, i)) {
	    b++;
	    vp->order_map[b] = i;
	    vp->var_map[i].map_index = b; 
	}
	else {
	    u--;
	    vp->order_map[u] = i;
	    vp->var_map[i].map_index = u;
	}
    }
    return u;
}


static void order_k_identity(varc_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i].key[k] = i;
    }
}

static void order_k_random(varc_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i].key[k] = arc4_random_uniform(&vp->as, 0x7fffffff);
    }
}

static void order_k_undefined(varc_t* vp, int k)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i].key[k] = 0;
    }
}

// scan through all variables and calculate the occur count, key[k]
static void order_k_occur(varc_t* vp, int k)
{
    int i;
    
    for (i = 2; i < (int)vp->vnext; i++)
	vp->var_map[i].key[k] = 0;

    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	if (cp != NULL) {
	    int j;
	    for (j = 0; j < (int)cp->size; j++) {
		int x = get(vp, cp->lit[j]);
		if (x < 1)
		    vp->var_map[-x].key[k]++;
		else if (x > 1)
		    vp->var_map[x].key[k]++;
	    }
	}
    }
}

static void depth_varref(varc_t* vp, varref_t* rp, int k)
{
    while(rp) {
	if (rp->pos > 0) {
	    clause_t* cp = vp->clause_map[rp->cix];
	    cp->key[0]++;
	    if (cp->key[0]+1 == cp->size) {
		int y = ABS(cp->lit[0]);  // output
		if (y > 1) {
		    int depth = 0;
		    int i;
		    for (i = 1; i < (int)cp->size; i++) {
			int x = ABS(cp->lit[i]);
			if (x > 1) {
			    int d = vp->var_map[x].key[k];
			    if (d > depth)
				depth = d;
			}
		    }
		    vp->var_map[y].key[k] = depth+1;
		    // printf("var %d depth=%d\r\n", y,
		    //  vp->var_map[y].key[VAR_DEPTH_KEY]);
		    enqueue_variable(vp, &vp->var_map[y]);
		}
	    }
	}
	rp = rp->next;
    }
}


static void order_k_depth(varc_t* vp, int k)
{
    int i;
    variable_t* vptr;
    
    clear_variable_queue(vp);  // maybe warn if not empty?
    
    for (i = 2; i < (int)vp->vnext; i++) {
	vp->var_map[i].key[k] = 0;
	vp->var_map[i].key[VAR_MARK_KEY] = 0;
    }

    // mark all output variables & clear clause key
    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp;
	if ((cp = vp->clause_map[i]) != NULL) {
	    int j;
	    int x = ABS(cp->lit[0]);
	    cp->key[0] = 0;  // input edge counter
	    if (x > 1)
		vp->var_map[x].key[VAR_MARK_KEY] = 1;
	    for (j = 1; j < (int)cp->size; j++) {
		if (ABS(cp->lit[j]) == 1)  // calculate constants here!
		    cp->key[0]++;
	    }
	}
    }

    // set all unmarked variables to depth=1 and enqueue them
    for (i = 2; i < (int)vp->vnext; i++) {
	if (vp->var_map[i].key[VAR_MARK_KEY] == 0) {
	    vp->var_map[i].key[k] = 1;
	    // printf("var %d depth=%d\r\n", i, vp->var_map[i].key[VAR_DEPTH_KEY]);
	    enqueue_variable(vp, &vp->var_map[i]);
	}
    }

    // each variable in the queue calc depth on output 

    while((vptr = dequeue_variable(vp)) != NULL) {
	depth_varref(vp, vptr->pref, k);
	depth_varref(vp, vptr->nref, k);
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
    varc_t* vp = (varc_t*) arg;
    int k1 = vp->sort_key[0];
    int k2 = vp->sort_key[1];
    variable_t* ap = &vp->var_map[*((int*)a)];
    variable_t* bp = &vp->var_map[*((int*)b)];
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

static ERL_NIF_TERM varc_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    int arg = 0;
    int u;
    int i;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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
	else if ((argv[i] == ATOM(occur)) ||
		 (argv[i] == ATOM(occur_ascending))) {
	    order_k_occur(vp, k);
	}
	else if (argv[i] == ATOM(occur_descending)) {
	    order_k_occur(vp, k);
	    k = -k;
	}
	else if ((argv[i] == ATOM(depth)) ||
		 (argv[i] == ATOM(depth_ascending))) {
	    order_k_depth(vp, k);
	}
	else if (argv[i] == ATOM(depth_descending)) {
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
	vp->var_map[v].map_index = i;
    }
    return ATOM(ok);
}

// move the list of variables first among the unbound variables
// and keep the order of the other variables.
// this is done through by copy the various part into a new
// array.
static ERL_NIF_TERM varc_order_sort_first(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;
    int* map;
    unsigned int i, ui, mi;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);

    // validate list
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	int x;
	if (!get_literal(env, vp, head, &x) || is_constant(x))
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    if (!(map = enif_alloc(vp->vsize*sizeof(int))))
	return enif_make_badarg(env);

    // clear moved mark
    for (i = 0; i < vp->vnext; i++)
	vp->var_map[i].flags &= ~VAR_FLAG_MARK;

    map[0] = 0;
    vp->var_map[0].flags |= VAR_FLAG_MARK;
    map[1] = 1;
    vp->var_map[1].flags |= VAR_FLAG_MARK;
    mi = 2;
    // copy all bound variables
    while ((mi < vp->vnext) && is_bound(vp, vp->order_map[mi])) {
	int x = vp->order_map[mi];
	vp->var_map[x].flags |= VAR_FLAG_MARK;
	map[mi++] = x;
    }
    ui = mi;  // save the position for the first unbound variabel
    // copy/move variables in the list (not already copied)
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	int x;
	if (!get_literal(env, vp, head, &x) || is_constant(x))
	    return enif_make_badarg(env);
	if (x < 0) x = -x;
	if (!(vp->var_map[x].flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[x].flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[x].map_index = mi;
	    map[mi++] = x;
	}
	list = tail;
    }
    // move rest of the varaibles not already moved
    while(ui < vp->vnext) {
	int x = vp->order_map[ui];
	if (!(vp->var_map[x].flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[x].flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[x].map_index = mi;
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

static ERL_NIF_TERM varc_order_sort_last(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;
    int* map;
    unsigned int i, ui, mi;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);

    // validate list
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	int x;
	if (!get_literal(env, vp, head, &x) || is_constant(x))
	    return enif_make_badarg(env);
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);

    if (!(map = enif_alloc(vp->vsize*sizeof(int))))
	return enif_make_badarg(env);

    // clear moved mark
    for (i = 0; i < vp->vnext; i++)
	vp->var_map[i].flags &= ~VAR_FLAG_MARK;

    map[0] = 0;
    vp->var_map[0].flags |= VAR_FLAG_MARK;
    map[1] = 1;
    vp->var_map[1].flags |= VAR_FLAG_MARK;
    mi = 2;
    // copy all bound variables
    while ((mi < vp->vnext) && is_bound(vp, vp->order_map[mi])) {
	int x = vp->order_map[mi];
	vp->var_map[x].flags |= VAR_FLAG_MARK;
	map[mi++] = x;
    }
    ui = mi;  // save the position for the first unbound variabel
    mi = vp->vnext;  // last position(+1)
    // copy/move variables in the list (not already copied)
    list = argv[1];
    while (enif_get_list_cell(env, list, &head, &tail)) {
	int x;
	if (!get_literal(env, vp, head, &x) || is_constant(x))
	    return enif_make_badarg(env);
	if (x < 0) x = -x;
	if (!(vp->var_map[x].flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[x].flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[x].map_index = --mi;
	    map[mi] = x;
	}
	list = tail;
    }

    mi = ui;
    // move rest of the varaibles not already moved
    while(ui < vp->vnext) {
	int x = vp->order_map[ui];
	if (!(vp->var_map[x].flags & VAR_FLAG_MARK)) { // not moved
	    vp->var_map[x].flags |= VAR_FLAG_MARK;     // mark as moved
	    vp->var_map[x].map_index = mi;
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
static ERL_NIF_TERM varc_get(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (!(x = get(vp, x)))
	return enif_make_badarg(env);
    return make_literal(env, x);
}

static ERL_NIF_TERM varc_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (!(x = klass(vp, x)))
	return enif_make_badarg(env);
    return enif_make_int(env, x);
}

static ERL_NIF_TERM varc_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    int ix, lit;
    int k;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &lit))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &k))
	return enif_make_badarg(env);
    if ((k < 0) || (k > 2))
	return enif_make_badarg(env);
    ix = (lit < 1) ? -lit : lit;
    return enif_make_int(env, vp->var_map[ix].key[k]);
}

// retrieve implication clause
// return {ClauseIndex, LiteralPosition, Mark}
static ERL_NIF_TERM varc_implication_clause(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    variable_t* var;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_variable(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return enif_make_tuple3(env,
			    enif_make_int(env, var->cix),
			    enif_make_int(env, var->li),
			    enif_make_int(env, var->mark));
}

static ERL_NIF_TERM varc_is_variable(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    int x;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    return make_boolean(env, is_literal(x));
}

static ERL_NIF_TERM varc_conflicting_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->conflicting_clause);
}

static ERL_NIF_TERM varc_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    int x;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    return make_boolean(env,is_bound(vp,x));
}

static ERL_NIF_TERM varc_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (x < 0)
	return enif_make_int(env, -vp->var_map[-x].klass);
    else
	return enif_make_int(env, vp->var_map[x].klass);
}


static ERL_NIF_TERM varc_is_equal(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    int x, y;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[2], &y))
	return enif_make_badarg(env);
    if (!(x = get(vp, x)))
	return enif_make_badarg(env);
    if (!(y = get(vp, y)))
	return enif_make_badarg(env);
    return make_boolean(env, (x == y));
}

//
// Set value X = 1, X = -1
// or make associate variables
// X = Y, X = -Y
//
static ERL_NIF_TERM varc_put(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    int x, y;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[2], &y))
	return enif_make_badarg(env);
    if (vp->bcp && !is_constant(y))
	return enif_make_badarg(env);
    if (put(vp, x, y, -1, -1) < 0)
	return ATOM(false);
    return ATOM(true);
}

static ERL_NIF_TERM varc_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    unsigned int mark;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &mark) || (mark == 0))
	return enif_make_badarg(env);
    push(vp, MARK, mark, vp->mark);  // push mark and save old mark!
    vp->mark = mark;  // set current mark
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
static ERL_NIF_TERM varc_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    undo_t* up;
    int mark;
    int count = 0;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (argc == 1)
	mark = 0;
    else {
	if (!enif_get_int(env, argv[1], &mark))
	    return enif_make_badarg(env);
    }
    if (mark < 0)
	count = -mark;

    // find the mark - improve by link marks or separate mark stack?
    if ((count == 0) && (mark != 0)) {
	up = vp->undo_stack;
	while(up != NULL) {
	    if ((up->what == MARK) && (up->x == mark))
		goto found;
	    up = up->next;
	}
	// mark not found!
	return enif_make_badarg(env);
    }
found:
    up = vp->undo_stack;
    while(up != NULL) {
	int x, y;
	undo_type_t w;
	undo_t* un;
	
	x = up->x;
	y = up->y;
	w = up->what;
	un = up->next;
	undo_free(vp,up);
	up = un;
	vp->undo_stack_size--;
	switch(w) {
	case VALUE:
	    undo_var(vp,x,vp->var_map[x].value);
	    vp->var_map[x].value = y;
	    vp->value_stack_size--;
	    break;
	case CLASS:
	    vp->var_map[x].klass = y;
	    vp->klass_stack_size--;
	    break;
	case MARK:
	    if (count) count--;
	    if ((x == mark) || ((mark<0) && (count == 0))) {
		vp->undo_stack = up;
		vp->mark = y; // y is the previous mark !
		return enif_make_int(env, x);
	    }
	    break;
	default:
	    break;
	}
    }
    vp->undo_stack = up;
    vp->mark = 0;
    return enif_make_int(env, 0);
}

//
// remove a mark, leave bindings intact
// or remove count(-mark) number of marks
//
static ERL_NIF_TERM varc_remove_mark(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    undo_t* up;
    undo_t** upp;
    int mark;
    int count = 0;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &mark))
	return enif_make_badarg(env);
    if (mark < 0)
	count = -mark;

    upp = &vp->undo_stack;
    while((up = *upp) != NULL) {
	if (up->what == MARK) {
	    if (up->x == mark) {
		*upp = up->next;
		undo_free(vp,up);
		vp->undo_stack_size--;
		return enif_make_int(env, mark);
	    }
	    else if (mark < 0) {
		int x = up->x;
		*upp = up->next;
		undo_free(vp,up);
		vp->undo_stack_size--;
		count--;
		if (count == 0)
		    return enif_make_int(env, x);
	    }
	}
	else {
	    upp = &up->next;
	}
    }
    return ATOM(false);
}

// eval:
//  return false  when conflict is found
//         true   when no conflict is found
//         more   when eval must be run again
//
static ERL_NIF_TERM varc_eval(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);

    vp->eval_counter++;
    vp->conflicting_clause = -1;
    if (vp->qv) {
	variable_t* vptr;
	while((vptr = dequeue_variable(vp)) != NULL) {
	    if (eval_variable(vp, vptr) < 0) {
		clear_variable_queue(vp);
		return ATOM(false);  // contradiction
	    }
	}
    }
    else {
	clause_t* cp;
	while((cp = dequeue_clause(vp)) != NULL) {
	    if (eval_clause(vp, cp) < 0) {
		vp->conflicting_clause = cp->cix;
		clear_clause_queue(vp);
		return ATOM(false);  // contradiction
	    }
	    // FIXME: check if we must pause the eval loop
	}
    }
    return ATOM(true);
}


// get information
static ERL_NIF_TERM varc_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
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
	return enif_make_int(env, vp->value_stack_size);
    }
    else if (argv[1] == ATOM(number_of_unbound_variables)) {
	return enif_make_int(env, vp->vnum - vp->value_stack_size);
    }
    else if (argv[1] == ATOM(clause_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter);
    }
    else if (argv[1] == ATOM(eval_counter)) {
	return enif_make_uint64(env, vp->eval_counter);
    }
    else if (argv[1] == ATOM(undo_stack_size)) {
	return enif_make_uint64(env, vp->undo_stack_size);
    }
    else if (argv[1] == ATOM(value_stack_size)) {
	return enif_make_uint64(env, vp->value_stack_size);
    }
    else if (argv[1] == ATOM(class_stack_size)) {
	return enif_make_uint64(env, vp->klass_stack_size);
    }
    else if (argv[1] == ATOM(bcp)) {
	return make_boolean(env, vp->bcp);
    }
    else if (argv[1] == ATOM(qv)) {
	return make_boolean(env, vp->qv);
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
static int cmp_rev_abs_lit QSORT_R_ARGS(const void* a, const void* b,void* arg)
{
    (void) arg;
    int r = abs(*(int*)b) - abs(*(int*)a);
    if (r == 0)
	r = *(int*)b - *(int*)a;
    return r;
}


void print_lit(char* label, int* literal, size_t size)
{
    if (size == 0)
	printf("%s={}", label);
    else {
	unsigned k;
	printf("%s={%d", label, literal[0]);
	for (k=1; k<size; k++)
	    printf(",%d",literal[k]);
	printf("}\r\n");
    }
}

// #define PRINT_LIT(msg,lit,size) print_lit((msg),(lit),(size))
#define PRINT_LIT(msg,lit,size)

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

static ERL_NIF_TERM add_clause_array(ErlNifEnv* env, varc_t* vp, int op,
				     int* literal, size_t size)
{
    clause_t* cp;
    int cix;
    unsigned i;
    unsigned Tc=0, Fc=0;

    PRINT_LIT("   src", literal, size);
    
    // first sort all literals by absolute value
    QSORT_R(literal+1, size-1, sizeof(int), cmp_rev_abs_lit, vp);

    PRINT_LIT(" sorted", literal, size);

    // remove FALSE literals
    i = size-1;
    while((i > 0) && (literal[i] == FALSE)) { i--; size--; Fc++; }
    PRINT_LIT("  del-F", literal, size);

    // remove TRUE literals
    while((i > 0) && (literal[i] == TRUE)) { i--; size--; Tc++; }
    PRINT_LIT("  del-T", literal, size);

    // remove duplicates
    if (op == OR_GATE) {
	unsigned u=1,v=1,w=1;
	while(v < size) {
	    while((w < size) && (literal[v] == literal[w])) w++;
	    if ((u > 1) && (literal[u-1] == -literal[v])) { // OR A -A => T
		u--;
		Tc++;
	    }
	    else
		literal[u++] = literal[v];
	    v = w;
	}
	size = u;
    }
    else {
	unsigned u=1,v=1,w=1;
	while(v < size) {
	    while((w < size) && (literal[v] == literal[w])) w++;
	    if ((w-v) & 1) { // odd number of duplicates save one
		if ((u > 1) && (literal[u-1] == -literal[v])) { // XOR A -A => T
		    u--;
		    Tc++;
		}
		else
		    literal[u++] = literal[v];
	    }
	    else {  // even number of duplicates => FALSE
		Fc++;
	    }
	    v = w;
	}
	size = u;
    }

    PRINT_LIT("del-dup", literal, size);


    if (op == OR_GATE) {
	if (size == 1) {
	    if ((Tc==0) && (Fc>0)) 
		literal[size++] = FALSE;
	}
	if (Tc>0) // add the T constant to the gate
	    literal[size++] = TRUE;
	if (literal[0] == TRUE)
	    op = OR_CLAUSE;  // it is a clause
    }
    else {  // XOR
	if (size == 1) {
	    if ((Tc==0) && (Fc>0))
		literal[size++] = FALSE;
	    else if (Tc>0)
		literal[size++] = (Tc & 1) ? TRUE : FALSE;
	}
	else if (Tc & 1) // T = XOR(X4,X3,X2) => T = XOR(-X4,X3,X2)
	    literal[0] = -literal[0];
    }
    PRINT_LIT("   dest", literal, size);
    
    if ((cp = clause_alloc(vp, op, size)) == NULL)
	return enif_make_badarg(env);
    if ((cix = insert_clause(env, vp, cp)) < 0)
	return enif_make_badarg(env);

    for (i = 0; i < size; i++) {
	cp->lit[i] = literal[i];
	if (abs(literal[i]) > 1) {
	    if (add_varref(vp, literal[i], cp, i) < 0)
		return enif_make_badarg(env);
	}
	else if (literal[i] == FALSE)
	    bitset_set(&cp->mask_F, &cp->mask_F, i);
	else if (literal[i] == TRUE)
	    bitset_set(&cp->mask_T, &cp->mask_T, i);
    }
    cp->size = size;
    return enif_make_int(env, cix);
}

//
// add_clause(vp, 'or',  x1, ..., xn)
// add_clause(vp, 'xor', x1, ..., xn)
// add_clause(vp, 'or'|'xor', [x1, ..., xn])
//
static ERL_NIF_TERM varc_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    int op;
    varc_t* vp;
    int size = 0;
    int literal[MAX_CLAUSE_LENGTH];

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);

    if (argv[1] == ATOM(or)) op = OR_GATE;
    else if (argv[1] == ATOM(xor)) op = XOR_GATE;
    else return enif_make_badarg(env);

    
    if (argc == 3) {   // argv[2] is a list of literals
	ERL_NIF_TERM list = argv[2];
	ERL_NIF_TERM head, tail;

	while(enif_get_list_cell(env, list, &head, &tail)) {
	    int x;
	    if (!get_literal(env, vp, head, &x))
		return enif_make_badarg(env);
	    if (size < MAX_CLAUSE_LENGTH)
		literal[size] = x;
	    size++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
    }
    else {
	int j;
	for (j = 2; j < argc; j++) {
	    int x;
	    if (!get_literal(env, vp, argv[j], &x))
		return enif_make_badarg(env);
	    if (size < MAX_CLAUSE_LENGTH)
		literal[size] = x;
	    size++;
	}
    }
    if ((size < 2) || (size > MAX_CLAUSE_LENGTH))
	return enif_make_badarg(env);
    return add_clause_array(env, vp, op, literal, size);
}

static ERL_NIF_TERM varc_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    unsigned int cix;
    clause_t* cp;
    int i;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    if (cix >= vp->cnext)
	return enif_make_badarg(env);
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);

    // remove all varrefs
    for (i = 0; i < (int)cp->size; i++) {
	int lit = cp->lit[i];
	if ((lit != TRUE) && (lit != FALSE)) {
	    if (lit < 0) {
		del_varref(vp,&vp->var_map[-lit].nref,cix,i);
	    }
	    else {
		del_varref(vp,&vp->var_map[lit].pref,cix,i);
	    }
	}
    }
    remove_clause_from_queue(vp, cp);
    clause_free(vp, cp);
    vp->clause_map[cix] = NULL;  // FIXME! reuse this position 
    vp->cnum--;
    return ATOM(ok);
}

static ERL_NIF_TERM varc_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varc_t* vp;
    unsigned int cix;
    ERL_NIF_TERM list;
    ERL_NIF_TERM op;
    int i;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    if (cix >= vp->cnext)
	return enif_make_badarg(env);
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);

    list = enif_make_list(env, 0);
    for (i = cp->size-1; i >= 0; i--) {
	ERL_NIF_TERM elem = make_literal(env, cp->lit[i]);
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

static ERL_NIF_TERM varc_get_clause_flags(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varc_t* vp;
    unsigned int cix;
    ERL_NIF_TERM list;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
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
    if (cp->flags & CLAUSE_FLAG_DEAD)
	list = enif_make_list_cell(env, ATOM(dead), list);
    return list;
}

static ERL_NIF_TERM build_varref_list(ErlNifEnv* env, varref_t* vrp,
				      ERL_NIF_TERM list)
{
    while(vrp) {
	ERL_NIF_TERM elem = enif_make_uint(env, vrp->cix);
	list = enif_make_list_cell(env, elem, list);
	vrp = vrp->next;
    }
    return list;
}


static ERL_NIF_TERM varc_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    int lit, ix;
    ERL_NIF_TERM list;
    variable_t* vptr;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &lit))
	return enif_make_badarg(env);
    ix = (lit < 0) ? -lit : lit;
    list = enif_make_list(env, 0);
    vptr = &vp->var_map[ix];
    list = build_varref_list(env,vptr->pref,list);
    list = build_varref_list(env,vptr->nref,list);
    return list;
}

// Get index to the first clause in queue
static ERL_NIF_TERM varc_get_queue_first(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    clause_t* cp;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);    
    if ((cp = vp->eval_queue_hd) != NULL)
	return enif_make_int(env, cp->cix);
    return ATOM(false);
}

static ERL_NIF_TERM varc_get_queue_next(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    clause_t* cp;
    int cix;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &cix))
	return enif_make_badarg(env);
    if ((cix < 0) || (cix >= (int)vp->cnum))
	return enif_make_badarg(env);
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);
    if ((cp = cp->next) != NULL)
	return enif_make_int(env, cp->cix);
    return ATOM(false);
}


static ERL_NIF_TERM varc_clear_queue(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (vp->qv)
	clear_variable_queue(vp);
    else
	clear_clause_queue(vp);
    return ATOM(ok);
}

static ERL_NIF_TERM varc_enqueue_all(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    int count;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (vp->qv)
	count = enqueue_all_variables(vp);
    else
	count = enqueue_all_clauses(vp);
    return enif_make_int(env, count);
}


// get_bindings(Vp, Mark, ClauseInfo)
// Mark >=   collect bindings until Mark = mark (not including)
// Mark < 0  collect bindings until number of marks N ( = -Mark )
// Mark == 0 latest binding

static ERL_NIF_TERM varc_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    ERL_NIF_TERM list;
    undo_t* up;
    int mark;
    int count = 0;
    int clause_info = 0;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &mark))
	return enif_make_badarg(env);
    if (!get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    if (mark < 0)
	count = -mark;
    list = enif_make_list(env, 0);
    up = vp->undo_stack;
    while(up) {
	ERL_NIF_TERM elem;
	int value;
	switch(up->what) {
	case VALUE:
	    value = get(vp, up->x);
	    if (clause_info) {
		int li = vp->var_map[up->x].li;
		int cix = vp->var_map[up->x].cix;
		elem = enif_make_tuple4(env,
					enif_make_int(env, up->x),
					make_literal(env, value),
					enif_make_int(env, li),
					enif_make_int(env, cix));
	    }
	    else {
		elem = enif_make_tuple2(env,
					enif_make_int(env, up->x),
					make_literal(env, value));
	    }
	    if (mark == 0)
		return elem;
	    list = enif_make_list_cell(env, elem, list);
	    break;
	case CLASS:
	    break;
	case MARK:
	    if (count) count--;
	    if ((up->x == mark) || ((mark<0) && (count == 0)))
		return list;
	    break;
	default:
	    break;
	}
	up = up->next;
    }
    return list;
}

// get_nbindings(Vp, Count, ClauseInfo)
// Count >= 0 get at most Count bindings
//
// returned list [{Var,Value}|{mark,Mark}]
// or            [{Var,Value,LiteralPos,ClauseIndex}|{mark,Mark}]
//
static ERL_NIF_TERM varc_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varc_t* vp;
    ERL_NIF_TERM list;
    undo_t* up;
    int count = 0;
    int clause_info = 0;
    
    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &count) || (count < 0))
	return enif_make_badarg(env);
    if (!get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    
    list = enif_make_list(env, 0);
    up = vp->undo_stack;
    while(up && count) {
	ERL_NIF_TERM elem;
	int value;
	switch(up->what) {
	case VALUE:
	    value = get(vp, up->x);
	    if (clause_info) {
		int li = vp->var_map[up->x].li;
		int cix = vp->var_map[up->x].cix;
		elem = enif_make_tuple4(env,
					enif_make_int(env, up->x),
					make_literal(env, value),
					enif_make_int(env, li),
					enif_make_int(env, cix));
	    }
	    else {
		elem = enif_make_tuple2(env,
					enif_make_int(env, up->x),
					make_literal(env, value));
	    }
	    list = enif_make_list_cell(env, elem, list);
	    count--;
	    break;
	case CLASS:
	    break;
	case MARK:
	    elem = enif_make_tuple2(env, ATOM(mark),
				    enif_make_int(env,up->x));
	    list = enif_make_list_cell(env, elem, list);
	    break;
	default:
	    break;
	}
	up = up->next;
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
    LOAD_ATOM(flags);
    LOAD_ATOM(mask);
    LOAD_ATOM(identity);
    LOAD_ATOM(random);
    LOAD_ATOM(occur);
    LOAD_ATOM_STRING(occur_ascending, "+occur");
    LOAD_ATOM_STRING(occur_descending,"-occur");
    LOAD_ATOM(depth);
    LOAD_ATOM_STRING(depth_ascending, "+depth");
    LOAD_ATOM_STRING(depth_descending, "-depth");
    
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


static int varc_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    UNUSED(env);
    UNUSED(load_info);

    // Create resource types
    varc_res = enif_open_resource_type(env, 0, "varc", varc_dtor,
				       ERL_NIF_RT_CREATE, &tried);
    load_atoms(env);
    *priv_data = 0;
    return 0;
}

static int varc_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
			ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    UNUSED(load_info);

    varc_res = enif_open_resource_type(env, 0, "varc", varc_dtor,
				       ERL_NIF_RT_CREATE | ERL_NIF_RT_TAKEOVER,
				       &tried);
    load_atoms(env);

    *priv_data = *old_priv_data;
    return 0;
}

static void varc_unload(ErlNifEnv* env, void* priv_data)
{
    UNUSED(env);
    UNUSED(priv_data);
}

ERL_NIF_INIT(varc, varc_funcs,
	     varc_load, NULL,
	     varc_upgrade, varc_unload)

