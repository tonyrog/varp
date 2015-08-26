//
// NIF library for managing variable classes
//
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <memory.h>
#include <sys/time.h>
#include "erl_nif.h"

#if (ERL_NIF_MAJOR_VERSION > 2) || ((ERL_NIF_MAJOR_VERSION == 2) && (ERL_NIF_MINOR_VERSION >= 7))
#define NIF_FUNC(name,arity,fptr) {(name),(arity),(fptr),(0)}
#else
#define NIF_FUNC(name,arity,fptr) {(name),(arity),(fptr)}
#endif


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
static ERL_NIF_TERM varc_get_queue(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_clear_queue(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varc_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_number_of_variables(ErlNifEnv* env, int argc,
					     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_get_number_of_clauses(ErlNifEnv* env, int argc,
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
static ERL_NIF_TERM varc_occure(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_equal(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_mark(ErlNifEnv* env, int argc,
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

#define DEFAULT_MAP_SIZE   1024
#define DEFAULT_MAP_EXPAND 1024

#define MAX_MAP_SIZE       (1024*1024)   // max inital size
#define MAX_MAP_EXPAND     (256*1024)    // max expand

#define HEAP_BLOCK_SIZE      4096
#define MAX_HEAP_ALLOC_SIZE  (HEAP_BLOCK_SIZE - sizeof(heap_t))
#define HEAP_ALIGN           sizeof(void*)

#define ALIGN(ptr,align) ((((intptr_t) (ptr)) + (align) -1) & ~((align)-1))
#define PAD(ptr,align) (((align)-((intptr_t)(ptr)) & ((align)-1)) & ((align)-1))

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

#define CLASS 0
#define VALUE 1
#define MARK  2
#define UMARK(v) ((v) >> 2)

typedef struct _undo_t {
    struct _undo_t* next; // MUST BE FIRST
    int what;   // (CLASS | VALUE) | MARK
    int x;      // variable
    int y;      // old value
} undo_t;

#define CLAUSE_OP_OR   0
#define CLAUSE_OP_AND  1
#define CLAUSE_OP_XOR  2

#define CLAUSE_FLAG_INQUEUE 0x0001
#define CLAUSE_FLAG_DEAD    0x0002

typedef struct _clause_var_t  // not used yet...
{
    struct _clause_var_t* next;
    struct _clause_var_t* prev;
    uint64_t mask_F;             // bit mask of assigned positions
    uint64_t mask_T;             // bit mask of assigned positions
    uint16_t flags;              // INQUEUE ...
} clause_var_t;

typedef struct _clause_t
{
    struct _clause_t* next;      // MUST BE FIRST
    int      size;               // number of literals
    int      cix;                // clause index
    uint64_t mask_F;             // bit mask for 64 positions = FALSE
    uint64_t mask_T;             // bit mask for 64 positions = TRUE
    uint16_t flags;              // INQUEUE ...
    uint16_t op;                 // OR|AND|XOR
    int      lit[0];
} clause_t;

// FIXME: maybe store multiple clause/pos per block?
typedef struct _varref_t
{
    struct _varref_t* next;   // MUST BE FIRST
    unsigned clause;          // clause index
    unsigned pos;             // clause pos
} varref_t;

// FIXME: split structure to allow parallell access?
typedef struct _variable_t
{
    int value;             // current value
    int klass;             // class index
    int occure;            // occure counter
    varref_t* first;
    varref_t* first_pos[3];
    varref_t* first_neg[3];
} variable_t;

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

    int bcp;                 // boolean constraint propagation

    unsigned int expand;     // how much to expand value/class map
    variable_t*  var_map;    // variable/class map 
    int*         order_map;  // variable order table
    clause_t** clause_map;   // clause_map[v] = class chain of variable v
    unsigned int umark;      // next entry should be marked
    undo_t*  undo_stack;     // undo stack
    clause_t* eval_queue_hd; // eval queue head
    clause_t* eval_queue_tl; // eval queue tail

    arc4_stream_t as;        // random stream 

    allocator_t undo_allocator;
    allocator_t varref_allocator;
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
    NIF_FUNC( "new",                 2,  varc_new ),
    NIF_FUNC( "add_variable",        1,  varc_add_variable ),
    NIF_FUNC( "get_number_of_variables", 1,  varc_get_number_of_variables ),
    NIF_FUNC( "get",                 2,  varc_get ),
    NIF_FUNC( "put",                 3,  varc_put ),
    NIF_FUNC( "class",               2,  varc_class ),
    NIF_FUNC( "occure",              2,  varc_occure ),
    NIF_FUNC( "is_variable",         2,  varc_is_variable ),
    NIF_FUNC( "is_bound",            2,  varc_is_bound ),
    NIF_FUNC( "class_next",          2,  varc_class_next ),
    NIF_FUNC( "equal",               3,  varc_equal ),
    NIF_FUNC( "mark",                2,  varc_mark ),
    NIF_FUNC( "undo",                1,  varc_undo ),
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
    NIF_FUNC( "get_number_of_clauses",   1,  varc_get_number_of_clauses ),
    NIF_FUNC( "get_clauses",         2,  varc_get_clauses ),
    NIF_FUNC( "get_queue",           1,  varc_get_queue ),
    NIF_FUNC( "clear_queue",         1,  varc_clear_queue ),
    NIF_FUNC( "get_bindings",        2,  varc_get_bindings ),
    NIF_FUNC( "order_first",         1,  varc_order_first ),
    NIF_FUNC( "order_next",          2,  varc_order_next ),
    NIF_FUNC( "order_sort",          2,  varc_order_sort ),
    NIF_FUNC( "order_sort",          3,  varc_order_sort ),
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
DECL_ATOM(undefined);
DECL_ATOM(error);
DECL_ATOM(and);
DECL_ATOM(or);
DECL_ATOM(xor);
DECL_ATOM(inqueue);
DECL_ATOM(dead);
DECL_ATOM(flags);
DECL_ATOM(mask);
DECL_ATOM(id);
DECL_ATOM(random);
DECL_ATOM(occure);

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
    size = ALIGN(size, HEAP_ALIGN);
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
    ap->size = size;
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
	fread(rdat.rnd, 1, sizeof(rdat.rnd), f);
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
    cp->size = size;
    cp->mask_F = 0;
    cp->mask_T = 0;
    cp->flags = 0;
    cp->op = op;
    return cp;
}

static void clause_free(varc_t* vp, clause_t* cp)
{
    if (cp->size > 32)
	enif_free(cp);
    else
	varc_free(&vp->clause_allocator[cp->size], (object_t*) cp);
}

static int is_variable(varc_t* vp, int x)
{
    return ((x > TRUE) && (x < (int)vp->vnext));
}

static int is_literal(varc_t* vp, int x)
{
    return (((x > TRUE) && (x < (int)vp->vnext)) ||
	    ((x < FALSE) && (-x < (int)vp->vnext)));
}

static int is_constant(varc_t* vp, int x)
{
    (void) vp;
    return ((x == TRUE) || (x == FALSE));
}

static int is_bound( varc_t* vp, int x)
{
    if (x < 0) x = -x;
    if ((x < 2) || (x >= (int)vp->vnext)) return -1;
    return vp->var_map[x].value != UNDEF;
}

// Save binding on the undo stack
static void push(varc_t* vp, int what, int x, int y)
{
    undo_t* up;

    up = undo_alloc(vp);
    up->what = what | vp->umark;
    up->x = x;
    up->y = y;
    up->next = vp->undo_stack;
    vp->undo_stack = up;
    vp->umark &= ~MARK;  // remove decision mark
}

// put clause on eval queue
static int enqueue_clause(varc_t* vp, clause_t* cp)
{
    if (cp->flags & (CLAUSE_FLAG_INQUEUE|CLAUSE_FLAG_DEAD))
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
    }
    return cp;
}

static void init_variable(variable_t* var, int value, int klass)
{
    int i;

    var->value = value;
    var->klass = klass;
    var->first = NULL;
    for (i = 0; i < 3; i++)
	var->first_pos[i] = NULL;
    for (i = 0; i < 3; i++)
	var->first_neg[i] = NULL;
}


static void clear_queue(varc_t* vp)
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

static void enqueue_varref(varc_t* vp,varref_t* vrp,int x,int y)
{
    while(vrp) {
	clause_t* cp = vp->clause_map[vrp->clause];
	unsigned pos = vrp->pos;
	if (pos < 64) {  // FIXME: other positions (>=64)!
	    if (x == -cp->lit[pos]) // FIXME: use several varref chains
		y = -y;
	    if (y == TRUE)
		cp->mask_T |= (1 << pos);
	    else if (y == FALSE)
		cp->mask_F |= (1 << pos);
	}
	enqueue_clause(vp,cp);
	vrp = vrp->next;
    }
}

static void enqueue_var(varc_t* vp,int x,int y)
{
    while(x != 0) {
	if (x < 0) {
	    y = -y;
	    enqueue_varref(vp,vp->var_map[-x].first,-x,y);
	    x = vp->var_map[-x].klass;
	}
	else {
	    enqueue_varref(vp,vp->var_map[x].first,x,y);
	    x = vp->var_map[x].klass;
	}
    }
}

static void wakeup_clause(varc_t* vp,clause_t* cp)
{
    (void) vp;
    cp->flags &= ~CLAUSE_FLAG_DEAD;
}

static void wakeup_varref(varc_t* vp,varref_t* vrp,int x,int y)
{
    while(vrp) {
	clause_t* cp = vp->clause_map[vrp->clause];
	unsigned pos = vrp->pos;
	if (pos < 64) {  // FIXME: other positions!
	    if (x == -cp->lit[pos]) // FIXME: use several varref chains
		y = -y;
	    if (y == TRUE)
		cp->mask_T &= ~(1 << pos);
	    else if (y == FALSE)
		cp->mask_F &= ~(1 << pos);
	}
	wakeup_clause(vp,cp);
	vrp = vrp->next;
    }
}

static void wakeup_var(varc_t* vp,int x,int y)
{
    while(x != 0) {
	if (x < 0) {
	    y = -y;
	    wakeup_varref(vp,vp->var_map[-x].first,-x,y);
	    x = vp->var_map[-x].klass;
	}
	else {
	    wakeup_varref(vp, vp->var_map[x].first,x,y);
	    x = vp->var_map[x].klass;
	}
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
	    // assert(x < vp->vnext)
	    x = -map[x].value;
	}
	else {
	    if (x0 == TRUE)
		return TRUE;
	    // assert(x < vp->vnext)
	    x = map[x].value;
	}
    }
    return x0;
}

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
	    // assert(x < vp->vnext)
	    x = -map[x].klass;
	}
	else {
	    if (x0 == TRUE)
		return TRUE;
	    // assert(x < vp->vnext)
	    x = map[x].klass;
	}
    }
    return x0;
}

static int put(varc_t* vp, int x, int y)
{
    int xc, yc;

    xc = klass(vp, x);
    yc = klass(vp, y);
    x = get(vp, xc);
    y = get(vp, yc);
    if (x == -y)
	return -1; // contradictory
    if (x == y)
	return 0;  // already equal
    // at this point x and y can not both be literal
    if (is_literal(vp,x)) {  // x is a literal (y may also be a literal)
	if (x < 0) {
	    x = -x; xc = -xc;
	    y = -y; yc = -yc;
	}
    }
    else if (is_literal(vp,y)) { // swap x and y
	if (y < 0) {
	    int tc = -yc, t = -y;
	    y = -x; yc = -xc;
	    x = t; xc = tc;
	}
	else {
	    int tc = yc, t = y;
	    y = x; yc = xc;
	    x = t; xc = tc;
	}
    }
    push(vp, VALUE, x, vp->var_map[x].value);
    enqueue_var(vp, x, y);
    vp->var_map[x].value = y;
    if (yc < 0) {
	if (yc != FALSE) {
	    yc = -yc;
	    push(vp, CLASS, yc, vp->var_map[yc].klass);
	    vp->var_map[yc].klass = -xc;
	}
    }
    else {
	if (yc != TRUE) {
	    push(vp, CLASS, yc, vp->var_map[yc].klass);
	    vp->var_map[yc].klass = xc;
	}
    }
    return 0;
}



static int add_varref(varc_t* vp,int op,int lit,unsigned clause,unsigned pos)
{
    varref_t* vrp;
    varref_t* vrp1;
    int ix;

    if ((lit == TRUE) || (lit == FALSE))
	return 0;
    // remove this soon
    if ((vrp = varc_alloc(&vp->varref_allocator)) == NULL)  
	return -1;
    if ((vrp1 = varc_alloc(&vp->varref_allocator)) == NULL)
	return -1;
    // Keep a positive and a negative literal list for each op & variable
    if (lit < 0) {
	ix = -lit;
	vrp1->next = vp->var_map[ix].first_pos[op];
	vp->var_map[ix].first_pos[op] = vrp1;
    }
    else {
	ix = lit;
	vrp1->next = vp->var_map[ix].first_neg[op];
	vp->var_map[ix].first_neg[op] = vrp1;
    }
    vrp->next = vp->var_map[ix].first;
    vp->var_map[ix].first = vrp;
    vp->var_map[ix].occure++;
    vrp->clause = clause;
    vrp->pos = pos;
    return 0;
}

// locate, unlink and free the variable reference
static int del_varref(varc_t* vp,varref_t** vrpp,unsigned clause,unsigned pos)
{
    varref_t* vrp;

    while((vrp = *vrpp)) {
	if ((vrp->clause == clause) && (vrp->pos == pos)) {
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
    int cix;

    enqueue_clause(vp, cp);

    if (vp->cnext == vp->csize) {
	unsigned int old_csize = vp->csize;
	unsigned int new_csize = old_csize + vp->expand;
	void* p;
	// expand
	if (!(p = enif_realloc(vp->clause_map, new_csize*sizeof(clause_t**))))
	    return -1;
	vp->clause_map = p;
	vp->csize = new_csize;
    }
    vp->cnum++;
    cix = vp->cnext++;
    vp->clause_map[cix] = cp;
    cp->cix = cix;
    return cix;
}

static ERL_NIF_TERM make_boolean(ErlNifEnv* env, int value)
{
    (void) env;
    return value ? ATOM(true) : ATOM(false);
}

static int get_literal(ErlNifEnv* env, varc_t* vp, ERL_NIF_TERM arg, int* x)
{
    int t;

    if (arg == ATOM(true)) {
	*x = TRUE;
	return 1;
    }
    if (arg == ATOM(false)) {
	*x = FALSE;
	return 1;
    }
    if (!enif_get_int(env, arg, &t))
	return 0;
    if (t < 0) {
	if (-t >= (int)vp->vnext) return 0;
	*x = t;
	return 1;
    }
    else if (t > 0) {
	if (t >= (int)vp->vnext) return 0;
	*x = t;
	return 1;
    }
    return 0;
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, int value)
{
    if (value == TRUE)
	return ATOM(true);
    else if (value == FALSE)
	return ATOM(false);
    return enif_make_int(env, value);
}

//
// F = Y1 OR Y2 OR ...          => Y1/FALSE, Y2/FALSE ...
//
// T  = F OR F ... OR F       => CONTRADICTION
// T  = F OR Y OR F ... OR F   => Y / TRUE
//
// X = F OR F ... OR F         => X/F
// X = Y1 OR T ... OR Yn       => X/T
// X = F OR Y ... OR F         => X/Y
//
// FIXME: use mask_F and mask_T to eval clause
//

static int eval_or_clause(varc_t* vp, clause_t* cp)
{
    int v,w;
    int i, j=0;
    int nf;

    w = v = get(vp, cp->lit[0]);
    switch(v) {
    case FALSE:
	TRACE("or:%d: lit[0]=%d size=%zd\r\n",cp->cix,w,cp->size);
	cp->flags |= CLAUSE_FLAG_DEAD;
	for (i = 1; i < cp->size; i++) {
	    if (put(vp, cp->lit[i], FALSE) < 0)
		return -1;
	}
	break;

    case TRUE:
	// if all literals except ONE lit[j] are FALSE, set lit[i] = TRUE
	nf = 0;  // count number of FALSE literals
	for (i = 1; i < cp->size; i++) {
	    if ((v = get(vp, cp->lit[i])) == TRUE)
		;
	    else if (v == FALSE)
		nf++;
	    else
		j = i; // save unbound pos
	}
	TRACE("or:%d: lit[0]=%d size=%zd nf=%d\r\n",cp->cix,w,cp->size,nf);
	if (nf == cp->size-1) { // all are false
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    return -1;  // contradiction
	}
	else if ((nf == cp->size-2) && j) {  // all but one are false
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (put(vp, cp->lit[j], TRUE) < 0) return -1;
	}
	break;
	
    default:
	nf = 0;  // count number of FALSE literals
	for (i = 1; i < cp->size; i++) {
	    if ((v = get(vp, cp->lit[i])) == TRUE) {
		TRACE("or:%d: lit[0]=%d size=%zd lit[%d]=true\r\n",
		      cp->cix,w,cp->size,i);
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[0], TRUE) < 0) return -1; // assert?
		return 0;
	    }
	    else if (v == FALSE)
		nf++;
	    else
		j = i;  // save unbound pos
	}
	TRACE("or:%d: lit[0]=%d size=%zd nf=%d\r\n",cp->cix,w,cp->size,nf);
	if (nf == cp->size-1) {  // all are false
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (put(vp, cp->lit[0], FALSE) < 0) return -1; // assert?
	}
	else if ((nf == cp->size-2) && j) {  // all but one are false
	    if (!vp->bcp) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[0], cp->lit[j]) < 0) return -1;
	    }
	}
	break;
    }
    return 0;
}

//
// F  = T AND T ... AND T         => CONTRADICTION
// F  = T AND Y ... AND T         => Y/F
//
// T = Y1 AND Y2 AND ...          => Y1/TRUE, Y2/TRUE ...
//
// X = T AND T ... AND T         => X/T
// X = Y1 AND F ... AND Yn       => X/F
// X = T AND Y ... AND T         => X/Y
//
// FIXME: use mask_F and mask_T to eval clause
//

static int eval_and_clause(varc_t* vp, clause_t* cp)
{
    int v,w;
    int i, j=0;
    int nt;

    v = w = get(vp, cp->lit[0]);
    switch(v) {
    case FALSE:
	nt = 0;  // count number of FALSE literals
	for (i = 1; i < cp->size; i++) {
	    if ((v = get(vp, cp->lit[i])) == FALSE)
		;
	    else if (v == TRUE)
		nt++;
	    else
		j = i; // save unbound pos
	}
	TRACE("and:%d: lit[0]=%d size=%zd nt=%d\r\n",cp->cix,w,cp->size,nt);
	if (nt == cp->size-1) { // all are true
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    return -1;  // contradiction
	}
	else if ((nt == cp->size-2) && j) {  // all but one are true
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (put(vp, cp->lit[j], FALSE) < 0) return -1;
	}
	break;
	
    case TRUE:
	TRACE("and:%d: lit[0]=%d size=%zd\r\n",cp->cix,w,cp->size);
	cp->flags |= CLAUSE_FLAG_DEAD;
	for (i = 1; i < cp->size; i++) {
	    if (put(vp, cp->lit[i], TRUE) < 0)
		return -1;
	}
	break;

    default:
	nt = 0;  // count number of FALSE literals
	for (i = 1; i < cp->size; i++) {
	    if ((v = get(vp, cp->lit[i])) == FALSE) {
		TRACE("and:%d: lit[0]=%d size=%zd lit[%d]=false\r\n",
		      cp->cix,w,cp->size,i);
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[0], FALSE) < 0) return -1; // assert?
		return 0;
	    }
	    else if (v == TRUE)
		nt++;
	    else
		j = i;  // save unbound pos
	}
	TRACE("and:%d: lit[0]=%d size=%zd nt=%d\r\n",cp->cix,w,cp->size,nt);
	if (nt == cp->size-1) {  // all are true
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (put(vp, cp->lit[0], TRUE) < 0) return -1; // assert?
	}
	else if ((nt == cp->size-2) && j) {  // all but one are true
	    if (!vp->bcp) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[0], cp->lit[j]) < 0) return -1;
	    }
	}
	break;
    }
    return 0;
}

//
// F = F XOR T XOR F        => CONTRADICTION
// F = T XOR F XOR T        => 
// F = T XOR X XOR F        => X/T
// F = F XOR X XOR F        => X/F
// F = F XOR X1 XOR X2      => X1/X2
// F = T XOR X1 XOR X2      => X1/-X2
//
// T = T XOR F XOR T        => CONTRADICTION
// T = F XOR T XOR F        => 
// T = F XOR X XOR T        => X/F
// T = T XOR X XOR T        => X/T
// T = T XOR X1 XOR X2      => X1/X2
// T = F XOR X1 XOR X2      => X1/-X2
//
// X = T XOR F XOR T        => X/F
// X = F XOR T XOR F        => X/T
// X = F XOR Y XOR T        => X/-Y
// X = T XOR Y XOR T        => X/Y
//
// FIXME: use mask_F and mask_T to eval clause
//
static int eval_xor_clause(varc_t* vp, clause_t* cp)
{
    int v, w;
    int i, j=0, k=0;
    int nf=0, nt=0;

    for (i = 1; i < cp->size; i++) {
	if ((v = get(vp, cp->lit[i])) == FALSE)
	    nf++;
	else if (v == TRUE)
	    nt++;
	else if (j)
	    k = i; // save unbound pos 2
	else 
	    j = i; // save unbound pos 1
    }
    v = w = get(vp, cp->lit[0]);

    TRACE("xor:%d: lit[0]=%d, size=%zd, nf=%d, nt=%d\r\n",cp->cix,
	  w,cp->size,nf,nt);

    switch(v) {
    case FALSE:
	if ((nt+nf) == cp->size-1) { // all are bound
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if (nt & 1)
		return -1;
	    return 0;
	}
	else if (((nt+nf) == cp->size-2) && j) {
	    if (nt & 1) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[j], TRUE) < 0) return -1;
	    }
	    else {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[j], FALSE) < 0) return -1;
	    }
	    return 0;
	}
	else if (((nt+nf) == cp->size-3) && j && k) {
	    if (nt & 1) {
		if (!vp->bcp) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    if (put(vp, cp->lit[j], -cp->lit[k]) < 0) return -1;
		}
	    }
	    else {
		if (!vp->bcp) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    if (put(vp, cp->lit[j], cp->lit[k]) < 0) return -1;
		}
	    }
	    return 0;
	}
	break;
	
    case TRUE:
	if ((nt+nf) == cp->size-1) { // all are bound
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if ((nt & 1))
		return -1; // contradiction
	    return 0;
	}
	else if (((nt+nf) == cp->size-2) && j) {
	    if (nt & 1) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[j], FALSE) < 0) return -1;
	    }
	    else {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[j], TRUE) < 0) return -1;
	    }
	    return 0;
	}
	else if (((nt+nf) == cp->size-3) && j && k) {
	    if (nt & 1) {
		if (!vp->bcp) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    if (put(vp, cp->lit[j], cp->lit[k]) < 0) return -1;
		}
	    }
	    else {
		if (!vp->bcp) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    if (put(vp, cp->lit[j], -cp->lit[k]) < 0) return -1;
		}
	    }
	    return 0;
	}
	break;

    default:
	if ((nt+nf) == cp->size-1) { // all are bound
	    if (nt & 1) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[0], TRUE) < 0) return -1;
	    }
	    else {
		cp->flags |= CLAUSE_FLAG_DEAD;
		if (put(vp, cp->lit[0], FALSE) < 0) return -1;
	    }
	    return 0;
	}
	else if (((nt+nf) == cp->size-2) && j) {
	    if (nt & 1) {
		if (!vp->bcp) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    if (put(vp, cp->lit[0], -cp->lit[j]) < 0) return -1;
		}
	    }
	    else {
		if (!vp->bcp) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    if (put(vp, cp->lit[0], cp->lit[j]) < 0) return -1;
		}
	    }
	    return 0;
	}
	break;
    }
    return 0;
}

static int eval_clause(varc_t* vp, clause_t* cp)
{
    switch(cp->op) {
    case CLAUSE_OP_OR: return eval_or_clause(vp, cp);
    case CLAUSE_OP_AND: return eval_and_clause(vp, cp);
    case CLAUSE_OP_XOR: return eval_xor_clause(vp, cp);
    default: return -1;
    }
}

static void cleanup(varc_t* vp)
{
    int i;

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
    unsigned int expand = DEFAULT_MAP_EXPAND;
    unsigned int vsize  = DEFAULT_MAP_SIZE;
    unsigned int csize  = DEFAULT_MAP_SIZE;
    ERL_NIF_TERM t;
    int i;
    
    if (!(vp = enif_alloc_resource(varc_res, sizeof(varc_t))))
	goto error;

    memset(vp, 0, sizeof(varc_t));

    if (argc >= 1) {
	if (!enif_get_uint(env, argv[0], &vsize))
	    return enif_make_badarg(env);
	if (vsize == 0)
	    vsize = DEFAULT_MAP_SIZE;
	else if ((vsize < 2) || (vsize > MAX_MAP_SIZE))
	    return enif_make_badarg(env);
    }
    if (argc >= 2) {
	if (!enif_get_uint(env, argv[1], &expand))
	    return enif_make_badarg(env);
	if (expand == 0)
	    expand = DEFAULT_MAP_EXPAND;
	else if (expand >  MAX_MAP_EXPAND)
	    return enif_make_badarg(env);
    }
    vp->vnext = 2;
    vp->vsize = vsize;
    vp->vnum  = 0;

    vp->expand = expand;
    if (!(vp->var_map = enif_alloc(vsize*sizeof(variable_t))))
	goto error;
    if (!(vp->order_map = enif_alloc(vsize*sizeof(int))))
	goto error;
    vp->cnext = 0;
    vp->csize = csize;
    vp->cnum = 0;

    vp->bcp = 0;

    if (!(vp->clause_map = enif_alloc(csize*sizeof(clause_t**))))
	goto error;
    if (init_allocator(&vp->undo_allocator, sizeof(undo_t)) < 0)
	goto error;
    if (init_allocator(&vp->varref_allocator, sizeof(varref_t)) < 0)
	goto error;
    for (i = 0; i <= 32; i++) {
	if (init_allocator(&vp->clause_allocator[i],
			   sizeof(clause_t)+i*sizeof(int)) < 0)
	    goto error;
    }
    vp->umark = MARK;

    init_variable(&vp->var_map[0], 0, 0);
    init_variable(&vp->var_map[1], 1, 1);
    
    vp->order_map[0] = 0;
    vp->order_map[1] = 1;

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

static ERL_NIF_TERM varc_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    unsigned int var;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vp->vnext == vp->vsize) {
	unsigned int old_vsize = vp->vsize;
	unsigned int new_vsize = old_vsize + vp->expand;
	variable_t* ptr;
	int* iptr;
	// expand
	if (!(ptr = enif_realloc(vp->var_map, new_vsize*sizeof(variable_t))))
	    return enif_make_badarg(env);
	if (!(iptr = enif_realloc(vp->order_map, new_vsize*sizeof(int))))
	    return enif_make_badarg(env);
	vp->var_map = ptr;
	vp->order_map = iptr;
	vp->vsize = new_vsize;
    }
    var = vp->vnext++;
    vp->vnum++;
    vp->var_map[var].value = UNDEF;
    vp->var_map[var].klass = UNDEF;
    vp->var_map[var].occure = 0;
    vp->var_map[var].first = NULL;
    vp->order_map[var] = var;
    return enif_make_int(env, var);
}

static ERL_NIF_TERM varc_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    (void) argc;
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
    (void) argc;
    varc_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &i))
	return enif_make_badarg(env);
    if (i < 1)
	return enif_make_badarg(env);

    for (i=i+1; i < (int)vp->vnext; i++) {
	int v = vp->order_map[i];
	if (!is_bound(vp, v))
	    return enif_make_tuple2(env,enif_make_int(env, i),
				    enif_make_int(env, v));
    }
    return ATOM(false);
}

static void order_reset(varc_t* vp)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++)
	vp->order_map[i] = i;
}

static void order_r_reset(varc_t* vp)
{
    int i;
    for (i = 2; i < (int)vp->vnext; i++)
	vp->order_map[(vp->vnext-i)+1] = i;
}

static void order_id(varc_t* vp, int arg)
{
    if (arg < 0)
	order_r_reset(vp);
    else
	order_reset(vp);
}


static void shuffle_array(varc_t* vp, int* a, size_t n)
{
    int i;
    // fprintf(stderr, "shuffle %lu\r\n", n);
    for (i = n-1; i >= 1; i--) {
	int j = arc4_random_uniform(&vp->as, n);
	// fprintf(stderr, "  swap %d, %d\r\n", i, j);
	if (i != j) {
	    int t = a[i];
	    a[i] = a[j];
	    a[j] = t;
	}
    }
    // fprintf(stderr, "done\r\n");
}

static void order_random(varc_t* vp, int arg)
{
    order_reset(vp);
    if (!arg) 
	arc4_stir(&vp->as);
    else {
	arc4_init(&vp->as);
	arc4_add_random(&vp->as, (uint8_t*)&arg, sizeof(arg));
    }
    shuffle_array(vp, vp->order_map+2, vp->vnext-2);
}

static int cmp_occure_inc(void* arg, const void* a, const void* b)
{
    varc_t* vp = (varc_t*) arg;
    return vp->var_map[*((int*)a)].occure - vp->var_map[*((int*)b)].occure;
}

static int cmp_occure_dec(void* arg, const void* a, const void* b)
{
    varc_t* vp = (varc_t*) arg;
    return vp->var_map[*((int*)b)].occure - vp->var_map[*((int*)a)].occure;
}

static void order_occure(varc_t* vp, int arg)
{
    order_reset(vp);
    if (arg < 0)
	qsort_r(vp->order_map+2, vp->vnext-2, sizeof(int), vp,
		cmp_occure_inc);
    else
	qsort_r(vp->order_map+2, vp->vnext-2, sizeof(int), vp,
		cmp_occure_dec);
}


static ERL_NIF_TERM varc_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    int arg = 0;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    if (argc > 2) {
	if (!enif_get_int(env, argv[2], &arg))
	    return enif_make_badarg(env);
    }
    if (argv[1] == ATOM(id))
	order_id(vp, arg);
    else if (argv[1] == ATOM(random))
	order_random(vp, arg);
    else if (argv[1] == ATOM(occure))
	order_occure(vp, arg);
    else
	return enif_make_badarg(env);
    return ATOM(ok);
}


static ERL_NIF_TERM varc_get_number_of_variables(ErlNifEnv* env, int argc,
						 const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->vnum);
}

static ERL_NIF_TERM varc_get_number_of_clauses(ErlNifEnv* env, int argc,
					       const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->cnum);
}

//
// get(Vct,X) -> Value.
// value of a literal X
//
static ERL_NIF_TERM varc_get(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    (void) argc;
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
    (void) argc;
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

static ERL_NIF_TERM varc_occure(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    (void) argc;
    int ix, lit;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);    
    if (!get_literal(env, vp, argv[1], &lit))
	return enif_make_badarg(env);
    ix = (lit < 1) ? -lit : lit;
    return enif_make_int(env, vp->var_map[ix].occure);
}


static ERL_NIF_TERM varc_is_variable(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    int x;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    return make_boolean(env, is_literal(vp,x));
}

static ERL_NIF_TERM varc_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    int x;
    int p;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if ((p = is_bound(vp,x)) < 0)
	return enif_make_badarg(env);
    return make_boolean(env, p);
}


//
//  class_next(X, Vct) -> X'
//
static ERL_NIF_TERM varc_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    (void) argc;
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);	
    if (!is_variable(vp,x))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->var_map[x].klass);
}


static ERL_NIF_TERM varc_equal(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    (void) argc;
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
    (void) argc;
    int x, y;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[2], &y))
	return enif_make_badarg(env);
    if (put(vp, x, y) < 0)
	return ATOM(false);
    return ATOM(true);
}

static ERL_NIF_TERM varc_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    unsigned int mark;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &mark))
	return enif_make_badarg(env);
    vp->umark = MARK | (mark<<2);
    return ATOM(true);
}

static ERL_NIF_TERM varc_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    undo_t* up;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);

    up = vp->undo_stack;
    while(up != NULL) {
	int x, y, w;
	undo_t* un;
	x = up->x;
	y = up->y;
	w = up->what;
	un = up->next;
	undo_free(vp,up);
	up = un;
	wakeup_var(vp,x,y);
	if (w & VALUE)
	    vp->var_map[x].value = y;
	else
	    vp->var_map[x].klass = y;
	if (w & MARK)
	    break;
    }
    vp->undo_stack = up;
    return ATOM(true);
}

static ERL_NIF_TERM varc_eval(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    clause_t* cp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);

    while((cp = dequeue_clause(vp)) != NULL) {
	TRACE("dequeue = %d\r\n", cp->cix);
	if (eval_clause(vp, cp) < 0) {
	    clear_queue(vp);
	    return ATOM(false);  // contradiction
	}
    }
    return ATOM(true);
}

static ERL_NIF_TERM add_clause_list(ErlNifEnv* env, varc_t* vp, int op,
				    ERL_NIF_TERM list, size_t size)
{
    clause_t* ptr;
    ERL_NIF_TERM head, tail;
    int i, cix;

    if ((ptr = clause_alloc(vp, op, size)) == NULL)
	return enif_make_badarg(env);
    if ((cix = insert_clause(env, vp, ptr)) < 0)
	return enif_make_badarg(env);
    i = 0;
    while(enif_get_list_cell(env, list, &head, &tail)) {
	int x;
	if (!get_literal(env, vp, head, &x))  // should not fail!
	    return enif_make_badarg(env);
	ptr->lit[i] = x;
	if (add_varref(vp, op, x, cix, i) < 0)
	    return enif_make_badarg(env);
	i++;
	list = tail;
    }
    return enif_make_int(env, cix);
}

static ERL_NIF_TERM add_clause_array(ErlNifEnv* env, varc_t* vp, int op,
				     const ERL_NIF_TERM* array, size_t size)
{
    clause_t* ptr;
    int i, cix;

    if ((ptr = clause_alloc(vp, op, size)) == NULL)
	return enif_make_badarg(env);
    if ((cix = insert_clause(env, vp, ptr)) < 0)
	return enif_make_badarg(env);

    for (i = 0; i < (int)size; i++) {
	int x;
	if (!get_literal(env, vp, array[i], &x))  // should not fail!
	    return enif_make_badarg(env);
	ptr->lit[i] = x;
	if (add_varref(vp, op, x, cix, i) < 0)
	    return enif_make_badarg(env);
    }
    return enif_make_int(env, cix);
}

//
// add_clause(vp, 'and', x1, ..., xn)
// add_clause(vp, 'or',  x1, ..., xn)
// add_clause(vp, 'xor', x1, ..., xn)
// add_clause(vp, Op, [x1, ..., xn])
//
static ERL_NIF_TERM varc_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    int op;
    varc_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);

    if (argv[1] == ATOM(and))
	op = CLAUSE_OP_AND;
    else if (argv[1] == ATOM(or))
	op = CLAUSE_OP_OR;
    else if (argv[1] == ATOM(xor))
	op = CLAUSE_OP_XOR;
    else
	return enif_make_badarg(env);

    if (argc == 3) {   // argv[2] is a list of literals
	ERL_NIF_TERM list = argv[2];
	ERL_NIF_TERM head, tail;
	size_t n;  // clause length

	n = 0;
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    int x;
	    if (!get_literal(env, vp, head, &x))
		return enif_make_badarg(env);
	    if (!is_literal(vp,x) && !is_constant(vp,x))
		return enif_make_badarg(env);
	    n++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
	return add_clause_list(env, vp, op, argv[2], n);
    }
    else {
	for (i = 2; i < argc; i++) {
	    int x;
	    if (!get_literal(env, vp, argv[i], &x))
		return enif_make_badarg(env);
	    if (!is_literal(vp,x) && !is_constant(vp,x))
		return enif_make_badarg(env);
	}
	return add_clause_array(env, vp, op, argv+2, argc-2);
    }
}

static ERL_NIF_TERM varc_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    (void) argc;
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
    for (i = 0; i < cp->size; i++) {
	int lit = cp->lit[i];
	if ((lit != TRUE) && (lit != FALSE)) {
	    int ix;
	    if (lit < 0) {
		ix = -lit;
		del_varref(vp, &vp->var_map[ix].first_neg[cp->op], cix, i);
	    }
	    else {
		ix = lit;
		del_varref(vp, &vp->var_map[ix].first_pos[cp->op], cix, i);
	    }
	    del_varref(vp, &vp->var_map[ix].first, cix, i);
	    vp->var_map[ix].occure--;
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
    (void) argc;
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
    case CLAUSE_OP_AND: op = ATOM(and); break;
    case CLAUSE_OP_OR: op = ATOM(or); break;
    case CLAUSE_OP_XOR: op = ATOM(xor); break;
    default: op = ATOM(undefined); break;
    }
    return enif_make_tuple2(env, op, list);
}

static ERL_NIF_TERM varc_get_clause_flags(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    (void) argc;
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


static ERL_NIF_TERM varc_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    varref_t* vrp;
    int lit, ix, i;
    ERL_NIF_TERM list;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_literal(env, vp, argv[1], &lit))
	return enif_make_badarg(env);
    ix = (lit < 0) ? -lit : lit;
    list = enif_make_list(env, 0);

    for (i = 0; i < 3; i++) {
	vrp = vp->var_map[ix].first_pos[i];
	while(vrp) {
	    ERL_NIF_TERM elem = enif_make_uint(env, vrp->clause);
	    list = enif_make_list_cell(env, elem, list);
	    vrp = vrp->next;
	}
    }
    for (i = 0; i < 3; i++) {
	vrp = vp->var_map[ix].first_neg[i];
	while(vrp) {
	    ERL_NIF_TERM elem = enif_make_uint(env, vrp->clause);
	    list = enif_make_list_cell(env, elem, list);
	    vrp = vrp->next;
	}
    }
    return list;
}


static ERL_NIF_TERM varc_get_queue(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    ERL_NIF_TERM list;
    clause_t* cp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    list = enif_make_list(env, 0);
    cp = vp->eval_queue_hd;
    while(cp) {
	ERL_NIF_TERM elem = enif_make_uint(env, cp->cix);
	list = enif_make_list_cell(env, elem, list);
	cp = cp->next;
    }
    return list;
}

static ERL_NIF_TERM varc_clear_queue(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    clear_queue(vp);
    return ATOM(ok);
}

static ERL_NIF_TERM varc_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    (void) argc;
    varc_t* vp;
    ERL_NIF_TERM list;
    undo_t* up;
    int mark;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &mark))
	return enif_make_badarg(env);

    list = enif_make_list(env, 0);
    up = vp->undo_stack;
    while(up) {
	ERL_NIF_TERM elem;
	int value;
	value = get(vp, up->x);
	elem = enif_make_tuple2(env,
				enif_make_int(env, up->x),
				make_literal(env, value));
	list = enif_make_list_cell(env, elem, list);
	if ((up->what & MARK) && (UMARK(up->what) == mark))
	    break;
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
    LOAD_ATOM(error);
    LOAD_ATOM(and);
    LOAD_ATOM(or);
    LOAD_ATOM(xor);
    LOAD_ATOM(inqueue);
    LOAD_ATOM(dead);
    LOAD_ATOM(flags);
    LOAD_ATOM(mask);
    LOAD_ATOM(id);
    LOAD_ATOM(random);
    LOAD_ATOM(occure);
}


static int varc_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    (void) env;
    (void) load_info;

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
    (void) load_info;

    varc_res = enif_open_resource_type(env, 0, "varc", varc_dtor,
				       ERL_NIF_RT_CREATE | ERL_NIF_RT_TAKEOVER,
				       &tried);
    load_atoms(env);

    *priv_data = *old_priv_data;
    return 0;
}

static void varc_unload(ErlNifEnv* env, void* priv_data)
{
    (void) env;
    (void) priv_data;
}

ERL_NIF_INIT(varc, varc_funcs,
	     varc_load, NULL,
	     varc_upgrade, varc_unload)

