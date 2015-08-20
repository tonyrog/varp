//
// NIF library for managing variable classes
//
#include <stdio.h>
#include <stdint.h>
#include <memory.h>
#include "erl_nif.h"

static int varc_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varc_reload(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
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
static ERL_NIF_TERM varc_number_of_variables(ErlNifEnv* env, int argc,
					     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_number_of_clauses(ErlNifEnv* env, int argc,
					   const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_value(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_is_variable(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_equivalent(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_is_equivalent(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);

#define DEFAULT_MAP_SIZE   1024
#define DEFAULT_MAP_EXPAND 1024

#define MAX_MAP_SIZE       (1024*1024)   // max inital size
#define MAX_MAP_EXPAND     (256*1024)    // max expand

#define HEAP_BLOCK_SIZE      4096
#define MAX_HEAP_ALLOC_SIZE  (HEAP_BLOCK_SIZE - sizeof(heap_t))
#define HEAP_BYTE_ALIGN      sizeof(void*)

#define FALSE -1
#define TRUE  1

#define MARK  1
#define VALUE 2
#define CLASS 0

typedef struct _undo_t {
    struct _undo_t* next;  // undo list next
    int what;   // (CLASS | VALUE) | MARK
    int x;
    int y;
} undo_t;

#define CLAUSE_OP_OR   1
#define CLAUSE_OP_AND  2
#define CLAUSE_OP_XOR  3

#define CLAUSE_FLAG_INQUEUE 0x0001

// max clause length is 32
typedef struct _clause_t
{
    struct _clause_t* next;      // next in queue or other lists
    uint32_t mask;               // bit mask of assigned positions
    uint16_t flags;              // INQUEUE ...
    uint8_t  op;                 // OR|AND|XOR
    uint8_t  size;               // number of literals 1..32
    int      lit[0];
} clause_t;

typedef struct _heap_t
{
    struct _heap_t* next;       // next heap block
    uint8_t* current;           // must be aligned
    uint8_t* end;
    uint8_t base[0];
} heap_t;

typedef struct _varc_t {
    unsigned int vnext;      // next free variable number
    unsigned int vsize;      // allocated size of value/class map
    unsigned int cnext;      // next clause number
    unsigned int csize;      // allocated size of value/class map
    unsigned int expand;     // how much to expand value/class map
    int*   value_map;        // value_map[v] = value of variable v
    int*   class_map;        // class_map[v] = class chain of variable v
    clause_t** clause_map;   // class_map[v] = class chain of variable v
    unsigned int umark;      // next entry should be marked
    undo_t*  undo_stack;     // undo stack
    clause_t* eval_queue;    // clauses to eval 

    heap_t* undo_heap;       // memory heap to allocate/free undo elements from
    undo_t* undo_free;          // free list of undo_t
    heap_t* clause_heap[33]; // memory heaps to allocate/free clauses from
    clause_t* clause_free[33];  // free list of clause_t
} varc_t;

ErlNifResourceType* varc_res;

ErlNifFunc varc_funcs[] = 
{
    { "new",                 0,  varc_new },
    { "new",                 1,  varc_new },
    { "new",                 2,  varc_new },
    { "add_variable",        1,  varc_add_variable },
    { "number_of_variables", 1,  varc_number_of_variables },
    { "value",               2,  varc_value },
    { "class",               2,  varc_class },
    { "is_variable",         2,  varc_is_variable },
    { "is_bound",            2,  varc_is_bound },
    { "class_next",          2,  varc_class_next },
    { "equivalent",          3,  varc_equivalent },
    { "is_equivalent",       3,  varc_is_equivalent },
    { "mark",                1,  varc_mark },
    { "undo",                1,  varc_undo },
    { "add_clause",          3,  varc_add_clause },   // x1 = OP x2 ... x32
    { "add_clause",          4,  varc_add_clause },   // x1 = OP x2
    { "add_clause",          5,  varc_add_clause },   // x1 = OP x2 x3
    { "add_clause",          6,  varc_add_clause },   // x1 = OP x2 x3 x4
    { "add_clause",          7,  varc_add_clause },   // x1 = OP x2 x3 x4 x5
    { "add_clause",          8,  varc_add_clause },   // x1 = OP x2 x3 x4 x5 x6
    { "get_clause",          2,  varc_get_clause },
    { "number_of_clauses",   1,  varc_number_of_clauses },
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


static heap_t* new_heap_block(heap_t* next)
{
    void* block;
    heap_t* hp;

    if (posix_memalign(&block, HEAP_BYTE_ALIGN, HEAP_BLOCK_SIZE) < 0)
	return NULL;
    hp = (heap_t*) block;
    hp->next    = next;
    hp->current = hp->base;
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
    if (hp->current + size >= hp->end) {
	if ((hq = new_heap_block(hp)) == NULL)
	    return NULL;
	*pool = hq;
	hp = hq;
    }
    size = (size + HEAP_BYTE_ALIGN - 1) & ~(HEAP_BYTE_ALIGN-1);
    ptr = hp->current;
    hp->current += size;
    return ptr;
}

undo_t* undo_alloc(varc_t* vp)
{
    undo_t* ptr;
    if ((ptr = vp->undo_free) == NULL)
	return heap_alloc(&vp->undo_heap, sizeof(undo_t));
    vp->undo_free = ptr->next;
    return ptr;
}

void undo_free(undo_t* ptr, varc_t* vp)
{
    ptr->next = vp->undo_free;
    vp->undo_free = ptr;
}

// allocate a simple clause (size <= 32)
clause_t* clause_alloc(varc_t* vp, uint8_t op, size_t size)
{
    clause_t* ptr;
    if ((size < 2) || (size > 32))
	return NULL;
    if ((ptr = vp->clause_free[size]) != NULL)
	vp->clause_free[size] = ptr->next;
    else if ((ptr = heap_alloc(&vp->clause_heap[size],
			       sizeof(clause_t)+sizeof(int)*size)) == NULL)
	return NULL;
    ptr->next = NULL;
    ptr->mask = 0;
    ptr->op   = op;
    ptr->size = size;
    // memset(ptr->lit, 0, sizeof(int)*size); // debug only?
    return ptr;
}

void clause_free(clause_t* ptr, varc_t* vp)
{
    ptr->next = vp->clause_free[ptr->size];
    vp->clause_free[ptr->size] = ptr;
}

static ERL_NIF_TERM x_enif_make_boolean(ErlNifEnv* env, int value)
{
    return value ? ATOM(true) : ATOM(false);
}

static int is_variable(int x, varc_t* vp)
{
    return ((x > TRUE) && (x < vp->vnext));
}

static int is_literal(int x, varc_t* vp)
{
    return (((x > TRUE) && (x < vp->vnext)) ||
	    ((x < FALSE) && (-x < vp->vnext)));
}

static int is_constant(int x, varc_t* vp)
{
    return ((x == TRUE) || (x == FALSE));
}

static int is_bound(int x, varc_t* vp)
{
    if (x < 0) x = -x;
    if ((x < 2) || (x >= vp->vnext)) return -1;
    return vp->value_map[x] != 0;
}

static int lookup(int x, int* map, size_t map_size)
{
    int x0 = x;

    while(x != 0) {
	x0 = x;
	if (x0 < 0) {
	    if (x0 == FALSE)
		return FALSE;
	    x = -x0;
	    if (x >= map_size)
		return 0;
	    x = -map[x];
	}
	else {
	    if (x0 == TRUE)
		return TRUE;
	    if (x >= map_size)
		return 0;
	    x = map[x];
	}
    }
    return x0;
}

static void push(int what, int x, int y, varc_t* vp)
{
    undo_t* up;

    up = undo_alloc(vp);
    up->what = what | vp->umark;
    up->x = x;
    up->y = y;
    up->next = vp->undo_stack;
    vp->undo_stack = up;
    vp->umark = 0;  // mark reset
}

static void cleanup(varc_t* vp)
{
    heap_t* hp;
    int i;

    if (vp->value_map) {
	free(vp->value_map);
	vp->value_map = NULL;
    }
    if (vp->class_map) {
	free(vp->class_map);
	vp->class_map = NULL;
    }
    if (vp->clause_map) {
	free(vp->clause_map);
	vp->clause_map = NULL;
    }
    hp = vp->undo_heap;
    while(hp != NULL) {
	heap_t* hp_next = hp->next;
	free(hp);
	hp = hp_next;
    }
    vp->undo_heap = NULL;
    vp->undo_free = NULL;

    for(i = 0; i <= 32; i++) {
	hp = vp->clause_heap[i];
	while(hp != NULL) {
	    heap_t* hp_next = hp->next;
	    free(hp);
	    hp = hp_next;
	}
	vp->clause_heap[i] = NULL;
	vp->clause_free[i] = NULL;
    }
}


static void varc_dtor(ErlNifEnv* env, void* obj)
{
    (void) env;
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
    vp->expand = expand;
    if (!(vp->value_map = malloc(vsize*sizeof(int))))
	goto error;
    if (!(vp->class_map = malloc(vsize*sizeof(int))))
	goto error;

    vp->cnext = 0;
    vp->csize = csize;
    if (!(vp->clause_map = malloc(csize*sizeof(clause_t**))))
	goto error;

    if (!(vp->undo_heap = new_heap_block(NULL)))
	goto error;
    for (i = 1; i <= 32; i++) {
	if (!(vp->clause_heap[i] = new_heap_block(NULL)))
	    goto error;
    }

    vp->umark = MARK;
    
    vp->value_map[0] = 0;
    vp->value_map[1] = 1;
    vp->class_map[0] = 0;
    vp->class_map[1] = 1;
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
    varc_t* vp;
    unsigned int var;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vp->vnext == vp->vsize) {
	unsigned int old_vsize = vp->vsize;
	unsigned int new_vsize = old_vsize + vp->expand;
	void* ptr;
	// expand
	if (!(ptr = realloc(vp->value_map, new_vsize*sizeof(int))))
	    return enif_make_badarg(env);
	vp->value_map = ptr;
	if (!(ptr = realloc(vp->class_map, new_vsize*sizeof(int))))
	    return enif_make_badarg(env);
	vp->class_map = ptr;
	vp->vsize = new_vsize;
    }
    var = vp->vnext++;
    vp->value_map[var] = 0;
    vp->class_map[var] = 0;
    return enif_make_int(env, var);
}

static ERL_NIF_TERM varc_number_of_variables(ErlNifEnv* env, int argc,
					     const ERL_NIF_TERM argv[])
{
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->vnext-2);
}

static ERL_NIF_TERM varc_number_of_clauses(ErlNifEnv* env, int argc,
					   const ERL_NIF_TERM argv[])
{
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->cnext);
}

//
// value(X, Vct) -> Value.
// value of a literal X
//
static ERL_NIF_TERM varc_value(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if (is_constant(x,vp))
	return enif_make_int(env, x);	
    if (!is_literal(x,vp))
	return enif_make_badarg(env);
    if (!(x = lookup(x, vp->value_map, vp->vsize)))
	return enif_make_badarg(env);
    return enif_make_int(env, x);
}

static ERL_NIF_TERM varc_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);    
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if (is_constant(x,vp))
	return enif_make_int(env, x);	
    if (!is_literal(x,vp))
	return enif_make_badarg(env);
    if (!(x = lookup(x, vp->class_map, vp->vsize)))
	return enif_make_badarg(env);
    return enif_make_int(env, x);
}


static ERL_NIF_TERM varc_is_variable(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    int x;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    return x_enif_make_boolean(env, is_literal(x, vp));
}

static ERL_NIF_TERM varc_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    int x;
    int p;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if ((p = is_bound(x, vp)) < 0)
	return enif_make_badarg(env);
    return x_enif_make_boolean(env, p);
}


//
//  class_next(X, Vct) -> X'
//
static ERL_NIF_TERM varc_class_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    int x;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);	
    if (!is_variable(x, vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->class_map[x]);
}


static ERL_NIF_TERM varc_is_equivalent(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    int x, y;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &y))
	return enif_make_badarg(env);
    if (!(x = lookup(x, vp->class_map, vp->vsize)))
	return enif_make_badarg(env);
    if (!(y = lookup(y, vp->class_map, vp->vsize)))
	return enif_make_badarg(env);
    return x_enif_make_boolean(env, (x == y));
}

//
// Make two literals equivalent
// X must be unbound!
//
static ERL_NIF_TERM varc_equivalent(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    int x, y, yc;
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &y))
	return enif_make_badarg(env);
    if (!is_literal(x, vp))
	return enif_make_badarg(env);

    if (x < 0) { x = -x; y = -y; }

    // we could allow bound x by let x mean class(x)
    if (is_bound(x, vp))
	return enif_make_badarg(env);
    if (!(yc = lookup(y, vp->class_map, vp->vsize)))
	return enif_make_badarg(env);
    push(VALUE, x, vp->value_map[x], vp);
    vp->value_map[x] = y;
    if (yc < 0) {
	if (yc != FALSE) {
	    yc = -yc;
	    push(CLASS, yc, vp->class_map[yc], vp);
	    vp->class_map[yc] = -x;
	}
    }
    else {
	if (yc != TRUE) {
	    push(CLASS, yc, vp->class_map[yc], vp);
	    vp->class_map[yc] = x;
	}
    }
    return argv[2];
}

static ERL_NIF_TERM varc_mark(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    vp->umark = MARK;
    return argv[0];
}

static ERL_NIF_TERM varc_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
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
	undo_free(up, vp);
	up = un;
	if (w & VALUE)
	    vp->value_map[x] = y;
	else
	    vp->class_map[x] = y;
	if (w & MARK)
	    break;
    }
    vp->undo_stack = up;
    return argv[0];
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
    uint8_t op;
    int lit[32];
    clause_t* ptr;
    varc_t* vp;
    int i;
    size_t size;
    unsigned int clause;

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

	i = 0;
	while((i < 32) && enif_get_list_cell(env, list, &head, &tail)) {
	    if (!enif_get_int(env, head, &lit[i]))
		return enif_make_badarg(env);
	    i++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
	size = i;
    }
    else if (argc  <= 34) {
	for (i = 2; i < argc; i++) {
	    if (!enif_get_int(env, argv[i], &lit[i-2]))
		return enif_make_badarg(env);
	}
	size = i-2;
    }
    else 
	return enif_make_badarg(env);

    if ((ptr = clause_alloc(vp, op, size)) == NULL)
	return enif_make_badarg(env);

    // check all literals
    for (i = 0; i < size; i++) {
	if (!is_literal(lit[i], vp) && !is_constant(lit[i], vp))
	    return enif_make_badarg(env);
	ptr->lit[i] = lit[i];
    }

    ptr->next = vp->eval_queue;
    vp->eval_queue = ptr;
    ptr->flags |= CLAUSE_FLAG_INQUEUE;

    if (vp->cnext == vp->csize) {
	unsigned int old_csize = vp->csize;
	unsigned int new_csize = old_csize + vp->expand;
	void* p;
	// expand
	if (!(p = realloc(vp->clause_map, new_csize*sizeof(clause_t**))))
	    return enif_make_badarg(env);
	vp->clause_map = p;
	vp->csize = new_csize;
    }

    clause = vp->cnext++;
    vp->clause_map[clause] = ptr;
    return enif_make_int(env, clause);
}

static ERL_NIF_TERM varc_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    clause_t* ptr;
    varc_t* vp;
    unsigned int clause;
    ERL_NIF_TERM lit[32];
    ERL_NIF_TERM op;
    int i;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &clause))
	return enif_make_badarg(env);
    if (clause >= vp->cnext)
	return enif_make_badarg(env);
    ptr = vp->clause_map[clause];
    
    for (i = 0; i < ptr->size; i++)
	lit[i] = enif_make_int(env, ptr->lit[i]);
    switch(ptr->op) {
    case CLAUSE_OP_AND: op = ATOM(and); break;
    case CLAUSE_OP_OR: op = ATOM(or); break;
    case CLAUSE_OP_XOR: op = ATOM(xor); break;
    default: op = ATOM(undefined); break;
    }
    return enif_make_tuple2(env, op, 
			    enif_make_list_from_array(env, lit, ptr->size));
}


static int varc_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    (void) env;
    (void) load_info;

    // Create resource types
    varc_res = enif_open_resource_type(env, 0, "varc", varc_dtor, 
				       ERL_NIF_RT_CREATE, &tried);
    // Load atoms
    LOAD_ATOM(ok);
    LOAD_ATOM(true);
    LOAD_ATOM(false);
    LOAD_ATOM(undefined);
    LOAD_ATOM(error);
    LOAD_ATOM(and);
    LOAD_ATOM(or);
    LOAD_ATOM(xor);

    *priv_data = 0;
    return 0;
}

static int varc_reload(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info)
{
    (void) env;
    (void) load_info;
    (void) priv_data;
    return 0;
}

static int varc_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
			ERL_NIF_TERM load_info)
{
    (void) env;
    (void) load_info;
    *priv_data = *old_priv_data;
    return 0;
}

static void varc_unload(ErlNifEnv* env, void* priv_data)
{
    (void) env;
    (void) priv_data;
}

ERL_NIF_INIT(varc, varc_funcs,
	     varc_load, varc_reload, 
	     varc_upgrade, varc_unload)

