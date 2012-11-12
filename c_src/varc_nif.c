//
// NIF library for managing variable classes
//
#include <stdio.h>
#include <memory.h>
#include "erl_nif.h"

static int varc_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varc_reload(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varc_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
                         ERL_NIF_TERM load_info);
static void varc_unload(ErlNifEnv* env, void* priv_data);

static ERL_NIF_TERM varc_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_new_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varc_number_of_variables(ErlNifEnv* env, int argc,
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

#define FALSE -1
#define TRUE  1

#define MARK  1
#define VALUE 2
#define CLASS 0

typedef struct _undo_t {
    int what;   // (CLASS | VALUE) | MARK
    int x;
    int y;
} undo_t;

typedef struct _varc_t {
    unsigned int next;   // next free variable number
    unsigned int size;   // allocated size of value/class map
    unsigned int expand; // how much to expand value/class map
    int*   value_map;    // value_map[v] = value of variable v
    int*   class_map;    // class_map[v] = class chain of variable v
    unsigned int usize;  // allocated size of undo vector
    unsigned int upos;   // "stack" position of undo
    unsigned int umark;  // next entry should be marked
    undo_t*  undo_map;   // undo vector
} varc_t;

ErlNifResourceType* varc_res;

ErlNifFunc varc_funcs[] = 
{
    { "new",                 0,  varc_new },
    { "new",                 1,  varc_new },
    { "new",                 2,  varc_new },
    { "new_variable",        1,  varc_new_variable },
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

static ERL_NIF_TERM x_enif_make_boolean(ErlNifEnv* env, int value)
{
    return value ? ATOM(true) : ATOM(false);
}

static int is_variable(int x, varc_t* vp)
{
    return ((x > TRUE) && (x < vp->size));
}

static int is_literal(int x, varc_t* vp)
{
    return (((x > TRUE) && (x < vp->size)) ||
	    ((x < FALSE) && (-x < vp->size)));
}

static int is_constant(int x, varc_t* vp)
{
    return ((x == TRUE) || (x == FALSE));
}

static int is_bound(int x, varc_t* vp)
{
    if (x < 0) x = -x;
    if ((x < 2) || (x >= vp->size)) return -1;
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

    if (vp->upos >= vp->size) {
	fprintf(stderr, "varc_nif: trying to push above limit\r\n");
	return;
    }
    up = &vp->undo_map[vp->upos];
    up->what = what | vp->umark;
    up->x = x;
    up->y = y;
    vp->upos++;
    vp->umark = 0;  // mark reset
}

static void cleanup(varc_t* vp)
{
    if (vp->value_map) {
	free(vp->value_map);
	vp->value_map = NULL;
    }
    if (vp->class_map) {
	free(vp->class_map);
	vp->class_map = NULL;
    }
    if (vp->undo_map) {
	free(vp->undo_map);
	vp->undo_map = NULL;
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
    unsigned int size   = DEFAULT_MAP_SIZE;
    ERL_NIF_TERM t;
    
    if (!(vp = enif_alloc_resource(varc_res, sizeof(varc_t))))
	goto error;

    memset(vp, 0, sizeof(varc_t));

    if (argc >= 1) {
	if (!enif_get_uint(env, argv[0], &size))
	    return enif_make_badarg(env);
	if (size == 0)
	    size = DEFAULT_MAP_SIZE;
	else if ((size < 2) || (size > MAX_MAP_SIZE))
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
    vp->next = 2;
    vp->size = size;
    vp->expand = expand;
    if (!(vp->value_map = malloc(size*sizeof(int))))
	goto error;
    if (!(vp->class_map = malloc(size*sizeof(int))))
	goto error;	
    if (!(vp->undo_map  = malloc(size*sizeof(undo_t))))
	goto error;
    vp->upos  = 0;
    vp->umark = MARK;
    vp->usize = size;
    
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

static ERL_NIF_TERM varc_new_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    unsigned int var;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vp->next == vp->size) {
	unsigned int old_size = vp->size;
	unsigned int new_size = old_size + vp->expand;
	void* ptr;
	// expand
	if (!(ptr = realloc(vp->value_map, new_size*sizeof(int))))
	    return enif_make_badarg(env);
	vp->value_map = ptr;
	if (!(ptr = realloc(vp->class_map, new_size*sizeof(int))))
	    return enif_make_badarg(env);
	vp->class_map = ptr;
	if (!(ptr = realloc(vp->undo_map, new_size*sizeof(undo_t))))
	    return enif_make_badarg(env);
	vp->undo_map = ptr;
	vp->size = new_size;
    }
    var = vp->next++;
    vp->value_map[var] = 0;
    vp->class_map[var] = 0;
    return enif_make_tuple2(env, enif_make_int(env, var), argv[0]);
}

static ERL_NIF_TERM varc_number_of_variables(ErlNifEnv* env, int argc,
					     const ERL_NIF_TERM argv[])
{
    varc_t* vp;

    if (!enif_get_resource(env, argv[0], varc_res, (void**)&vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->next);
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
    
    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);
    if (!enif_get_resource(env, argv[1], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (is_constant(x,vp))
	return enif_make_int(env, x);	
    if (!is_literal(x,vp))
	return enif_make_badarg(env);
    if (!(x = lookup(x, vp->value_map, vp->size)))
	return enif_make_badarg(env);
    return enif_make_int(env, x);
}

static ERL_NIF_TERM varc_class(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    int x;
    varc_t* vp;
    
    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);
    if (!enif_get_resource(env, argv[1], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (is_constant(x,vp))
	return enif_make_int(env, x);	
    if (!is_literal(x,vp))
	return enif_make_badarg(env);
    if (!(x = lookup(x, vp->class_map, vp->size)))
	return enif_make_badarg(env);
    return enif_make_int(env, x);
}


static ERL_NIF_TERM varc_is_variable(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    int x;

    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);
    if (!enif_get_resource(env, argv[1], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    return x_enif_make_boolean(env, is_literal(x, vp));
}

static ERL_NIF_TERM varc_is_bound(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    varc_t* vp;
    int x;
    int p;

    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);
    if (!enif_get_resource(env, argv[1], varc_res, (void**) &vp))
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

    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);	
    if (!enif_get_resource(env, argv[1], varc_res, (void**) &vp))
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

    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &y))
	return enif_make_badarg(env);
    if (!enif_get_resource(env, argv[2], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!(x = lookup(x, vp->class_map, vp->size)))
	return enif_make_badarg(env);
    if (!(y = lookup(y, vp->class_map, vp->size)))
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

    if (!enif_get_int(env, argv[0], &x))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &y))
	return enif_make_badarg(env);
    if (!enif_get_resource(env, argv[2], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!is_literal(x, vp))
	return enif_make_badarg(env);

    if (x < 0) { x = -x; y = -y; }

    // we could allow bound x by let x mean class(x)
    if (is_bound(x, vp))
	return enif_make_badarg(env);
    if (!(yc = lookup(y, vp->class_map, vp->size)))
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
    int pos;

    if (!enif_get_resource(env, argv[0], varc_res, (void**) &vp))
	return enif_make_badarg(env);
    pos = vp->upos;
    while(pos > 0) {
	int x, y;

	pos--;
	x = vp->undo_map[pos].x;
	y = vp->undo_map[pos].y;
	if (vp->undo_map[pos].what & VALUE)
	    vp->value_map[x] = y;
	else
	    vp->class_map[x] = y;
	if (vp->undo_map[pos].what & MARK)
	    break;
    }
    vp->upos = pos;
    return argv[0];
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

