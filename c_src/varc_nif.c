//
// NIF library for running watched literals clauses
//

#ifdef __linux__
#define _GNU_SOURCE
#endif

#ifdef __WIN32__
#include <windows.h>
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

#define EPSILON 1.19e-07
//
// configurations
// NIF_TRACE
// TWL_BACKWARD      
// ASSERTIONS         various sanity test in runtime (during test)
// DEBUG              various output during debug
// DEBUG_MEM          special wrapped allocators to find leaks etc
// DEBUG_BCP          print clauses during bcp
// LIT_INTEGER        literals are represented as integers, size=8,16,32
// LIT_VALUE          store literal values instead of variable value
// PACKED_VALUE       two bit values in separate vector size=1,4 per byte
//
// #define NIF_TRACE
#define TWL_BACKWARD
#define LIT_INTEGER 32
#define LIT_VALUE
#define PACKED_VALUE 1
#define ASSERTIONS
// #define DEBUG
// #define DEBUG_MEM
// #define DEBUG_BCP
// #define DEBUG_EDGE
// #define DEBUG_ORDER
// #define COUNT(vp, cnt)
#define COUNT(vp, cnt) vp->counter[(cnt)]++

// #define USE_CLAUSE_SHUFFLE
// #define USE_CLAUSE_FIND

#ifdef ASSERTIONS
// #define NDEBUG
#include <assert.h>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

typedef enum {
    false = 0,
    true = 1
} bool_t;

typedef enum {
    lifo = 0,
    fifo = 1,
    recursive = 2
} qtype_t;

typedef enum {
    off = 0,
    mvsids = 1,  // minisat style (update variables)
    cvsids = 2   // chaff style (update literals)
} atype_t;

#define ACTIVITY_INIT 0.0f

// counters
#define CLAUSE_N      0   // n>2
#define CLAUSE_2      1
#define CLAUSE_3      2
#define CLAUSE_D      3
#define EDGE_2        4
#define EDGE_D        5
#define NUM_COUNTERS  6

// use LSB bit to signal negation, this makes it easy
// to use cantor pair encoding since literals have as
// low numbers as possible

typedef enum {
    I_UNDEF = 0,  // 000
    I_BOUND = 1,  // 001
    I_TRUE  = 2,  // 010
    I_FALSE = 3   // 011
} ival_t;

#define IMPORT(x)      (((x)<0) ? (((-(x))<<1)|1) : ((x)<<1))
#define EXPORT(y)      (((y)&1) ? -((y)>>1) : ((y)>>1))
#define INDEX(x)       ((x)>>1)   // variable index
#define NEGATE(x)      ((x)^1)
#define SIGN(x)        ((x)&1)    // sign=1 if negative, positive otherwise
#define UNPACK(x)      ((x)&0x3)
#define PACK(x)        ((x)&0x3)
#define IS_CONSTANT(x) ((x)>1)   // true=2, false=3
#define MAKE_LIT(v,sgn) (((v)<<1)+(sgn))

// How many bytes to pack x values?
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
#define DBG(args...) enif_fprintf(stdout, args)
#else
#define DBG(args...)
#endif

#if defined(DEBUG_BCP)
#define DBG_BCP(args...) enif_fprintf(stdout, args)
#else
#define DBG_BCP(args...)
#endif

#define UNUSED(x) (void)(x)

static int varp_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varp_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
			ERL_NIF_TERM load_info);
static void varp_unload(ErlNifEnv* env, void* priv_data);

#define NIF_LIST \
    NIF( "new",                 1,  varp_new ) \
    NIF( "info",                2,  varp_info ) \
    NIF( "config",              3,  varp_config ) \
    NIF( "add_variable",        2,  varp_add_variable ) \
    NIF( "del_variable",        2,  varp_del_variable ) \
    NIF( "value",               2,  varp_value ) \
    NIF( "bind",                2,  varp_bind ) \
    NIF( "bind",                3,  varp_bind ) \
    NIF( "subst",               3,  varp_subst ) \
    NIF( "key",                 3,  varp_key ) \
    NIF( "implication_clause",  2,  varp_implication_clause ) \
    NIF( "implication_level",   2,  varp_implication_level ) \
    NIF( "implication_pos",     2,  varp_implication_pos ) \
    NIF( "conflicting_clause",  2,  varp_conflicting_clause ) \
    NIF( "is_variable",         2,  varp_is_variable ) \
    NIF( "is_bound",            2,  varp_is_bound ) \
    NIF( "is_equal",            3,  varp_is_equal ) \
    NIF( "set_level",           2,  varp_set_level ) \
    NIF( "keep_level",          2,  varp_keep_level ) \
    NIF( "move_level",          3,  varp_move_level ) \
    NIF( "undo_level",          2,  varp_undo_level ) \
    NIF( "undo",                1,  varp_undo ) \
    NIF( "bcp",                 1,  varp_bcp ) \
    NIF( "nbcp",                1,  varp_nbcp ) \
    NIF( "add_clause",          2,  varp_add_clause ) \
    NIF( "add_clause",          3,  varp_add_clause ) \
    NIF( "get_clause",          4,  varp_get_clause ) \
    NIF( "find_clause",         2,  varp_find_clause ) \
    NIF( "compress_clause",     2,  varp_compress_clause )  \
    NIF( "clause_info",         3,  varp_clause_info )  \
    NIF( "variable_info",       3,  varp_variable_info )  \
    NIF( "literal_info",        3,  varp_literal_info ) \
    NIF( "del_clause",          2,  varp_del_clause )  \
    NIF( "clean_clause",        2,  varp_clean_clause )  \
    NIF( "clean_edges",         2,  varp_clean_edges )  \
    NIF( "sort_clauses",        2,  varp_sort_clauses )  \
    NIF( "get_clauses",         3,  varp_get_clauses ) \
    NIF( "get_queue_first",     1,  varp_get_queue_first ) \
    NIF( "get_queue_next",      2,  varp_get_queue_next ) \
    NIF( "get_decision",        2,  varp_get_decision ) \
    NIF( "get_bindings",        3,  varp_get_bindings ) \
    NIF( "get_decision",        3,  varp_get_decision ) \
    NIF( "get_nbindings",       3,  varp_get_nbindings ) \
    NIF( "get_number_of_bindings", 2,  varp_get_number_of_bindings ) \
    NIF( "order_first",         1,  varp_order_first ) \
    NIF( "order_next",          3,  varp_order_next ) \
    NIF( "order_sort",          4,  varp_order_sort ) \
    NIF( "order_sort_first",    2,  varp_order_sort_first ) \
    NIF( "order_sort_last",     2,  varp_order_sort_last ) \
    NIF( "add_symbol",          3,  varp_add_symbol) \
    NIF( "find_symbol",         2,  varp_find_symbol ) \
    NIF( "use_clause",          2,  varp_use_clause ) \
    NIF( "decay",               2,  varp_decay ) \
    NIF( "subscribe",           2,  varp_subscribe ) \
    NIF( "clauseset_size",      2,  varp_clauseset_size ) \
    NIF( "clauseset_offset",    2,  varp_clauseset_offset ) \
    NIF( "clauseset_offset",    3,  varp_clauseset_offset ) \
    NIF( "clauseset_xref",      3,  varp_clauseset_xref ) \
    NIF( "clause_first",        2,  varp_clause_first ) \
    NIF( "clause_next",         2,  varp_clause_next ) \
    NIF( "set_user_count",      3,  varp_set_user_count )

// Declare all nif functions
#ifdef NIF_TRACE
#define NIF(name, arity, func) \
    static ERL_NIF_TERM func(ErlNifEnv* env, int argc,const ERL_NIF_TERM argv[]); \
    static ERL_NIF_TERM trace##_##func##_##arity(ErlNifEnv* env, int argc,const ERL_NIF_TERM argv[]);
#else
#define NIF(name, arity, func) \
    static ERL_NIF_TERM func(ErlNifEnv* env, int argc,const ERL_NIF_TERM argv[]);
#endif

NIF_LIST
#undef NIF

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


#ifdef LIT_INTEGER
#if LIT_INTEGER == 8
typedef uint8_t ulit_t;
#define VLIMIT 0x7f
#elif LIT_INTEGER == 16
typedef uint16_t ulit_t;
#define VLIMIT 0x7fff
#elif LIT_INTEGER == 32
typedef uint32_t ulit_t;
#define VLIMIT 0x07ffffff
#elif LIT_INTEGER == 64
typedef uint64_t ulit_t;
#define VLIMIT 0x07ffffff
#endif
typedef ulit_t lit_t;
#else
typedef uint32_t ulit_t;
#define VLIMIT 0x07ffffff
typedef struct _literal_t *lit_t;
#endif

#define ULIT_TRUE   0
#define ULIT_FALSE  1


typedef struct _literal_t
{
    uint32_t sign;             // 0=positive, 1=negative
    uint32_t degree;           // degree count for this literal
    uint32_t user;             // user count for sorting
    float    activity;         // activity value
    ulit_t    l;               // integer literal code
#if defined(LIT_VALUE) && !defined(PACKED_VALUE)
    ival_t    ivalue;
#endif
    // uint16_t flags;
    struct _variable_t* var;   // "parent"
    struct _wlink_t* wlist;    // list of watch positions
    struct _literal_t* qlink;  // unit propagation queue/stack
    struct _edge_t* elist;     // list of 2-clause triggers
    struct _xref_t* xfirst;    // cross ref clauses
    struct _xref_t** xlast;
} literal_t;

typedef uint32_t cix_t;             // clause index type <<set:2,index:30>>
typedef int32_t  pos_t;             // literal position type (-1 = invalid)
#define CLAUSE_NONE ((cix_t) -1)
#define MAKE_CIX(si,ix)  (((si)<<30)|(ix))
#define GET_SI(cix)      ((cix)>>30)
#define GET_IX(cix)      ((cix)&0x3FFFFFFF)

typedef struct _xref_t // :object_t
{
    struct _xref_t* next;
    cix_t cix;
    pos_t p;
} xref_t;

typedef struct _edge_t // :object_t
{
    struct _edge_t* next;
    cix_t    cix;            // real 2-clause    
    lit_t l;
} edge_t;

typedef struct _lqueue_t
{
//  size_t size;
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
#if !defined(LIT_VALUE) && !defined(PACKED_VALUE)
    ival_t    ivalue;
#endif
    int vix;                   // variable index
    float pkey[2];             // sort keys for positive literals
    float nkey[2];             // sort keys for negative literals
    float activity;            // activity 
    int map_index;             // order_map index
    cix_t implication_clause;  // implication clause index (0=none)
    pos_t literal_pos;         // position in implication clause
    int  level;                // implication clause level
    char* strname;             // string formated name or NULL
    struct _symbol_t* names;   // list of aliases
    literal_t lit[2];          // literal containers LIT_POS=0 LIT_NEG=1
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

#define CLAUSE_FLAG_INQUEUE   0x0001
#define CLAUSE_FLAG_DEAD      0x0002
#define CLAUSE_FLAG_CONFLICT  0x0004   // clause is in conflict list
#define CLAUSE_FLAG_UNWATCH   0x0008   // clause is on unwatch list
#define CLAUSE_FLAG_TWO       0x0010   // convert into 3-clause info a 2-clause

// sizeof wlink should be 8 on 32 bit machine or 16 on 64 bit machine
// 32 bit machine alignement should be 2*8 = 16 bytes
// 64 bit machine alignement should be 2*16 = 32 bytes
#define CLAUSE_ALIGNMENT (2*sizeof(wlink_t))

typedef struct _clause_t
{
    wlink_t    wl[2];        // ALIGNED watch point 1&2+links (DO NOT MOVE!)
    cix_t      cix;          // clause id (index) 0..n-1  (<< 1)    
    uint32_t   size;         // number of literals in lit
    uint8_t    flags;        // INQUEUE ...
    uint8_t    select;       // case select 0=2_clause, 1=3_clause, 2=n_clause
    struct _clause_t* uwatch;// clauses to unwatch
    uint64_t stamp;          // last used time (bcp_counter clock)
    uint32_t hvalue;         // clause hash value
    lit_t lit[];             // literal array
} clause_t;

// hash structure
typedef struct _hlink_t
{
    struct _hlink_t* next;
    uint32_t hvalue;
    cix_t cix;
} hlink_t;

typedef struct _undo_t
{
    lit_t decision;      // descision literal from bind
    int   t;             // 0=UNDEF, 1=SET+EVAL, 2=UNDO+NEG, 3=NEG+EVAL
    int   ix;            // order index
    variable_t* bs;      // list of bound variables
} undo_t;

typedef struct arc4_stream_t {
    uint8_t i;
    uint8_t j;
    uint8_t s[256];
} arc4_stream_t;

// flags
#define SUB_FLAG_VAR         0x0001    // report variable bindings (level 0)
#define SUB_FLAG_ATOM        0x0002    // only report "atom" bindings
#define SUB_FLAG_NUM_VARS    0x0010    // report number of variables
#define SUB_FLAG_NUM_BOUND   0x0020    // report number of bound variables
#define SUB_FLAG_NUM_CLAUSES 0x0040    // report number of variables
#define SUB_FLAG_NUM_DEAD    0x0080    // report number of bound variables
#define SUB_FLAG_MAX_LEVEL   0x0100    // report max level sinc last
#define SUB_FLAG_MAX_BOUND   0x0200    // report max bound variables since last

typedef struct _subscription_t { // :object_t
    struct _subscription_t* next;
    ErlNifPid pid;               // the subscriber pid
    ErlNifMonitor mon;           // monitor the pid
    uint32_t      flags;         // subscription flags
} subscription_t;

// CSET=0 Delta is the permanent clause set
// CSET=1 Gamma is the learned clause set
// CSET=2 Alpha is the temporary clause set
// CSET=3 Beta is unused right now

#define NUM_CSET 4

typedef struct _varp_t {
    // lit_t ltrue;
    // lit_t lfalse;
    size_t vnext;             // next free variable number
    size_t vsize;             // allocated size of value map
    size_t vnum;              // number of variables
    uint32_t cnext[NUM_CSET]; // next clause number
    uint32_t csize[NUM_CSET]; // allocated size of clause map
    uint32_t cnum[NUM_CSET];  // number of clauses
    uint32_t coffs[NUM_CSET]; // offset for clause iterator

    uint32_t cdead;           // number of dead clauses (level=0)
    uint32_t edead;           // number of dead edges (level=0)    
    uint32_t nedge;           // number of edges in use
    
    int num_conflicting;      // number of conflicting clauses saved
    int max_conflicting;      // max number of conflicting <= MAX_CONFLICTING
    int conflicting_clauses[MAX_CONFLICTING];
    uint32_t grow;            // how much to expand value map
    variable_t** var_map;     // variable map
#if defined(LIT_VALUE)
#if defined(PACKED_VALUE)
    uint8_t*     lit_value;   // ivals for every lit_t value
    uint16_t*    lit_overlay; // write overlay access for single write access
#endif
#else
#if defined(PACKED_VALUE)
    uint8_t*     var_value;   // values are stored 8 bit/2 bit packed
#endif
#endif
    size_t ssize;             // size of symbol hash table
    size_t snum;              // number of symbols in symbol hash table
    symbol_t**   sym_map;     // symbol hash table
    size_t       chsize;      // size of clause hash table
    size_t       chnum;       // number of clauses in clause hash table (cnext)?
    hlink_t**    clause_hash; // clause hash table    
    int*         order_map;   // literal order table
    int          sort_key[2]; // sort order -1,-2,1,2 (0=not used)
    clause_t**   clause_map[NUM_CSET]; // array of clauses, entries may be null
    clause_t*    unwatch;     // clauses to unwatch (check after bcp)
    size_t       unum;        // number of levels allocated
    undo_t*      undo;        // array of undo block, one for each level
    size_t       num_bound;   // number of bound variables
    size_t       max_bound;   // statistics max bound variables since last check
    
    int level;                // current undo level (mark)
    int max_level;            // statistics max level since last check
    qtype_t  qtype;           // literal queue is fifo/lifo/recursive
    atype_t  atype;           // conflict activity in use
    bool_t   xref;            // xref used or not
    lqueue_t q;               // literal queue for propagation
    bool_t   edge;            // keep edge list for 2-clauses

    uint64_t  counter[NUM_COUNTERS];
    uint64_t  bcp_counter;    // performance counter/step counter/clock
    uint64_t  conflict_counter; // number of conflicts
    
    variable_t constant;

    arc4_stream_t as;              // random stream

    subscription_t* subs;          // list of subscriptions
    ErlNifEnv*      msg_env;       // message environment
    ErlNifEnv*      caller_env;    // message environment
    
    allocator_t var_allocator;     // heap storage for variable_t
    allocator_t sym_allocator;     // heap storage for symbols_t
    allocator_t xref_allocator;    // heap storage for xref_t
    allocator_t sub_allocator;     // heap storage for subscription_t
    allocator_t edge_allocator;    // heap storage for edge_t
    allocator_t hlink_allocator;   // heap storage for hlink_t
} varp_t;

#define LL_TRUE(vp)    (&(vp)->constant.lit[LIT_POS])
#define LL_FALSE(vp)   (&(vp)->constant.lit[LIT_NEG])

#ifdef LIT_INTEGER
#define L_TRUE(vp)     ULIT_TRUE
#define L_FALSE(vp)    ULIT_FALSE
#else
#define L_TRUE(vp)     LL_TRUE(vp)
#define L_FALSE(vp)    LL_FALSE(vp)
#endif



#define MAX(a,b) (((a)>(b)) ? (a) : (b))
#define SWAP_INT(a,b) do { \
	int _t = (a); a=(b); b=(_t);		\
    } while(0)

ErlNifResourceType* varp_res;

#ifdef NIF_TRACE
#define NIF(name,arity,func) NIF_FUNC(name, arity, trace##_##func##_##arity),
#else
#define NIF(name,arity,func) NIF_FUNC(name, arity, func),
#endif

ErlNifFunc varp_funcs[] = 
{
    NIF_LIST
};
#undef NIF

// Atom macros
#define ATOM(name) atm_##name

#define DECL_ATOM(name) \
    ERL_NIF_TERM atm_##name = 0

// require env in context (ugly)
#define LOAD_ATOM(name)			\
    atm_##name = enif_make_atom(env,#name)

#define LOAD_ATOM_STRING(name,string)			\
    atm_##name = enif_make_atom(env,string)

DECL_ATOM(t);
DECL_ATOM(f);
DECL_ATOM(ok);
DECL_ATOM(true);
DECL_ATOM(false);
DECL_ATOM(default);
DECL_ATOM(grow);
DECL_ATOM(size);
DECL_ATOM(error);
DECL_ATOM(inqueue);
DECL_ATOM(dead);
DECL_ATOM(conflict);
DECL_ATOM(watch);
DECL_ATOM(watch0);
DECL_ATOM(watch1);
DECL_ATOM(status);
DECL_ATOM(literal);
DECL_ATOM(variable);
DECL_ATOM(flags);
DECL_ATOM(undefined);
DECL_ATOM(activity);
DECL_ATOM(degree);
DECL_ATOM(user);

DECL_ATOM(mvsids);
DECL_ATOM(cvsids);
DECL_ATOM(off);
// info
DECL_ATOM(max_clause_length);
DECL_ATOM(max_conflicting);
DECL_ATOM(number_of_conflicting_clauses);
DECL_ATOM(number_of_clauses);
DECL_ATOM(number_of_edges);
DECL_ATOM(number_of_dead_clauses);
DECL_ATOM(number_of_dead_edges);
DECL_ATOM(number_of_learned_clauses);
DECL_ATOM(number_of_variables);
DECL_ATOM(number_of_bound_variables);
DECL_ATOM(number_of_unbound_variables);
DECL_ATOM(clause_n_counter);
DECL_ATOM(clause_d_counter);
DECL_ATOM(clause_2_counter);
DECL_ATOM(clause_3_counter);
DECL_ATOM(edge_2_counter);
DECL_ATOM(edge_d_counter);
DECL_ATOM(bcp_counter);
DECL_ATOM(conflict_counter);
DECL_ATOM(unit);
DECL_ATOM(use);
DECL_ATOM(reset);
DECL_ATOM(level);
DECL_ATOM(max_level);
DECL_ATOM(max_bound);
DECL_ATOM(fifo);
DECL_ATOM(xref);
DECL_ATOM(clause_hash);
DECL_ATOM(implication);
DECL_ATOM(implication_clause);
DECL_ATOM(implication_pos);
DECL_ATOM(qtype);
DECL_ATOM(lifo);
DECL_ATOM(recursive);
DECL_ATOM(atom);
DECL_ATOM(varp);
DECL_ATOM(symbol);
DECL_ATOM(is_atom);
DECL_ATOM(edge);
DECL_ATOM(exclamation_mark);
DECL_ATOM(literal_size);
DECL_ATOM(literal_integer);
DECL_ATOM(value_packing);

// exceptions
DECL_ATOM(system_limit);

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
#define MASK  0x7f

//
// li is converted into a unsigned representation of
// li < 0 :  2*-li + 1
// li >=0 :  2*li
//
// then li is written as b0...bl
// 


static int compress_int(int li, uint8_t* ptr)
{
    int len;
    uint8_t* ptr0 = ptr;

    li = (li < 0) ? ((-li)<<1)+1 : li << 1;
    len = sizeof(int)*8 - __builtin_clz(li);
    while(len > 7) {
	*ptr++ = (li & MASK) + EXT;
	li >>= 7;
	len -= 7;
    }
    *ptr++ = (li & MASK);
    return (ptr-ptr0);
}

#if 0
static int decompress_int(uint8_t* ptr)
{
    int li = 0;
    int i = 0;
    uint8_t code;

    do {
	code = *ptr++;
	li |= ((code & MASK) << i);
	i += 7;
    } while(code & EXT);

    if (li & 1)
	return -(li>>1);
    return
	li >> 1;
}
#endif


// Clause point from wlink_t pointer
static inline clause_t* clause_pointer(wlink_t* wl)
{
    intptr_t w = (intptr_t) wl;
    return (clause_t*) (w & ~(CLAUSE_ALIGNMENT-1));
}

static inline int wlink_index(wlink_t* wl)
{
    intptr_t w = (intptr_t) wl;
    return (w & (CLAUSE_ALIGNMENT-1)) / sizeof(wlink_t);
}


static inline clause_t* get_clause(varp_t* vp, cix_t index)
{
    return vp->clause_map[GET_SI(index)][GET_IX(index)];
}

static inline void set_clause(varp_t* vp, cix_t index, clause_t* cp)
{
    vp->clause_map[GET_SI(index)][GET_IX(index)] = cp;
}

static size_t get_number_of_clauses(varp_t* vp)
{
    size_t cnum = 0;
    int i;
    for (i = 0; i < NUM_CSET; i++)
	cnum += vp->cnum[i];
    return cnum;
}

// primitive negate a literal
static inline literal_t* neg_ll(literal_t* lp)
{
    // return lp->sign ? &lp->var->lit[LIT_POS] : &lp->var->lit[LIT_NEG];
    return &lp->var->lit[!lp->sign];
}

static inline literal_t* vindex_ll(varp_t* vp, int i)
{
    ASSERT(i != 0);
    // return (i < 0) ? &vp->var_map[-i]->lit[LIT_NEG] :
    // &vp->var_map[i]->lit[LIT_POS];
    return &vp->var_map[abs(i)]->lit[(i<0)];
}

static inline lit_t vindex_l(varp_t* vp, int vix)
{
#ifdef LIT_INTEGER
    UNUSED(vp);    
    return (lit_t) IMPORT(vix);
#else
    return (lit_t) vindex_ll(vp, vix);
#endif
}

static inline int export_ll(literal_t* lp)
{
    ASSERT(lp->var != 0);
    return lp->sign ? -lp->var->vix : lp->var->vix;
}

static inline ERL_NIF_TERM external_ll(ErlNifEnv* env,literal_t* lp)
{
    if (lp->var->vix == 0)
	return lp->sign ? ATOM(f): ATOM(t);
    else {
	int x = export_ll(lp);
	return enif_make_int(env, x);
    }
}

static inline int is_neg_l(lit_t l)
{
#ifdef LIT_INTEGER
    return SIGN(l);
#else
    return l->sign;
#endif
}

static inline int is_constant_l(varp_t* vp, lit_t l)
{
    UNUSED(vp);
    return ((l == L_TRUE(vp)) || (l == L_FALSE(vp)));
}

static inline int export_l(lit_t l)
{
#ifdef LIT_INTEGER
    return EXPORT(l);
#else
    return export_ll(l);
#endif
}

static inline ERL_NIF_TERM external_l(ErlNifEnv* env,lit_t l)
{
#ifdef LIT_INTEGER
    if (l == ULIT_TRUE)
	return ATOM(t);
    else if (l == ULIT_FALSE)
	return ATOM(f);
    else
	return enif_make_int(env, export_l(l));
#else
    return external_ll(env, (literal_t*) l);
#endif    
}

static inline lit_t neg_l(lit_t l)
{
#ifdef LIT_INTEGER
    return NEGATE(l);
#else
    return neg_ll(l);
#endif
}

static inline literal_t* l2ll(varp_t* vp, lit_t l)
{
#ifdef LIT_INTEGER
    return &vp->var_map[INDEX(l)]->lit[SIGN(l)];
#else
    UNUSED(vp);
    return (literal_t*) l;
#endif
}

static inline lit_t ll2l(varp_t* vp, literal_t* lp)
{
    UNUSED(vp);
#ifdef LIT_INTEGER
    return lp->l;
#else
    UNUSED(vp);
    return (lit_t) lp;
#endif
}

// access variable from lit_t
static inline variable_t* var_l(varp_t* vp, lit_t l)
{
    literal_t* lp = l2ll(vp,l);
    return lp->var;
}

#ifdef PACKED_VALUE
static inline ival_t get_packed_ival(varp_t* vp, unsigned uix)
{
#if PACKED_VALUE == 1
#ifdef LIT_VALUE
    return (ival_t) vp->lit_value[uix<<1];
#else
    return (ival_t) vp->var_value[uix];
#endif
#elif PACKED_VALUE == 4
    int j = (uix & 0x3) << 1;  // shift 0,2,4,6
    uix >>= 2;
    return (ival_t) UNPACK(vp->var_value[uix] >> j);
#endif
}

static inline void set_packed_ival(varp_t* vp, unsigned uix, ival_t ivalue)
{
#if PACKED_VALUE == 1
#ifdef LIT_VALUE
    vp->lit_value[uix<<1] = ivalue;
#else
    vp->var_value[uix] = ivalue;
#endif
#elif PACKED_VALUE == 4
    int j = (uix&0x3) << 1;  // shift 0,2,4,6    
    uix >>= 2;
    vp->var_value[uix] = (vp->var_value[uix] & ~(0x3<<j)) | (PACK(ivalue) << j);
#endif
}

#endif

// primitiv get variable value
static inline ival_t get_vv(varp_t* vp, variable_t* var)
{
#ifdef PACKED_VALUE
    return get_packed_ival(vp, var->vix);
#else
    UNUSED(vp);
#ifdef LIT_VALUE
    return var->lit[LIT_POS].ivalue;
#else
    return var->ivalue;
#endif
#endif
}

static inline void write_vv(varp_t* vp, variable_t* var, ival_t v)
{
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
    vp->lit_overlay[var->vix] = (v << 8) | v;
#else
    set_packed_ival(vp, var->vix, v);
#endif
#else
    UNUSED(vp);
#ifdef LIT_VALUE
    var->lit[LIT_POS].ivalue = v;
    var->lit[LIT_NEG].ivalue = v;
#else
    var->ivalue = v;
#endif
#endif
}

static inline void clr_vv(varp_t* vp, variable_t* var)
{
    write_vv(vp, var, I_UNDEF);
}

static inline void bnd_vv(varp_t* vp, variable_t* var)
{
    write_vv(vp, var, I_BOUND);
}


static inline void set_vv(varp_t* vp, variable_t* var, ival_t ivalue)
{
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
#if BYTE_ORDER == LITTLE_ENDIAN
    uint16_t w = ((ivalue^1)<<8) | ivalue;
#else
    uint16_t w = (ivalue << 8) | ((ivalue^1)<<8);
#endif
    vp->lit_overlay[var->vix] = w;
#else
    set_packed_ival(vp, var->vix, ivalue);
#endif
#else
    UNUSED(vp);
#ifdef LIT_VALUE
    var->lit[LIT_POS].ivalue = ivalue;
    var->lit[LIT_NEG].ivalue = NEGATE(ivalue);
#else
    var->ivalue = ivalue;
#endif
#endif
}

// return literal match variables value (only when bound)
static inline literal_t* var_literal(varp_t* vp, variable_t* var)
{
    ival_t v = get_vv(vp,var);
    if (v == I_TRUE) return &var->lit[LIT_POS];
    else if (v == I_FALSE) return &var->lit[LIT_NEG];
    else {
	ASSERT(0);
	return NULL;
    }
}

// primitiv get literal value
static inline ival_t get_ll(varp_t* vp, literal_t* lp)
{
#ifdef LIT_VALUE
#ifdef PACKED_VALUE
    return vp->lit_value[lp->l];
#else
    UNUSED(vp);
    return lp->ivalue;
#endif
#else
    ival_t v = get_vv(vp,lp->var);
    if (IS_CONSTANT(v))
	return lp->sign ^ v;
    return v;
#endif
}

// primitive get lit value
static inline ival_t get_l(varp_t* vp, lit_t l)
{
#ifdef LIT_INTEGER

#ifdef LIT_VALUE
#ifdef PACKED_VALUE
    return vp->lit_value[l];
#else
    return vp->var_map[INDEX(l)]->lit[SIGN(l)].ivalue;
#endif
    
#else
    unsigned uix  = INDEX(l);
    unsigned sign = SIGN(l);
    ival_t ivalue;
#ifdef PACKED_VALUE
    ivalue = get_packed_ival(vp, uix);
#else
    ivalue = get_vv(vp, vp->var_map[uix]);
#endif
    if (IS_CONSTANT(ivalue))
	return sign ^ ivalue;
    return ivalue;
#endif
    
#else
    return get_ll(vp, (literal_t*)l);
#endif
}

#if 0
// primitive set literal value
static inline void set_ll(varp_t* vp, literal_t* lp, ival_t ivalue)
{
    if (lp->sign)
	set_vv(vp,lp->var,NEGATE(ivalue));
    else
	set_vv(vp,lp->var,ivalue);
}
#endif

// given a literal pointer, return the susbstituted literal value
static inline literal_t* lookup_literal(literal_t* lp)
{
    // fixme: keep neg flag separate to save neg_ll calls
    while (lp->var->bound) { // resolve literal
	if (lp->sign)  // negate literal
	    lp = neg_ll(lp->var->bound);
	else
	    lp = lp->var->bound;
    }
    return lp;
}

// return true if variable is constant or bound to other variable
// vix is a variable index or the negation of the same
static int vis_bound(varp_t* vp, int vix)
{
    variable_t* var = vp->var_map[ABS(vix)];
    return get_vv(vp, var) != I_UNDEF;
}

static inline int export_vv(varp_t* vp, variable_t* var)
{
    switch(get_vv(vp, var)) {
    case I_TRUE:  return var->vix;
    case I_FALSE: return -var->vix;
    case I_BOUND: ASSERT(0); return 0;
    case I_UNDEF: return 0;
    default: return 0;
    }
}

static uint32_t djb_hash(uint8_t* ptr, size_t len)
{
    uint32_t h = 5381;
    while(len--)
	h = ((h << 5) + h) + (*ptr++);
    return h;
}

// original:
// hash(L) := (1023·sum(L) + product(L) xor (31·xor(L))) (mod size)
// updated:
// hash(L) := (lengh(L)+1023·sum(L) + product(L)xor(31·xor(L))) (mod size)

static int32_t literal_array_hash(varp_t* vp, lit_t* lit, size_t size)
{
    UNUSED(vp);
    int32_t p = 1;
    int32_t s = 0;
    int32_t x = 0;
    int32_t len = 0;

    while(size--) {
	int32_t li;
	lit_t l = *lit++;
	
	ASSERT(l != L_TRUE(vp));
	if (l == L_FALSE(vp))  // count as zero
	    continue;
	li = export_l(l);
	p *= li;
	s += li;
	x ^= li;
	len++;
    }
    return len + (s<<10) - s + (p^((x<<5)-x));
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
    char* n = lp->sign ? "!" : "";
    UNUSED(vp);
    // alternate to allow to printf arguments!!
    litname = (litname == ln1) ? ln2 : ln1; 

    if (lp->var->strname != NULL)
	snprintf(litname, sizeof(ln1), "%s%s", n, lp->var->strname);
    else
	snprintf(litname, sizeof(ln1), "%s$%d", n, lp->var->vix);
    return litname;
}

char* format_lit(varp_t* vp, lit_t l)
{
    return format_literal(vp, l2ll(vp, l));
}

#if defined(DEBUG_BCP)
#define PRINT_CLAUSE(vp,msg,cp) print_clause((vp),(msg),(cp))
#else
#define PRINT_CLAUSE(vp,msg,cp)
#endif

#if defined(DEBUG)
#define PRINT_LIT_ARRAY(msg,lit,size) print_lit_array((msg),(lit),(size))
#else
#define PRINT_LIT_ARRAY(msg,lit,size)
#endif

char* format_ival(ival_t v)
{
    switch(v) {
    case I_UNDEF: return "u";
    case I_FALSE: return "f";
    case I_TRUE:  return "t";
    case I_BOUND:  return "U";
    default: return "?";
    }
}

void print_ll(literal_t* lp)
{
    int vix;
    if ((vix=lp->var->vix) == 0) {
	if (lp->sign)
	    enif_fprintf(stdout, "f");
	else
	    enif_fprintf(stdout, "t");
    }
    else {
	if (lp->sign)
	    enif_fprintf(stdout, "-%d", vix);
	else
	    enif_fprintf(stdout, "%d", vix);	
    }
}

void print_lit(lit_t l)
{
#ifdef LIT_INTEGER
    if (l == ULIT_TRUE)
	enif_fprintf(stdout, "t");
    else if (l == ULIT_FALSE)
	enif_fprintf(stdout, "f");
    else if (SIGN(l))
	enif_fprintf(stdout, "-%d", INDEX(l));
    else
	enif_fprintf(stdout, "%d", INDEX(l));
#else
    print_ll((literal_t*) l);
#endif
}

void print_lit_array(char* label, lit_t* lit, size_t size)
{
    if (size == 0)
	enif_fprintf(stdout, "%s=[]", label);
    else {
	unsigned k;
	enif_fprintf(stdout, "%s=[", label);
	print_lit(lit[0]);
	for (k=1; k<size; k++) {
	    enif_fprintf(stdout, ",");
	    print_lit(lit[k]);
	}
	enif_fprintf(stdout, "]\r\n");
    }
}

void print_clause(varp_t* vp, char* label, clause_t* cp)
{
    unsigned k;
    enif_fprintf(stdout, "%s id=%d,[%ld:%ld] [%d/%s",
		 label, cp->cix, cp->wl[0].p, cp->wl[1].p,
		 export_l(cp->lit[0]),
		 format_ival(get_l(vp,cp->lit[0])));
    for (k=1; k<cp->size; k++)
	enif_fprintf(stdout, ",%d/%s",
		     export_l(cp->lit[k]),
		     format_ival(get_l(vp,cp->lit[k])));
    enif_fprintf(stdout, "]\r\n");
}

void print_sym_clause(varp_t* vp, char* label, clause_t* cp)
{
    unsigned k;
    enif_fprintf(stdout, "%s id=%d,[%ld:%ld] [%s",
		 label, cp->cix, cp->wl[0].p, cp->wl[1].p,
		 format_lit(vp, cp->lit[0]));
    for (k=1; k<cp->size; k++)
	enif_fprintf(stdout, ",%s", format_lit(vp, cp->lit[k]));
    enif_fprintf(stdout, "] dead=%d\r\n", ((cp->flags & CLAUSE_FLAG_DEAD)!=0));
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

// FIXME: add debug info so that pointer contains allocator pointer!
// and check that objects are returned to correct allocator
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

static inline void set_wlink(wlink_t* wlp, long p, literal_t* lp)
{
    wlp->p = p;   // new watch point
    link_wlink(wlp, lp);
}

// FIXME: make constant
static void unwatch_ll(varp_t* vp, clause_t* cp, literal_t* lp)
{
    UNUSED(vp);
    wlink_t** wlp = &lp->wlist;
    wlink_t* wl;

    // DBG("UNWATCH cix=%lu lit=%d wl=%p\r\n", cp->cix, export_ll(lp), *wlp);

    while((wl = *wlp) && (clause_pointer(wl) != cp))
	wlp = &(wl->next);
    if (wl != NULL) {
	*wlp = wl->next;  // unlink
	wl->p = -1;       // mark as not used
    }
}

static inline void unwatch_l(varp_t* vp, clause_t* cp, lit_t l)
{
    unwatch_ll(vp, cp, l2ll(vp, l));
}

// remove the 2-WL watch points
static void unwatch_clause(varp_t* vp, clause_t* cp)
{
    long p;
    if ((p = cp->wl[0].p) >= 0) unwatch_l(vp, cp, cp->lit[p]);
    if ((p = cp->wl[1].p) >= 0) unwatch_l(vp, cp, cp->lit[p]);
}

static void schedule_unwatch_clause(varp_t* vp, clause_t* cp)
{
    if (!(cp->flags & CLAUSE_FLAG_UNWATCH)) {
	cp->uwatch = vp->unwatch;
	cp->flags |= CLAUSE_FLAG_UNWATCH;
	vp->unwatch = cp;
    }
}

static void lqueue_init(lqueue_t* q)
{
    q->head = NULL;
    q->tail = &q->head;
}

static void lqueue_clear(lqueue_t* q)
{
    lqueue_init(q);
}

static inline void lqueue_put_ll(varp_t* vp, literal_t* lp)
{
    lqueue_t* q = &vp->q;

    DBG("ENQ %s\r\n", format_literal(vp,lp));

    if (vp->qtype == lifo) {  // put element first
	lp->qlink = q->head;
	q->head = lp;
	if (lp->qlink == NULL)
	    q->tail = &(lp->qlink);
    }
    else {  // fifo put element last
	lp->qlink = NULL;
	*q->tail = lp;
	q->tail = &(lp->qlink);
    }
}

// always get from head of list(queue)
static inline literal_t* lqueue_get(varp_t* vp)
{
    lqueue_t* q = &vp->q;
    literal_t* lp;
    
    if ((lp = q->head) == NULL)
	return NULL;
    if ((q->head = lp->qlink) == NULL)
	q->tail = &q->head;
    DBG("DEQ %s(%d,%d)\r\n", format_literal(vp,lp),
	lp->var->vix, lp->var->literal_pos);
    return lp;
}

static inline void push_variable(varp_t* vp, variable_t* var, int level)
{
    ASSERT(get_vv(vp, var) == I_UNDEF);
    DBG_BCP("PUSH-VARIABLE: var=%s, level=%d\r\n", format_variable(var), level);
    var->next = vp->undo[level].bs;
    vp->undo[level].bs = var;
    vp->num_bound++;
}

static ERL_NIF_TERM make_cix(ErlNifEnv* env,cix_t cix)
{
    if (cix == CLAUSE_NONE)
	return enif_make_int(env, -1);
    else
	return enif_make_uint(env, cix);
}

static ERL_NIF_TERM make_binding(ErlNifEnv* env, varp_t*vp, variable_t* var)
{
    ASSERT(var->bound == NULL);
    return enif_make_int(env,export_vv(vp, var));
}

static ERL_NIF_TERM make_clause_info(ErlNifEnv* env,varp_t* vp,variable_t* var)
{
    ASSERT(var->bound == NULL);
    return enif_make_tuple3(env,
			    enif_make_int(env,export_vv(vp, var)),
			    enif_make_int(env, var->literal_pos),
			    make_cix(env, var->implication_clause));
}

//
// send message to process(es) interested in permanent assignments
// of variables.
// send either
//     X      for permanent assignment
//     {X, Y} for substitution where Y is replaced by X
//

static int make_sub_info(varp_t* vp,uint32_t flags,ERL_NIF_TERM* info)
{
    ErlNifEnv* env = vp->msg_env;
    ERL_NIF_TERM sub_info_keys[6] = {
	ATOM(number_of_variables),
	ATOM(number_of_bound_variables),
	ATOM(number_of_clauses),
	ATOM(number_of_dead_clauses),
	ATOM(max_level),
	ATOM(max_bound)
    };
    ERL_NIF_TERM values[6] = {
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined)
    };
	
    if (flags & SUB_FLAG_NUM_VARS)
	values[0] = enif_make_int(env, vp->vnum);
    if (flags & SUB_FLAG_NUM_BOUND)
	values[1] = enif_make_int(env, vp->num_bound);
    if (flags & SUB_FLAG_NUM_CLAUSES)
	values[2] = enif_make_int(env, get_number_of_clauses(vp));
    if (flags & SUB_FLAG_NUM_DEAD)
	values[3] = enif_make_int(env, vp->cdead);
    if (flags & SUB_FLAG_MAX_LEVEL) {
	values[4] = enif_make_int(env, vp->max_level);
	vp->max_level = 0;  // and reset
    }
    if (flags & SUB_FLAG_MAX_BOUND) {
	values[5] = enif_make_int(env, vp->max_bound);
	vp->max_bound = 0;  // and reset
    }
    return enif_make_map_from_arrays(env, sub_info_keys, values, 6, info);
}

static void log_permanent_(varp_t* vp, literal_t* x, literal_t* y)
{
    ErlNifEnv* env = vp->msg_env;
    subscription_t* sp = vp->subs;
    
    while(sp != NULL) {
	if ((sp->flags & SUB_FLAG_VAR) ||
	    ((sp->flags & SUB_FLAG_ATOM) &&
	     (x->var->flags & VAR_FLAG_ATOM))) {
	    ERL_NIF_TERM xt;
	    ERL_NIF_TERM yt;
	    ERL_NIF_TERM bnd = ATOM(false);
	    ERL_NIF_TERM info;
	    ERL_NIF_TERM msg;

	    // enif_fprintf(stdout, "log_permanent x=%s\r\n",
	    //  format_literal(vp, x));
		
	    if (y == NULL) {
		xt = external_ll(env,x);
		bnd = xt;
	    }
	    else { // if (y->var->flags & VAR_FLAG_ATOM) {
		yt = external_ll(env,y);
		xt = external_ll(env,x);
		bnd = enif_make_tuple2(env, xt, yt);
	    }

	    if (make_sub_info(vp, sp->flags, &info)) {
		msg = enif_make_tuple3(env, ATOM(varp), bnd, info);
		if (vp->caller_env != NULL) {
		    enif_send(vp->caller_env, &sp->pid, env, msg);
		    enif_clear_env(env);
		}
		else {
		    DBG("caller_env NOT set!!!\r\n");
		}
	    }
	}
	sp = sp->next;
    }
}

static inline void log_permanent(varp_t* vp, literal_t* x,
				 literal_t* y, int level)
{
    if (level != 0) return;
    if (vp->subs == NULL) return;
    log_permanent_(vp, x, y);
}
     
// level=0 work
// after evaluation of a literal in the L literal queue
// schedule all clauses in cross referenced from !L to
// be killed.

static void kill_clauses(varp_t* vp, literal_t* xp)
{
    xref_t* xptr = xp->xfirst;

    DBG_BCP("  kill %s\r\n", format_literal(vp, xp));

    while(xptr) {
	clause_t* cp = get_clause(vp, xptr->cix);
	if (cp && !(cp->flags & CLAUSE_FLAG_DEAD)) { // not alread dead
	    vp->cdead++;
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if ((cp->size == 2) && vp->edge) {
#ifdef DEBUG_EDGE
		print_sym_clause(vp, "  KILL EDGE", cp);
#endif
		; // not watched
	    }
	    else {
#ifdef DEBUG_EDGE
		print_sym_clause(vp, "  SCHEDULE-UNWATCH/KILL", cp);
#endif
		schedule_unwatch_clause(vp, cp);
	    }
	}
	xptr = xptr->next;
    }
}

// insert implication edge a -> b, this will trigger
// when a=1 and yield b=1
static void edge_insert(varp_t* vp, lit_t a, lit_t b, cix_t cix)
{
    edge_t* ep;
    literal_t* ap = l2ll(vp, a);
    
    ep = varp_alloc(&vp->edge_allocator);
    ep->l = b;
    ep->cix = cix;
    ep->next = ap->elist;
    ap->elist = ep;
    vp->nedge++;
}

static void edge_remove(varp_t* vp, lit_t a, lit_t b, cix_t cix)
{
    edge_t* pp;
    literal_t* ap = l2ll(vp, a);
    edge_t** ppp = &ap->elist;
    
    while((pp = *ppp)) {
	if ((pp->l == b) && (pp->cix == cix)) {
	    *ppp = pp->next;
	    varp_free(&vp->edge_allocator, pp);
	    vp->nedge--;
	    return;
	}
	ppp = &(pp->next);
    }
}

static void put_nq_ll(varp_t* vp, literal_t* lp, ival_t ivalue,
		      pos_t li, cix_t cix, int level)
{
    variable_t* var = lp->var;

    DBG_BCP("PUT-LITERAL %s@%d = %s\r\n", format_literal(vp,lp), level,
	    format_ival(ivalue));
    ASSERT(level >= 0);
    ASSERT(var->bound == NULL);    
    ASSERT(!IS_CONSTANT(get_vv(vp, var)));

    push_variable(vp, var, level);

    set_vv(vp, var, lp->sign ? NEGATE(ivalue) : ivalue);
    var->implication_clause = cix;
    var->literal_pos = li;
    var->level = level;
    log_permanent(vp, lp, NULL, level);
}

static void put_ll(varp_t* vp, literal_t* lp, ival_t ivalue,
		   pos_t li, cix_t cix, int level)
{
    put_nq_ll(vp, lp, ivalue, li, cix, level);
    if (IS_CONSTANT(ivalue))
	lqueue_put_ll(vp, (ivalue==I_TRUE) ? neg_ll(lp) : lp);
}

static inline void put_l(varp_t* vp,lit_t l,ival_t ivalue,
			 pos_t li, cix_t cix, int level)
{
    put_ll(vp,l2ll(vp, l),ivalue,li,cix,level);
}

static void init_level(varp_t* vp, int level)
{
    vp->undo[level].decision = L_FALSE(vp);
    vp->undo[level].t  = 0;
    vp->undo[level].ix = 0;	
    vp->undo[level].bs = NULL;    
}

static void undo_init(varp_t* vp)
{
    int i;
    vp->unum = DEFAULT_UNDO_SIZE;
    vp->undo = VARP_ALLOC(DEFAULT_UNDO_SIZE * sizeof(undo_t));
    for (i = 0; i < DEFAULT_UNDO_SIZE; i++)
	init_level(vp, i);
    vp->num_bound = 0;
    vp->level = 0;
}

// set current bindings level
static int set_level(varp_t* vp, int level)
{
    if (level >= (int)vp->unum) {
	int i;
	unsigned int n = vp->unum;
	vp->unum *= 2;
	vp->undo = VARP_REALLOC(vp->undo, vp->unum*sizeof(undo_t));
	for (i = n; i < (int)vp->unum; i++)
	    init_level(vp, i);
    }
    vp->level = level;
    if (level > vp->max_level)
	vp->max_level = level;
    DBG("SET-LEVEL: level=%d\r\n", level);
#ifdef ASSERTIONS
    {
	int i;
	for (i = level+1; i < (int)vp->unum; i++) {
	    ASSERT(vp->undo[i].bs == NULL);
	}
    }
#endif
    return 0;
}

static void unbind_level(varp_t* vp, int level)
{
    variable_t* bp = vp->undo[level].bs;
    int nbound = 0;

    while(bp != NULL) {
	ASSERT(bp->bound == NULL);
	DBG_BCP("CLR-VARIABLE %s value=%d\r\n",
		format_variable(bp), get_vv(vp, bp));
	clr_vv(vp, bp);
	bp = bp->next;
	nbound++;
    }
    vp->num_bound -= nbound;
    vp->undo[level].bs = NULL;
}

static void undo_level(varp_t* vp, int level)
{
    unbind_level(vp, level);
    init_level(vp, level);
    lqueue_clear(&vp->q);         // must clear queue
}

// move bindings from src level to dst level
// the bindings are moved last into dst level
static void move_level(varp_t* vp, int src, int dst)
{
    variable_t* var = vp->undo[src].bs;

    if (var) {
	log_permanent(vp, var_literal(vp,var), NULL, dst);
	// find last binding
	while(var->next) {
	    var->level = dst;
	    var = var->next;
	    log_permanent(vp, var_literal(vp,var), NULL, dst);
	}
	var->next = vp->undo[dst].bs;
	var->level = dst;
	vp->undo[dst].bs = vp->undo[src].bs;
	init_level(vp, src);
    }
}

// clear but do not undo a level (keep the bindings)
static void keep_level(varp_t* vp, int level)
{
    vp->undo[level].bs = NULL;
}

// update activity on one level
static void activate_lit_level(varp_t* vp, int level, float delta)
{
    variable_t* bp = vp->undo[level].bs;
    while(bp != NULL) {
	if (get_vv(vp, bp) == I_FALSE)
	    bp->lit[LIT_NEG].activity += delta;
	else
	    bp->lit[LIT_POS].activity += delta;
	bp = bp->next;
    }
}

static void activate_var_level(varp_t* vp, int level, float delta)
{
    variable_t* bp = vp->undo[level].bs;
    while(bp != NULL) {
      bp->activity += delta;
      bp = bp->next;
    }
}

// update activity on all levels (excluding 0 - that is already bound)
static void activate_levels(varp_t* vp, float bump)
{
    int i;

    switch(vp->atype) {
    case mvsids:
      for (i = 1; i <= vp->level; i++)
	activate_var_level(vp, i, bump);
      break;
    case cvsids:
      for (i = 1; i <= vp->level; i++)
	activate_lit_level(vp, i, bump);
      break;
    case off:
    default:
      break;
    }
}

static void activity_decay(varp_t* vp, float decay)
{
  int i;

  switch (vp->atype) {
  case cvsids:
    for (i = 1; i < (int)vp->vnext; i++) {
      vp->var_map[i]->lit[LIT_POS].activity *= decay;
      vp->var_map[i]->lit[LIT_NEG].activity *= decay;
    }
    break;
  case mvsids:
    for (i = 1; i < (int)vp->vnext; i++) {
      vp->var_map[i]->activity *= decay;
    }
    break;
  case off:
  default:
    break;
  }
}

static void init_literal(literal_t* lp, variable_t* var, uint32_t sign)
{
    lp->sign     = sign;
    lp->degree   = 0;
    lp->l        = MAKE_LIT(var->vix,sign);
    lp->activity = ACTIVITY_INIT;
    lp->var      = var;
    lp->wlist    = NULL;
    lp->qlink    = NULL;
    lp->elist    = NULL;
    lp->xfirst   = NULL;
    lp->xlast    = &lp->xfirst;
}

static void init_variable(varp_t* vp, variable_t* var, int vix)
{
    var->vix       = vix;
    var->next      = NULL;    
    var->flags     = 0;
    var->bound     = NULL;
    var->pkey[0]   = var->pkey[1] = 0.0f;
    var->nkey[0]   = var->nkey[1] = 0.0f;    
    var->activity  = ACTIVITY_INIT;
    var->map_index = vix;
    var->implication_clause = CLAUSE_NONE;
    var->literal_pos = -1;
    var->level = -1;
    var->strname = NULL;
    var->names = NULL;
    clr_vv(vp, var);
    init_literal(&var->lit[LIT_POS], var, LIT_POS);
    init_literal(&var->lit[LIT_NEG], var, LIT_NEG);
}


// FIXME clauses should really be heap allocated?
// except we need to garbage collect in that case when
// deleting clauses...or

static clause_t* clause_alloc(varp_t* vp, int size)
{
    UNUSED(vp);
    clause_t* cp;
    int r;
    size_t nbytes;
    
    if (size < 1)
	return NULL;
    nbytes = sizeof(clause_t) + sizeof(lit_t)*size;
#if defined(__WIN32__)
    if ((cp = _aligned_malloc(nbytes, CLAUSE_ALIGNMENT)) == NULL) {
      return NULL;
    }
#else
    if ((r=posix_memalign((void**)&cp, CLAUSE_ALIGNMENT, nbytes)) != 0) {
	errno = r;
	return NULL;
    }
#endif
    clear_wlink(&cp->wl[0]);
    clear_wlink(&cp->wl[1]);
    cp->size  = size;
    cp->flags = 0;
    return cp;
}

static void clause_hash_unlink(varp_t* vp, clause_t* cp)
{
    if (vp->clause_hash) {
	hlink_t** hpp = &vp->clause_hash[cp->hvalue & (vp->chsize-1)];
	while(*hpp) {
	    hlink_t* hp = *hpp;
	    if (hp->cix == cp->cix) {
		*hpp = hp->next;
		varp_free(&vp->hlink_allocator, hp);
		return;
	    }
	    hpp = &(hp->next);
	}
	DBG("clause %d not found in hash table\r\n", cp->cix);
    }
}

static void clause_free(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	cix_t cix;
	if ((cix = cp->cix) != CLAUSE_NONE) {
	    clause_hash_unlink(vp, cp);
	    set_clause(vp, cix, NULL);
	    vp->cnum[GET_SI(cix)]--;
	}
#if defined(__WIN32__)
	_aligned_free(cp);
#else
	free(cp);
#endif
    }
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

// if clause is already installed return index to installed clause if success
// return CLAUSE_NONE otherwise
cix_t clause_find(varp_t* vp, lit_t* lit, size_t size)
{
    uint32_t hvalue = (uint32_t) literal_array_hash(vp, lit, size);
    
    if (vp->clause_hash) {
	hlink_t* hp = vp->clause_hash[hvalue & (vp->chsize-1)];

	// enif_fprintf(stdout, "find hvalue=%u ", hvalue);
	// print_lit_array("", lit, size);
	
	while(hp) {
	    if (hp->hvalue == hvalue) {
		clause_t* cp = get_clause(vp, hp->cix);
		ASSERT(cp != NULL);
		if ((cp->size == size) && clause_is_equal(lit, cp->lit, size)) {
		    // enif_fprintf(stdout, "found %d\r\n", cp->cix);
		    return cp->cix;
		}
	    }
	    hp = hp->next;
	}
	// enif_fprintf(stdout, "not found\r\n");	    
    }
    else {
	int si;
	DBG("warning slow clause_find in use\r\n");
	// enif_fprintf(stdout, "find hvalue=%u ", hvalue);
	// print_lit_array("", lit, size);
	for (si = 0; si < NUM_CSET; si++) {
	    int ix;
	    for (ix = 0; ix < (int)vp->cnext[si]; ix++) {
		clause_t* cp = get_clause(vp, MAKE_CIX(si,ix));
		if ((cp != NULL) &&
		    (cp->size == size) &&
		    (cp->hvalue == hvalue) &&
		    clause_is_equal(lit, cp->lit, size)) {
		    // enif_fprintf(stdout, "found %d\r\n", cp->cix);
		    return cp->cix;
		}
	    }
	}
	// enif_fprintf(stdout, "not found\r\n");
    }
    return CLAUSE_NONE;
}

// assume cp->hvalue has been set!
static int clause_hash_link(varp_t* vp, clause_t* cp)
{
    if (vp->clause_hash) {  // insert in clause hash table
	size_t chsize = vp->chsize;	
	hlink_t* hp;
	int hix;
	if ((hp = varp_alloc(&vp->hlink_allocator)) == NULL)
	    return -1;
	hp->hvalue = cp->hvalue;
	hp->cix  = cp->cix;
	vp->chnum++;

	if (vp->chnum >= chsize) {  // rehash, fixme set ratio! like 75% ..
	    size_t chsize1 = chsize*2;
	    int i;
	    hlink_t** clause_hash1 = VARP_ALLOC(chsize1*sizeof(hlink_t**));

	    memset(clause_hash1, 0, chsize1*sizeof(hlink_t**));
	    for (i = 0; i < (int)chsize; i++) {
		hlink_t* hp1 = vp->clause_hash[i];
		while(hp1 != NULL) {
		    hlink_t* hpn = hp1->next;		
		    int hjx = hp1->hvalue & (chsize1 - 1);
		    hp1->next = clause_hash1[hjx];
		    clause_hash1[hjx] = hp1;
		    hp1 = hpn;
		}
		vp->clause_hash[i] = NULL;
	    }
	    VARP_FREE(vp->clause_hash);
	    vp->clause_hash = clause_hash1;
	    vp->chsize = chsize1;
	}
	// link hash bucket list
	hix = cp->hvalue & (vp->chsize -1 );
	hp->next = vp->clause_hash[hix];
	vp->clause_hash[hix] = hp;
    }
    return 0;
}

static cix_t clause_insert(varp_t* vp, int si, clause_t* cp, uint32_t hvalue)
{
    uint32_t ix = vp->cnext[si]++;
    cix_t cix = MAKE_CIX(si,ix);
    
    cp->cix = cix;
    cp->stamp = vp->bcp_counter;
    cp->hvalue = hvalue;
    
    if (ix >= vp->csize[si]) {
	uint32_t new_csize = vp->csize[si] + vp->grow;
	clause_t** cpp;
	
	if (!(cpp = VARP_REALLOC(vp->clause_map[si],
				 new_csize*sizeof(clause_t*))))
	    return CLAUSE_NONE;
	vp->clause_map[si] = cpp;
	vp->csize[si] = new_csize;
    }
    vp->cnum[si]++;
    set_clause(vp, cix, cp);

    clause_hash_link(vp, cp);

    return cix;
}

static int vif_get_boolean(ErlNifEnv* env, ERL_NIF_TERM term, bool_t* bool)
{
    (void) env;
    if (term == ATOM(true))
	*bool = true;
    else if (term == ATOM(false))
	*bool = false;
    else
	return 0;
    return 1;
}

static ERL_NIF_TERM make_boolean(ErlNifEnv* env, int value)
{
    (void) env;
    return value ? ATOM(true) : ATOM(false);
}

static int vif_get_number(ErlNifEnv* env,ERL_NIF_TERM arg,double* dp)
{
    if (!enif_get_double(env, arg, dp)) {
	int i;
	if (!enif_get_int(env, arg, &i))
	    return 0;
	*dp = (double) i;
    }
    return 1;
}

// get primitive literal value
static int vif_get_ll(ErlNifEnv* env,varp_t* vp,ERL_NIF_TERM arg,
		      literal_t** lpp)
{
    int x;
    if (enif_get_int(env, arg, &x)) {
	if (x == 0)
	    return 0;
	else if (ABS(x) < (int)vp->vnext)
	    *lpp = vindex_ll(vp, x);
	else {
	    DBG("literal %d out of range\r\n", x);
	    return 0;
	}
    }
    else if (arg == ATOM(t))
	*lpp = LL_TRUE(vp);
    else if (arg == ATOM(f))
	*lpp = LL_FALSE(vp);
    else return 0;
    return 1;
}

// get primitive lit value
static int vif_get_l(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, lit_t* l)
{
    int x;
    if (enif_get_int(env, arg, &x)) {
	if (x == 0)
	    return 0;
	else if (ABS(x) < (int)vp->vnext)
	    *l = vindex_l(vp, x);
	else {
	    DBG("literal %d out of range\r\n", x);
	    return 0;
	}
    }
    else if (arg == ATOM(t)) *l = L_TRUE(vp);
    else if (arg == ATOM(f)) *l = L_FALSE(vp);
    else return 0;
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

static int vif_get_cix(ErlNifEnv* env,varp_t* vp,ERL_NIF_TERM term,cix_t* cixp)
{
    unsigned int cix;
    int ix, si;
    if (!enif_get_uint(env, term, &cix))
	return 0;
    if ((si = GET_SI(cix)) >= NUM_CSET)
	return 0;
    if ((ix = GET_IX(cix)) >= (int)vp->cnext[si])
	return 0;
    *cixp = cix;
    return 1;
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, literal_t* lp)
{
    return enif_make_int(env, export_ll(lp));
}

static void cleanup(varp_t* vp)
{
    int si;
    
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

    if (vp->clause_hash) {
	VARP_FREE(vp->clause_hash);
	vp->clause_hash = NULL;		    
    }
    
    if (vp->var_map) {
	VARP_FREE(vp->var_map);
	vp->var_map = NULL;
    }
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
    if (vp->lit_value) {    
	VARP_FREE(vp->lit_value);
	vp->lit_value = NULL;
	vp->lit_overlay = NULL;
    }
#else
    if (vp->var_value) {
	VARP_FREE(vp->var_value);
	vp->var_value = NULL;
    }
#endif
#endif
    
    if (vp->order_map) {
	VARP_FREE(vp->order_map);
	vp->order_map = NULL;
    }

    for (si = 0; si < NUM_CSET; si++) {
	if (vp->clause_map[si] != NULL) {
	    clause_t** cm = vp->clause_map[si];
	    int n = (int) vp->cnext[si];
	    int i;
	    for (i = 0; i < n; i++) {
		clause_t* cp = cm[i];
		clause_free(vp, cp);
	    }
	}
	VARP_FREE(vp->clause_map[si]);
	vp->clause_map[si] = NULL;
    }

    if (vp->undo) {
	VARP_FREE(vp->undo);
	vp->undo = NULL;
    }
    
    cleanup_allocator(&vp->var_allocator);
    cleanup_allocator(&vp->sym_allocator);
    cleanup_allocator(&vp->xref_allocator);
    cleanup_allocator(&vp->sub_allocator);
    cleanup_allocator(&vp->edge_allocator);
    cleanup_allocator(&vp->hlink_allocator);
}

static ERL_NIF_TERM varp_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int grow   = DEFAULT_MAP_GROW;
    unsigned int vsize  = DEFAULT_MAP_SIZE;
    unsigned int csize  = DEFAULT_MAP_SIZE;
    size_t ssize;
    ERL_NIF_TERM t;
    ERL_NIF_TERM list = argv[0];
    ERL_NIF_TERM head, tail;
    qtype_t qtype = lifo;
    atype_t atype = off;
    bool_t clause_hash = false;
    bool_t edge = false;
    bool_t xref = false;
    int i;
    
    DBG("new varc instance\r\n");
    
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
	else if ((elem[0] == ATOM(qtype)) && (elem[1] == ATOM(fifo))) {
	    qtype = fifo;
	}
	else if ((elem[0] == ATOM(qtype)) && (elem[1] == ATOM(lifo))) {
	    qtype = lifo;
	}
	else if ((elem[0] == ATOM(qtype)) && (elem[1] == ATOM(recursive))) {
	    qtype = recursive;
	}	
	else if (elem[0] == ATOM(activity) && (elem[1] == ATOM(mvsids))) {
	    atype = mvsids;
	}
	else if (elem[0] == ATOM(activity) && (elem[1] == ATOM(cvsids))) {
	    atype = cvsids;
	}
	else if (elem[0] == ATOM(activity) && (elem[1] == ATOM(off))) {
	    atype = off;
	}	
	else if (elem[0] == ATOM(xref) && (elem[1] == ATOM(true))) {
	    xref = true;
	}
	else if (elem[0] == ATOM(xref) && (elem[1] == ATOM(false))) {
	    xref = false;
	}	
	else if (elem[0] == ATOM(clause_hash) && (elem[1] == ATOM(true))) {
	    clause_hash = true;
	}
	else if (elem[0] == ATOM(clause_hash) && (elem[1] == ATOM(false))) {
	    clause_hash = false;
	}
	else if (elem[0] == ATOM(edge) && (elem[1] == ATOM(true))) {
	    edge = true;
	}
	else if (elem[0] == ATOM(edge) && (elem[1] == ATOM(false))) {
	    edge = false;
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

    vp->qtype = qtype;
    vp->atype = atype;
    vp->xref = xref;
    vp->edge = edge;
    vp->vnext = 1;
    vp->vsize = vsize;
    vp->vnum  = 0;

    vp->grow = grow;
    if (!(vp->var_map = VARP_ALLOC(vsize*sizeof(variable_t**))))
	goto error;
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
    if (!(vp->lit_value = VARP_ALLOC(2*PACKED_BYTES(vsize)*sizeof(uint8_t))))
	goto error;
    vp->lit_overlay = (uint16_t*) vp->lit_value;
#else
    if (!(vp->var_value = VARP_ALLOC(PACKED_BYTES(vsize)*sizeof(uint8_t))))
	goto error;
#endif
#endif    
    ssize = 1;
    while(ssize < vsize) ssize *= 2;
    if (!(vp->sym_map = VARP_ALLOC(ssize*sizeof(symbol_t**))))
	goto error;
    memset(vp->sym_map, 0, ssize*sizeof(symbol_t**));
    vp->ssize = ssize;
    vp->snum = 0;

    vp->chsize = 0;
    vp->chnum = 0;
    if (clause_hash) {
	size_t chsize = 1;
	while(chsize < csize) chsize *= 2;
	if (!(vp->clause_hash = VARP_ALLOC(chsize*sizeof(hlink_t**))))
	    goto error;
	memset(vp->clause_hash, 0, chsize*sizeof(hlink_t**));
	vp->chsize = chsize;
    }
    
    if (!(vp->order_map = VARP_ALLOC(vsize*sizeof(int))))
	goto error;
    
    for (i = 0; i < NUM_CSET; i++) {
	vp->cnext[i] = 0;
	vp->csize[i] = 0;
	vp->cnum[i] = 0;
	vp->coffs[i] = 0;
	vp->clause_map[i] = NULL;
    }
    vp->csize[0] = csize;
    vp->cdead = 0;
    vp->edead = 0;    

    vp->unwatch = NULL;
    
    if (!(vp->clause_map[0] = VARP_ALLOC(csize*sizeof(clause_t*))))
	goto error;

    if (init_allocator(&vp->var_allocator, sizeof(variable_t)) < 0)
	goto error;
    if (init_allocator(&vp->sym_allocator, sizeof(symbol_t)) < 0)
	goto error;
    if (init_allocator(&vp->xref_allocator, sizeof(xref_t)) < 0)
	goto error;
    if (init_allocator(&vp->sub_allocator, sizeof(subscription_t)) < 0)
	goto error;
    if (init_allocator(&vp->edge_allocator, sizeof(edge_t)) < 0)
	goto error;
    if (init_allocator(&vp->hlink_allocator, sizeof(hlink_t)) < 0)
	goto error;        

    lqueue_init(&vp->q);
    undo_init(vp);

    // transient statistics
    vp->max_level = 0;
    vp->max_bound = 0;

    vp->max_conflicting = MAX_CONFLICTING;
    vp->bcp_counter = 0;
    vp->conflict_counter = 0;    
    vp->counter[CLAUSE_N] = 0;   // n-clause (n > 3)
    vp->counter[CLAUSE_2] = 0;   // 2-clause
    vp->counter[CLAUSE_3] = 0;   // 3-clause
    vp->counter[CLAUSE_D] = 0;   // dead clause counter
    vp->counter[EDGE_2] = 0;     // trigger list
    vp->counter[EDGE_D] = 0;     // "dead" rules

    vp->order_map[0] = 0;
    init_variable(vp, &vp->constant, 0);
    vp->var_map[0] = &vp->constant;
    set_vv(vp, &vp->constant, I_TRUE);
    
    arc4_init(&vp->as);

    vp->subs = NULL;
    vp->msg_env = enif_alloc_env();
    vp->caller_env = NULL;
    
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
    int vix;
    variable_t* var;
    bool_t is_atom;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!vif_get_boolean(env, argv[1], &is_atom))
	return enif_make_badarg(env);

    if (vp->vnext >= VLIMIT)
	enif_raise_exception(env, ATOM(system_limit));

    if ((var = varp_alloc(&vp->var_allocator)) == NULL)
	return enif_make_badarg(env);

    vix = (int) vp->vnext++;
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
#ifdef LIT_VALUE
	if (!(ptr = VARP_REALLOC(vp->lit_value,
				 2*PACKED_BYTES(new_vsize)*sizeof(uint8_t))))
	    return enif_make_badarg(env);
	vp->lit_value = ptr;
	vp->lit_overlay = (uint16_t*) ptr;
#else
	if (!(ptr = VARP_REALLOC(vp->var_value,
				 PACKED_BYTES(new_vsize)*sizeof(uint8_t))))
	    return enif_make_badarg(env);
	vp->var_value = ptr;
#endif
#endif	
	vp->vsize = new_vsize;
    }
    vp->vnum++;
    vp->order_map[vix] = vix;
    init_variable(vp, var, vix);
    vp->var_map[vix] = var;
    if (is_atom) var->flags |= VAR_FLAG_ATOM;
    return enif_make_int(env, vix);
}


// varc:del_variable(Vp:varc(), Index::integer()) -> integer()
static ERL_NIF_TERM varp_del_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);

    // check that variable is not referenced
    if ((var->lit[0].degree != 0) || (var->lit[1].degree != 0))
	return enif_make_badarg(env);
    ASSERT(var->lit[0].xfirst == NULL);
    ASSERT(var->lit[1].xfirst == NULL);
    
    // we should be able to delete the variable at this point
    // FIXME
    return ATOM(ok);
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

// get variable info
static ERL_NIF_TERM varp_variable_info(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_variable(env, vp, argv[1], &var))
	return enif_make_badarg(env);

    if (argv[2] == ATOM(implication)) {
	return enif_make_tuple3(env,
				make_cix(env, var->implication_clause),
				enif_make_int(env, var->literal_pos),
				enif_make_int(env, var->level));
    }
    if (argv[2] == ATOM(implication_clause))
	return make_cix(env, var->implication_clause);
    if (argv[2] == ATOM(implication_pos))
	return enif_make_int(env, var->literal_pos);
    if (argv[2] == ATOM(activity))
	return enif_make_double(env, var->activity);
    if (argv[2] == ATOM(level))
	return enif_make_int(env, var->level);
    if (argv[2] == ATOM(degree))
	return enif_make_uint(env, var->lit[0].degree+var->lit[1].degree);
    if (argv[2] == ATOM(is_atom))
	return make_boolean(env, var->flags & VAR_FLAG_ATOM);
    if (argv[2] == ATOM(symbol)) {
	symbol_t* sp = var->names;
	ERL_NIF_TERM list = enif_make_list(env, 0);
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
    return enif_make_badarg(env);    
}

// get literal info
static ERL_NIF_TERM varp_literal_info(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);

    if (argv[2] == ATOM(degree)) {
	return enif_make_uint(env, lp->degree);
    }
    if (argv[2] == ATOM(activity)) {
	return enif_make_double(env, lp->activity);
    }    
    if (argv[2] == ATOM(user)) {
	return enif_make_uint(env, lp->user);
    }
    if (argv[2] == ATOM(edge)) {
	ERL_NIF_TERM list = enif_make_list(env, 0);
	edge_t* ep = lp->elist;
	
	while(ep) {
	    ERL_NIF_TERM elem = enif_make_int(env, export_l(ep->l));
	    list = enif_make_list_cell(env, elem, list);
	    ep = ep->next;
	}
	return list;	
    }
    if (argv[2] == ATOM(symbol)) {
	symbol_t* sp = lp->var->names;
	ERL_NIF_TERM list = enif_make_list(env, 0);
	while(sp != NULL) {
	    ERL_NIF_TERM term;
	    if (sp->is_term) {
		enif_binary_to_term(env,sp->data,sp->size,&term,0);
		if (lp->sign)
		    term = enif_make_tuple2(env, ATOM(exclamation_mark), term);
	    }
	    else {
		size_t size = sp->size + lp->sign;
		uint8_t* data = enif_make_new_binary(env, size, &term);
		if (lp->sign)
		    *data++ = '!';
		memcpy(data, sp->data, sp->size);
	    }
	    list = enif_make_list_cell(env, term, list);
	    sp = sp->anext;
	}
	return list;	
    }
    return enif_make_badarg(env);    
}


static int order_next(varp_t* vp, int i, int skip)
{
    while(i < (int)vp->vnext) {
	if (!vis_bound(vp, vp->order_map[i])) {
	    if (!skip) return i;
	    skip--;
	}
	i++;
    }
    return 0;
}

static ERL_NIF_TERM varp_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if ((i = order_next(vp, 1, 0)) > 0)
	return enif_make_tuple2(env,enif_make_int(env, i),
				enif_make_int(env,  vp->order_map[i]));
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
    if (!enif_get_int(env, argv[1], &i) || (i < 0))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &skip) || (skip < 0))
	return enif_make_badarg(env);
    if ((i = order_next(vp, i+1, skip)) > 0)
	return enif_make_tuple2(env,enif_make_int(env, i),
				enif_make_int(env,  vp->order_map[i]));
    return ATOM(false);
}


#define ORDER_UNDEFINED  0x00   // "zero" order
#define ORDER_IDENTITY   0x01   // "input" order
#define ORDER_RANDOM     0x02   // "random" order
#define ORDER_DEGREE     0x03   // order according to occurence
#define ORDER_RANK       0x04   // 1/n1+...1/nk where ni is size of clause i
#define ORDER_ACTIVITY   0x05   // order according to conflict activity
#define ORDER_USER       0x06   // order according to user count

#define ORDER_ASCEND     0x00   // ascending order
#define ORDER_DESCEND    0x80   // descending order
#define ORDER_INTERLEAVE 0x40   // interleve order


// install variables as:
// bound-variables 0,1,...b  unbound-variables u....n
// return u (first unbound index)
//
static int order_reset(varp_t* vp)
{
    int i, l, u;

    vp->order_map[0] = 0;
    vp->var_map[0]->map_index = 0;
    l = 0;
    u = vp->vnext;

    for (i=(int)vp->vnext-1; i >= 1; i--) {
	if (vis_bound(vp, i)) {
	    l++;
	    vp->order_map[l] = i;
	    vp->var_map[i]->map_index = l;
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
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = (float) i + 0.1;  // make the positive side "win"
	var->nkey[k] = (float) i;
    }
}

// + order means only positive literals
// - order means only negative literals
// = order means interleaved positive and negative literals
static void order_k_random(varp_t* vp, int k, int order)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	float v1 = arc4_random_uniform(&vp->as, 0x7fffff) / (float)0x7fffff;
	float v2 = arc4_random_uniform(&vp->as, 0x7fffff) / (float)0x7fffff;

	if (order & ORDER_INTERLEAVE) {
	    var->pkey[k] = v1;
	    var->nkey[k] = v2;
	}
	else if (order & ORDER_DESCEND) {
	    var->pkey[k] = v1;
	    var->nkey[k] = v1+0.1;  // negative win
	}
	else {
	    var->pkey[k] = v1+0.1;  // positive win
	    var->nkey[k] = v1;
	}	
    }
}

static void order_k_undefined(varp_t* vp, int k)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = 0.0f;
	var->nkey[k] = 0.0f;
    }
}

// scan through all variables and calculate the degree count
static void order_k_degree(varp_t* vp, int k)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = var->lit[LIT_POS].degree;
	var->nkey[k] = var->lit[LIT_NEG].degree;
    }
}

// scan through all variables and calculate the "rank"
// foreach literal calculate Rj = Sum(1/Ni) where ni is the
// size of the clause that the literal Lj is a member
static void order_k_rank(varp_t* vp, int k)
{
    int i, si;
    int vmax = (int) vp->vnext;
    int vmin = -vmax;
    
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];	
	var->pkey[k] = 0.0f;
	var->nkey[k] = 0.0f;
    }

    for (si = 0; si < NUM_CSET; si++) {
	int n = (int)vp->cnext[si];
	clause_t** cm = vp->clause_map[si];
	for (i = 0; i < n; i++) {
	    clause_t* cp = cm[i];
	    int j;
	    if (cp != NULL) {
		int n = cp->size;
		if (n > 0) {
		    float r = 1/(float)n;
		    for (j = 0; j < n; j++) {
			int x = export_l(cp->lit[j]);
			if ((x > 0) && (x < vmax))
			    vp->var_map[x]->pkey[k] += r;
			else if ((x < 0) && (x > vmin))
			    vp->var_map[-x]->nkey[k] += r;
		    }
		}
	    }
	}
    }
}

// Set sort key k to the activity level on the variable
static void order_k_activity(varp_t* vp, int k)
{
    int i;

    switch(vp->atype) {
    case mvsids:
      for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = var->activity;
	var->nkey[k] = var->activity;
      }
      break;
    case cvsids:
      for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = var->lit[LIT_POS].activity;
	var->nkey[k] = var->lit[LIT_NEG].activity;
      }
      break;
    case off:
    default:
      for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = 0.0f;
	var->nkey[k] = 0.0f;
      }
      break;
    }
}

// Set sort key k to the user level on the literal
// FIXME: clear user field before set/use
static void order_k_user(varp_t* vp, int k)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = var->lit[LIT_POS].user;
	var->nkey[k] = var->lit[LIT_NEG].user;
    }
}

// this is INSANE!!!
#if defined(__ANDROID__)
// define qsort_r the gnu way

static _Thread_local struct
{
    int (*compar)(const void *, const void *, void *);
    void *arg;
} qsort_state;

static int qsort_compar_wrapper(const void *a, const void *b)
{
    return qsort_state.compar(a, b, qsort_state.arg);
}

void qsort_r(void *base, size_t nmemb, size_t size,
             int (*compar)(const void *, const void *, void *),
             void *arg)
{
    int (*saved_compar)(const void *, const void *, void *) = qsort_state.compar;
    void *saved_arg = qsort_state.arg;
    qsort_state.compar = compar;
    qsort_state.arg = arg;
    qsort(base, nmemb, size, qsort_compar_wrapper);
    qsort_state.compar = saved_compar;
    qsort_state.arg = saved_arg;
}

#endif

#if defined(_GNU_SOURCE)
#define QSORT(base,nmemb,size,compar,arg) \
    qsort_r((base),(nmemb),(size),(compar),(arg))
#define QSORT_ARGS(a,b,arg) (a, b, arg)
#elif defined(__WIN32__)
#define QSORT(base,nmemb,size,compar,arg) \
    qsort_s((base),(nmemb),(size),(compar),(arg))
#define QSORT_ARGS(a,b,arg) (arg, a, b)
#elif defined(__APPLE__)
#define QSORT(base,nmemb,size,compar,arg) \
    qsort_r((base),(nmemb),(size),(arg),(compar))
#define QSORT_ARGS(a,b,arg) (arg, a, b)
#endif

//
//   1 2 3 4 5 6 => 1 6 2 5 3 4
//   6 5 4 3 2 1
//
//

static int cmpk(variable_t* ap, variable_t* bp, int k)
{
    float a = MAX(ap->pkey[k],ap->nkey[k]);
    float b = MAX(bp->pkey[k],bp->nkey[k]);
    if (a < b) return -1;
    else if (a > b) return 1;
    return 0;
}

static int cmp_keys QSORT_ARGS(const void* a, const void* b,void* arg)
{
    varp_t* vp = (varp_t*) arg;
    int k1 = vp->sort_key[0];
    int k2 = vp->sort_key[1];
    variable_t* ap = vp->var_map[*((int*)a)];
    variable_t* bp = vp->var_map[*((int*)b)];
    int r = 0;

    // k1=0 means key[k1] is undefined, k2=0 means key[k2] is undefined
    if (k1 > 0) {
	if ((r = cmpk(ap, bp, k1-1)) != 0)
	    return r;
    }
    else if (k1 < 0) {
	if ((r = cmpk(bp, ap, -k1-1)) != 0)
	    return r;
    }
    if (k2 > 0)
	r = cmpk(ap, bp, k2-1);
    else if (k2 < 0)
	r = cmpk(bp, ap, -k2-1);
    return r;
}


static ERL_NIF_TERM varp_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    (void) argc;
    varp_t* vp;
    int arg = 0;
    int i, u;
    int order[2];
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (!enif_get_int(env, argv[1], &order[0]))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &order[1]))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[3], &arg))
	return enif_make_badarg(env);

    if (((order[0] & 0x0f) == ORDER_RANDOM) ||
	((order[1] & 0x0f) == ORDER_RANDOM)) {
	if (!arg)
	    arc4_stir(&vp->as);
	else {
	    arc4_init(&vp->as);
	    arc4_add_random(&vp->as, (uint8_t*)&arg, sizeof(arg));
	}
    }

    // generate the sort keys 0 and 1
    for (i = 1; i < 3; i++) {
	int k = i;
	switch(order[i-1] & 0x0f) {
	case ORDER_IDENTITY:
	    order_k_identity(vp, k-1);
	    break;
	case ORDER_UNDEFINED:
	    order_k_undefined(vp, k-1);
	    k = 0;
	    break;
	case ORDER_RANDOM:
	    order_k_random(vp, k-1, order[i-1]);
	    break;
	case ORDER_DEGREE:
	    order_k_degree(vp, k-1);
	    break;
	case ORDER_RANK:
	    order_k_rank(vp, k-1);
	    break;
	case ORDER_ACTIVITY:
	    order_k_activity(vp, k-1);
	    break;
	case ORDER_USER:
	    order_k_user(vp, k-1);
	    break;
	default:
	    return enif_make_badarg(env);
	}
	if (order[i-1] & ORDER_DESCEND)
	    k = -k;
	vp->sort_key[i-1] = k;
    }
    // install identity order
    u = order_reset(vp);

#ifdef DEBUG_ORDER
    enif_fprintf(stdout, "u = %d\r\n", u);
    enif_fprintf(stdout, "#bound = %d\r\n", vp->num_bound);
    enif_fprintf(stdout, "#unbound = %d\r\n", vp->vnum - vp->num_bound);
    enif_fprintf(stdout, "vnext = %d\r\n", (int)vp->vnext);

    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	enif_fprintf(stdout, "[%d]=([%f,%f],%d) ", var->vix,
		     var->pkey[0], var->nkey[0],
		     var->map_index);
    }
    enif_fprintf(stdout, "\r\n");
#endif
    // sort unbound variables according to sort_keys
    if (u < (int)vp->vnext) {
	int i;
	int k1, k2;

	QSORT(vp->order_map+u, vp->vnext-u, sizeof(int), cmp_keys, vp);

	k1 = ABS(vp->sort_key[0]);
	k2 = ABS(vp->sort_key[1]);
	// update map_index of sorted variables also update the sign
	// FIME: update INTERLEAVE SORT 1 2 3 4 5 6 7 => 1 7 2 6 3 5 4
	// X1/Y1 X1/Y2 X1/Y2  X2/Y
	for (i = u; i < (int)vp->vnext; i++) {
	    int v = vp->order_map[i];
	    variable_t* var = vp->var_map[v];
	    float r;
	    
	    var->map_index = i;
	    r = var->pkey[k1] - var->nkey[k1];
	    if (ABS(r) < EPSILON)
		r = (var->pkey[k2] - var->nkey[k2]);
	    if (r < 0.0)
		vp->order_map[i] = -v;
	}
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
    mi = 1;
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
	    map[mi++] = export_ll(lp);
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
    mi = 1;
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
	    map[mi] = export_ll(lp);
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
// value(Vct,X) -> t|f|undefined.
//
static ERL_NIF_TERM varp_value(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t x;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    switch(get_l(vp, x)) {
    case I_TRUE:  return ATOM(t);
    case I_FALSE: return ATOM(f);
    case I_UNDEF: return ATOM(undefined);
    case I_BOUND: return ATOM(undefined);
    default: return enif_make_int(env, 0);
    }
}

static ERL_NIF_TERM varp_key(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;    
    literal_t* xp;
    int x;    
    int k;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if ((x == 0) || (ABS(x) >= (int)vp->vnext)) {
	DBG("literal %d out of range\r\n", x);
	return enif_make_badarg(env);
    }    
    if (!enif_get_int(env, argv[2], &k))
	return enif_make_badarg(env);
    if ((k < 0) || (k > 1))
	return enif_make_badarg(env);
    xp = vindex_ll(vp, x);
    if (x < 0)
	return enif_make_double(env, xp->var->nkey[k]);
    else
	return enif_make_double(env, xp->var->pkey[k]);
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
    return make_cix(env, var->implication_clause);
}

static ERL_NIF_TERM varp_implication_level(ErlNifEnv* env, int argc,
					   const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    variable_t* var;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return enif_make_int(env, var->level);
}

static ERL_NIF_TERM varp_implication_pos(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    variable_t* var;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    return enif_make_int(env, var->literal_pos);
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
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &i) || (i<0) || (i>vp->num_conflicting))
	return enif_make_badarg(env);
    return make_cix(env, vp->conflicting_clauses[i]);
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
    return make_boolean(env, get_vv(vp, var) != I_UNDEF);
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

// Bind a literal to a value
static ERL_NIF_TERM varp_bind(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    varp_t* vp;
    int level = -1;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp)) {
	return enif_make_badarg(env);
    }
    if (argc == 3) {
	if (!enif_get_int(env, argv[2], &level) || (level < 0) ||
	    (level >= (int)vp->unum))
	    return enif_make_badarg(env);
    }
    if (level < 0) level = vp->level;
    
    switch(get_l(vp, xp)) {
    case I_TRUE:  return ATOM(true);
    case I_FALSE: return ATOM(false);
    case I_BOUND: return enif_make_badarg(env);
    case I_UNDEF:
    default:
	vp->caller_env = env;
	vp->undo[level].decision = xp;
	vp->undo[level].t = 0;
	vp->undo[level].ix = 0;	
	put_l(vp, xp, I_TRUE, -1, -1, level);
	vp->caller_env = NULL; 
	return ATOM(true);
    }
}

static ERL_NIF_TERM varp_set_user_count(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    literal_t* xp;
    int x;
    varp_t* vp;
    unsigned int count;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &x))
	return enif_make_badarg(env);
    if ((x == 0) || (ABS(x) >= (int)vp->vnext)) {
	DBG("literal %d out of range\r\n", x);
	return enif_make_badarg(env);
    }
    if (!enif_get_uint(env, argv[2], &count))
	return enif_make_badarg(env);
    xp = vindex_ll(vp, x);
    xp->user = count;
    return ATOM(ok);
}


// update degree for all literals in a clause
static void update_clause_degree(varp_t* vp, clause_t* cp, int value)
{
    int n = (int)cp->size;
    int i;
    
    for (i = 0; i < n; i++) {
	literal_t* lp = l2ll(vp, cp->lit[i]);
	lp->degree += value;
    }
}

// update activity for all literals in a clause
static void update_clause_activity(varp_t* vp, clause_t* cp, float value)
{
    int n = (int)cp->size;
    int i;

    if (vp->atype == cvsids) {
      for (i = 0; i < n; i++) {
	literal_t* lp = l2ll(vp, cp->lit[i]);
	lp->var->activity += value;
      }
    }
    else if (vp->atype == mvsids) {
      for (i = 0; i < n; i++) {
	literal_t* lp = l2ll(vp, cp->lit[i]);
	lp->activity += value;
      }
    }
}

// insert sort literal level 'l' into la
// while keeping track on position 'p' and literal index 'v'
void insert_sort3(int v, int l, int p, int va[3], int la[3], long pa[3])
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

static int is_unit_clause(varp_t* vp, clause_t* cp)
{
    long p;
    int  unbound = 0;
    
    for (p = 0; p < (long)cp->size; p++) {
	lit_t l = cp->lit[p];
	switch(get_l(vp,l)) {
	case I_TRUE:
	    return 0;
	case I_FALSE:
	    break;
	case I_UNDEF:
	    if (unbound) return 0;
	    unbound++;
	    break;
	case I_BOUND:
	    DBG("is_unit_clause: error literal %d bound\r\n",
		export_l(cp->lit[p]));
	    return 0;
	default:
	    break;
	}
    }
    return 1;
}


// (lp0,level0) track the literal that is bounded
// on the latest level, (lp1,level1) the next highest after
// (lp0,level0)
// setup TWL structure for a clause

static int watch_clause(varp_t* vp, clause_t* cp)
{
    int va[3], la[3];
    long pa[3];
    long p;
    int dead = 0;
    int nfalse = 0;
    int lev;
    
    la[0] = la[1] = la[2] = -1;
    pa[0] = pa[1] = pa[2] = -1;

    for (p = (int)cp->size-1; p >=0; p--) {
	lit_t l = cp->lit[p];
	switch(get_l(vp,l)) {
	case I_TRUE:
	    dead = 1;
	    lev = var_l(vp,l)->level;
	    break;
	case I_FALSE:
	    nfalse++;
	    lev = var_l(vp,l)->level;
	    break;
	case I_UNDEF:
	case I_BOUND:	    
	default:
	    lev = INT_MAX;
	    break;
	}
	insert_sort3(export_l(l),lev,p,va,la,pa);
    }
/*
    DBG("size=%ld, nfalse=%d,\r\n"
	"la[0]=%d,la[1]=%d,la[2]=%d,\r\n"
	"va[0]=%d,va[1]=%d,va[2]=%d,\r\n"
	"pa[0]=%ld,pa[1]=%ld,pa[2]=%ld\r\n",
	cp->size, nfalse,
	la[0], la[1], la[2],
	va[0], va[1], va[2],
	pa[0], pa[1], pa[2]);
*/
    if ((pa[0] < 0) || (pa[1] < 0)) {
	printf("Could not set TWL\r\n");
	return -1;
    }

    // setup watch
    set_wlink(&cp->wl[0], pa[0], l2ll(vp, cp->lit[pa[0]]));
    set_wlink(&cp->wl[1], pa[1], l2ll(vp, cp->lit[pa[1]]));
    
    if ((la[0] == INT_MAX) && (la[1] != INT_MAX)) {
	if (!dead) {
	    DBG("Set UNIT\r\n");
	    put_l(vp, cp->lit[pa[0]], I_TRUE, pa[0], cp->cix, vp->level);
	}
	return 1;
    }
    if (nfalse == (int)(cp->size)) // currently in conflict!
	return 0;
    return 1;
}

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


static void add_xref(varp_t* vp, clause_t* cp, pos_t p)
{
    literal_t* lp   = l2ll(vp, cp->lit[p]);
    xref_t* xp = varp_alloc(&vp->xref_allocator);
    xp->cix  = cp->cix;
    xp->p    = p;
    xp->next = NULL;
    *lp->xlast = xp;
    lp->xlast = &(xp->next);
}

static void xref_clause(varp_t* vp, clause_t* cp)
{
    long n = (long)cp->size;
    long p;
    for (p = 0; p < n; p++)
	add_xref(vp, cp, p);
}

// locate and remove xref link
static inline void del_xref(varp_t* vp, clause_t* cp, pos_t p)
{
    literal_t* lp = l2ll(vp, cp->lit[p]);
    xref_t* xp;
    xref_t** xpp = &lp->xfirst;

    while((xp = *xpp)) {
	if ((xp->cix == cp->cix) && (xp->p == p)) {
	    if (lp->xlast == &xp->next)
		lp->xlast = xpp;
	    *xpp = xp->next;
	    varp_free(&vp->xref_allocator, xp);
	    return;
	}
	xpp = &(xp->next);
    }
    DBG("xref not found for clause %lu pos = %ld\r\n", cp->cix, p);
}

static void unxref_clause(varp_t* vp, clause_t* cp)
{
    long n = (long)cp->size;
    long p;
    
    // add cross reference (config?)
    for (p = 0; p < n; p++)
	del_xref(vp, cp, p);
}

static int link_clause(varp_t* vp, clause_t* cp)
{
    if (vp->xref)
	xref_clause(vp, cp);
    if (vp->edge && (cp->size == 2)) {
	lit_t* lit  = cp->lit;
	edge_insert(vp, neg_l(lit[0]), lit[1], cp->cix);
	edge_insert(vp, neg_l(lit[1]), lit[0], cp->cix);
	cp->wl[0].p = -1;
	cp->wl[1].p = -1;
	// cp->flags |= CLAUSE_FLAG_DEAD;
	DBG("  edge-list added (no watch)\r\n");
	return 1;
    }
    return watch_clause(vp, cp);
}

//  2-clause coding...
//  (Y,A) (Y,B) (Y,C), (X,D) (X,A), (X, Y)
//  !X -> D, A, Y
//  !Y -> A, B, C, X
//  !A -> Y, X
//  !B -> Y
//  !C -> Y
//  !D -> X
//  [X/Y]  -> each L in !Y do in !L find Y and replace with X done
//            move all pairs in !Y to !X
//
//  (X,A) (X,B) (X,C), (X,D) (X,A), (X,X)
//  !A -> X, X (ignore?)
//  !B -> X
//  !C -> X
//  !X -> D, A, X, A, B, C, X
//  !D -> X
//

// FIXME!!!
static void subst_2_clause(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* xp = l2ll(vp, xl);
    literal_t* yp = l2ll(vp, yl);
    literal_t* nyp = neg_ll(yp);   // !Y
    literal_t* nxp = neg_ll(xp);   // !X
    edge_t* pl;

    for (pl = nyp->elist; pl != NULL; pl = pl->next) {
	literal_t* lp = l2ll(vp, pl->l);  // each L in !Y
	literal_t* nlp = neg_ll(lp);
	edge_t* ql;

	for (ql = nlp->elist; ql != NULL; ql = ql->next) {
	    if (ql->l == yl)
		ql->l = xl;
	    // detect X, !X ? FIXME! MUST
	}
    }

    pl = nyp->elist;
    while(pl) {
	edge_t* pl1 = pl->next;
	
	pl->next = nxp->elist;
	nxp->elist = pl;

	pl = pl1;
    }
}

//
// Substitute one literal for an other
// subst(Vp, X, Y)   apply [X/Y]
// Y is removed and replaced by X  ( Y => X )
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
void check_xref_consistence(literal_t* xp)
{
    size_t len = 0;
    xref_t* xptr;
    
    // check consistence of x and !x
    xptr = xp->xfirst;
    while(xptr) {
	xref_t* xptr1 = xptr->next;
	if (xptr1) {
	    ASSERT(xptr->cix < xptr1->cix);
	}
	xptr = xptr1;
	len++;
    }
    ASSERT(xp->degree == len);
}

// substitute one literal
static void subst_ll(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp   = l2ll(vp, yl);
    literal_t* xp   = l2ll(vp, xl);
    literal_t* nxp  = neg_ll(xp);
    xref_t**   xpp  = &xp->xfirst;
    xref_t**  nxpp  = &nxp->xfirst;
    xref_t*    yptr = yp->xfirst;
    
    ASSERT (yp != xp);

#ifdef ASSERTIONS
    // enif_fprintf(stdout, "y-check: %s\r\n", format_literal(vp, yp));
    check_xref_consistence(yp);
#endif

    // reset y xref
    yp->xfirst = NULL;
    yp->xlast  = &yp->xfirst;

    // scan and rewrite all y's into x's
    while(yptr) {
	xref_t* yptr1 = yptr->next;
	cix_t   cix   = yptr->cix;
	clause_t* cp  = get_clause(vp, cix);
	int rewatch = 0;

	ASSERT(yl == cp->lit[yptr->p]);

	if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
	    unwatch_clause(vp, cp);
	    rewatch = 1;
	}
	
	while((*xpp) && ((*xpp)->cix < cix))  // step x
	    xpp = &((*xpp)->next);

	while((*nxpp) && ((*nxpp)->cix < cix))  // step !x
	    nxpp = &((*nxpp)->next);

	if (((*xpp == NULL) || ((*xpp)->cix > cix)) &&
	    ((*nxpp == NULL) || ((*nxpp)->cix > cix))) { // Y only

	    cp->lit[yptr->p] = xl;
	    xp->degree++;
	    yp->degree--;

	    if (rewatch) {
		if (watch_clause(vp, cp) <= 0) {
		    ASSERT(0);
		}
	    }
	    // link in yptr before xp chain
	    yptr->next = *xpp;
	    *xpp = yptr;
	    xpp = &(yptr->next);
	}
	else if ((*xpp != NULL) && ((*xpp)->cix == cix)) { // X, Y
	    cp->lit[yptr->p] = L_FALSE(vp);
	    if (!rewatch && is_unit_clause(vp, cp)) {
		put_ll(vp, xp, I_TRUE, (*xpp)->p, cp->cix, vp->level);
	    }
	    yp->degree--;
	    if (rewatch) {
		if (watch_clause(vp, cp) <= 0) {
		    ASSERT(0);
		}
	    }
	    varp_free(&vp->xref_allocator, yptr);
	}
	else if (*nxpp && ((*nxpp)->cix == yptr->cix)) { // !X, Y
	    cp->lit[yptr->p] = L_TRUE(vp);
	    if (!(cp->flags & CLAUSE_FLAG_DEAD)) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		vp->cdead++;
	    }
	    yp->degree--;
	    varp_free(&vp->xref_allocator, yptr);
	}
	else {
	    ASSERT(yptr == NULL);
	}
	yptr = yptr1;
    }
    
    // all the way and update xlast just in case
    while(*xpp != NULL) {
	xref_t* xptr = *xpp;	
	xpp = &(xptr->next);
    }
    // the new last x
    xp->xlast = xpp;
    
#if 0 
    while(*nxpp != NULL) {
	xref_t* nxptr = *nxpp;
	nxpp = &(nxptr->next);
    }
    nxp->xlast = nxpp;
#endif

#ifdef ASSERTIONS
    // enif_fprintf(stdout, "x-check: %s\r\n", format_literal(vp, xp));
    check_xref_consistence(xp);
    // enif_fprintf(stdout, "x-check: %s\r\n", format_literal(vp, nxp));    
    check_xref_consistence(nxp);
#endif
}

// substitue [X/Y] == [X/Y], [!X/!Y]

static void subst(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp  = l2ll(vp, yl);
    literal_t* xp  = l2ll(vp, xl);
    variable_t* y = yp->var;
    
    ASSERT(yp != xp);
    ASSERT(get_vv(vp, y) == I_UNDEF);

    log_permanent(vp, xp, yp, 0);

    subst_ll(vp, xl, yl);
    subst_ll(vp, neg_l(xl), neg_l(yl));

    if (vp->edge)
	subst_2_clause(vp, xl, yl);
    
    // mark Y as bound (to X)
    bnd_vv(vp, y);
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
    if (!vp->xref) // must enable cross reference!
	return enif_make_badarg(env);	

    y = get_l(vp, yp);
    if (IS_CONSTANT(y)) {
	return enif_make_badarg(env);
    }

    x = get_l(vp, xp);
    if (IS_CONSTANT(x)) {
	return enif_make_badarg(env);
    }

    xv = var_l(vp, xp);
    yv = var_l(vp, yp);

    vp->caller_env = env;
    if (xv != yv) subst(vp, xp, yp);
    vp->caller_env = NULL;    
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
    DBG("set_level: level=%d, t=%d, ix=%d, decision=%d\r\n",
	level, vp->undo[level].t, vp->undo[level].ix,
	vp->undo[level].decision); 
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
	vp->caller_env = env;
	move_level(vp, src, dst);
	vp->caller_env = NULL;	
    }
    return ATOM(ok);
}

// use 2-lower bits on 0 pointer to signal cases
#define ev_LITERAL  0
#define ev_NONE     1
#define ev_DEAD     2
#define ev_CONFLICT 3

#define EV_NONE     ((literal_t*) ev_NONE)
#define EV_DEAD     ((literal_t*) ev_DEAD)
#define EV_CONFLICT ((literal_t*) ev_CONFLICT)

// bcp clause
//  is called when at least one literal was set to FALSE!
// return (literal_t*) 3  conflict
// return (literal_t*) 1  non conclusive
// return (literal_t*) 2  dead
// return assigned literal otherwise
//
static inline literal_t* bcp_2_clause(varp_t* vp, clause_t* cp, wlink_t* wl1)
{
    ival_t lw;
    lit_t  l;
    literal_t* lp1;
    
    COUNT(vp, CLAUSE_2);

    ASSERT (!vp->edge);
    l = cp->lit[wl1->p];
    if ((lw = get_l(vp, l)) == I_TRUE) {
	COUNT(vp, CLAUSE_D);
	return EV_DEAD;
    }
    if (lw == I_FALSE)
	return EV_CONFLICT;
    DBG_BCP("    %s=1\r\n", format_lit(vp,l));
    lp1 = l2ll(vp,l);
    put_nq_ll(vp, lp1, I_TRUE, wl1->p, cp->cix, vp->level);
    return lp1;
}

// bcp_3_clause us this 3-(wp0+wp1) to find the new watch point
//  0    1     2    wp0+wp1
//  p    wp0   wp1  = 3-3 = 0
//  wp0  p     wp1  = 3-2 = 1
//  wp0  wp1   p    = 3-1 = 2

static inline literal_t* bcp_3_clause(varp_t* vp, clause_t* cp,
				      wlink_t* wl0, wlink_t* wl1,
				      wlink_t** wlp)
{
    ival_t lw;
    lit_t  l1, l;
    literal_t* lp1;
    pos_t  p;

    COUNT(vp, CLAUSE_3);

    l1 = cp->lit[wl1->p];
    if ((lw = get_l(vp, l1)) == I_TRUE) {
	COUNT(vp, CLAUSE_D);
	return EV_DEAD;
    }
    p = 3-(wl0->p + wl1->p); // !!
    l = cp->lit[p];
    switch(get_l(vp, l)) {
    case I_TRUE:
	return EV_DEAD;
    case I_FALSE:
	if (lw == I_FALSE)
	    return EV_CONFLICT;
	lp1 = l2ll(vp, l1);
	DBG_BCP("    %s=1\r\n", format_lit(vp, l1));
	put_nq_ll(vp, lp1, I_TRUE, wl1->p, cp->cix, vp->level);
	return lp1;
    case I_UNDEF:
    case I_BOUND:
    default:
	// convert 3-clause into 2-clause edge-list?
	// the 3-clause is then dead because it is evaluated by
	// edge lists
	if ((vp->edge) && (vp->level == 0)) {
	    // check watch?
	    cp->flags |= CLAUSE_FLAG_TWO;
	    vp->cdead++;
#ifdef DEBUG_EDGE
	    print_sym_clause(vp, "  SCHEDULE-UNWATCH/BCP3 ", cp);
#endif
	    schedule_unwatch_clause(vp, cp);
	    return EV_NONE;
	}
	break;
    }
    DBG_BCP("  wp: %s %d=>%ld\r\n", format_lit(vp, cp->lit[wl0->p]), wl0->p, p);
    *wlp = wl0->next;
    set_wlink(wl0, p, l2ll(vp,l));
    return EV_NONE;
}

//
// bcp 4-clause ?
//
//  0    1     2    3      3-(wp0+wp1)
//  -    wp0   wp1  -      3-(1+2) = 0
//  wp0  -     wp1  -      3-(2+0) = 1
//  wp0  wp1   -    -      3-(0+1) = 2
//                         (wp0+wp1)
//  wp0  -     -    wp1    3
//  -    wp0   -    wp1    4
//  -    -     wp0  wp1    5
//

#ifdef TWL_BACKWARD
#define WATCH_INIT(w)   ((w)-1)
#define WATCH_STEP(p)   ((p)-1)
#define WATCH_WRAP(p,n) (((p) < 0) ? ((n)-1) : (p))
#else
#define WATCH_INIT(w)   ((w)+1)
#define WATCH_STEP(p)   ((p)+1)
#define WATCH_WRAP(p,n) (((p) >= (n)) ? 0 : (p))
#endif

static inline literal_t* bcp_n_clause(varp_t* vp, clause_t* cp,
				      wlink_t* wl0, wlink_t* wl1,
				      wlink_t** wlp, int n)
{
    pos_t wp0, wp1;
    pos_t p;
    ival_t lw;
    lit_t l1;

    COUNT(vp, CLAUSE_N);
    
    wp1 = wl1->p;
    ASSERT(wp1 >= 0);

    l1 = cp->lit[wp1];
    if ((lw = get_l(vp, l1)) == I_TRUE) {
	COUNT(vp, CLAUSE_D);
	return EV_DEAD;
    }
    wp0 = wl0->p;
    ASSERT(wp0 >= 0);
    p = WATCH_INIT(wp0);
    p = WATCH_WRAP(p,n);
    // first step can NOT be wp0, so we can use a do loop
    do {
	if (p != wp1) {
	    switch(get_l(vp, cp->lit[p])) {
	    case I_FALSE:
		break;
	    case I_TRUE:
		return EV_DEAD;
	    case I_UNDEF: // found a wp
		DBG_BCP("  wp: %s %d=>%ld\r\n",
			format_lit(vp, cp->lit[wl0->p]), wl0->p, p);
		*wlp = wl0->next;
		set_wlink(wl0, p, l2ll(vp, cp->lit[p]));
		return EV_NONE;
	    case I_BOUND:
	    default:
		ASSERT(0);
	    }
	}
	p = WATCH_STEP(p);
	p = WATCH_WRAP(p,n);
    } while (p != wp0);

    if (lw == I_FALSE)
	return EV_CONFLICT;
    else {  // unit set other watchpoint
	literal_t* lp1 = l2ll(vp, l1);
	DBG_BCP("    %s\r\n", format_lit(vp, l1));	
	put_nq_ll(vp, lp1, I_TRUE, wp1, cp->cix, vp->level);
	return lp1;
    }
}

static int bcp1(varp_t* vp, literal_t* lp);

// bcp edge list lp=1 (implication chain) set all implicants to TRUE
static int bcp_edge_list(varp_t* vp, literal_t* lp)
{
    edge_t** epp = &lp->elist;
    edge_t* ep;

    while((ep = *epp) != NULL) {
	literal_t* lp1;
	int cont = 0;

	COUNT(vp, EDGE_2);
	
	DBG_BCP("bcp_edge: %s -> %s\r\n",
		 format_literal(vp, lp), format_lit(vp, ep->l));
	switch(get_l(vp, ep->l)) {
	case I_TRUE:
	    COUNT(vp, EDGE_D);
	    break; // noop
	case I_FALSE:
	    if (vp->max_conflicting == 1) {
		vp->conflicting_clauses[vp->num_conflicting++] = ep->cix;
		goto conflict;
	    }
	    else if (vp->num_conflicting < vp->max_conflicting) {
		vp->conflicting_clauses[vp->num_conflicting++] = ep->cix;
	    }
	    else
		goto conflict;
	    break;
	case I_UNDEF:
	    lp1 = l2ll(vp, ep->l);
	    DBG_BCP("    %s\r\n", format_lit(vp, ep->l));
	    put_nq_ll(vp, lp1, I_TRUE, 1, ep->cix, vp->level);
	    if (vp->level == 0) {
		// unlink dead edge!
		*epp = ep->next;
		varp_free(&vp->edge_allocator, ep);
		vp->edead++;
		cont = 1;
	    }
	    if (vp->qtype == recursive) {
		if (bcp1(vp, neg_ll(lp1)) < 0)
		    goto conflict;
	    }
	    else {
		lqueue_put_ll(vp, neg_ll(lp1));
	    }
	    if (cont)
		continue;
	    break;
	case I_BOUND:
	default:
	    ASSERT(0);
	    break;
	}
	epp = &(ep->next);
    }
    return 0;
conflict:
    return -1;
}

// bcp literal chain lp
static int bcp_clauses(varp_t* vp, literal_t* lp)
{
    wlink_t** wlp = &lp->wlist;
    wlink_t*  wl;

    DBG_BCP("bcp_clauses: %s\r\n", format_literal(vp, neg_ll(lp)));
    
    while((wl = *wlp) != NULL) {
	clause_t* cp = clause_pointer(wl);
#if defined(DEBUG_BCP)
	print_sym_clause(vp, "  bcp: ", cp);
#endif
	if (!(cp->flags & (CLAUSE_FLAG_CONFLICT|CLAUSE_FLAG_DEAD))) {
	    int i = wlink_index(wl);
	    wlink_t* wl0 = &cp->wl[i];
	    wlink_t* wl1 = &cp->wl[1-i];
	    switch(cp->select) {
	    case 0:
		lp = bcp_2_clause(vp, cp, wl1);
		break;
	    case 1:
		lp = bcp_3_clause(vp, cp, wl0, wl1, wlp);
		break;
	    case 2:
		lp = bcp_n_clause(vp, cp, wl0, wl1, wlp, cp->size);
		break;
	    default:
		ASSERT(0);
	    }
	    switch((intptr_t)lp) {
	    case ev_CONFLICT:
		if (vp->max_conflicting == 1) {
		    vp->conflicting_clauses[vp->num_conflicting++] = cp->cix;
		    return -1;
		}
		else if (vp->num_conflicting < vp->max_conflicting) {
		    vp->conflicting_clauses[vp->num_conflicting++] = cp->cix;
		    cp->flags |= CLAUSE_FLAG_CONFLICT;
		}
		else
		    return -1;
		break;
	    case ev_DEAD:
		if (vp->level == 0) {
		    vp->cdead++;
		    cp->flags |= CLAUSE_FLAG_DEAD;
#ifdef DEBUG_EDGE
		    print_sym_clause(vp, "  SCHEDULE-UNWATCH/DEAD", cp);
#endif
		    schedule_unwatch_clause(vp, cp);
		}
		break;
	    case ev_NONE:
		break;
	    default:
		if (vp->level == 0) {
		    vp->cdead++;
		    cp->flags |= CLAUSE_FLAG_DEAD;
#ifdef DEBUG_EDGE
		    print_sym_clause(vp, "  SCHEDULE-UNWATCH/SET", cp);
#endif
		    schedule_unwatch_clause(vp, cp);
		}
		if (vp->qtype == recursive) {
		    if (bcp1(vp, neg_ll(lp)) < 0)
			return -1;
		}
		else {
		    lqueue_put_ll(vp, neg_ll(lp));
		}
		break;
	    }
	}
	if (*wlp == wl)
	    wlp = &wl->next;
    }
    return 0;
}

// bcp1, bcp literal lp=0 
static int bcp1(varp_t* vp, literal_t* lp)
{
    int r = 0;

    DBG_BCP("bcp1: %s\r\n", format_literal(vp, neg_ll(lp)));

    if ((r >= 0))
	r = bcp_clauses(vp, lp);

    // keep bcp_edge_list after bcp_clauses since some clauses may
    // be converted to edge lists by bcp_clauses
    
    if ((r >= 0) && vp->edge)
	r = bcp_edge_list(vp, neg_ll(lp));

    if ((vp->level == 0) && vp->xref)
	kill_clauses(vp, neg_ll(lp));
    return r;
}

static int bcp(varp_t* vp)
{
    literal_t* lp;

    DBG_BCP("bcp\r\n");

    while((lp = lqueue_get(vp)) != NULL) {
	if (bcp1(vp, lp) < 0)
	    break;
    }
    return 0;
}

// run unwatch, remove clauses that are dead (level=0) and convert
// marked 3-clauses into 2-clauses (or edges)
static void bcp_unwatch(varp_t* vp)
{
    clause_t* cp = vp->unwatch;
    
    while(cp != NULL) {
	if (cp->flags & CLAUSE_FLAG_DEAD)
	    ;
	else if (vp->edge && (cp->flags&CLAUSE_FLAG_TWO)) { // 3 -> 2 clause
	    int w0, w1;
	    if (((w0=cp->wl[0].p) >= 0) && ((w1=cp->wl[1].p) >= 0)) {
		lit_t a = cp->lit[w0];
		lit_t b = cp->lit[w1];
		int w2 = 3-(w0+w1);
		lit_t c = cp->lit[w2];

		if ((get_l(vp,a) == I_TRUE) ||
		    (get_l(vp,b) == I_TRUE) ||
		    (get_l(vp,c) == I_TRUE)) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		}
		else {
		    DBG("%d: add edge lists w0=%d, w1=%d, w2=%d\r\n", cp->cix,
			w0, w1);
#ifdef DEBUG_EDGE
		    print_sym_clause(vp, "EDGE-INSERT", cp);
		    enif_fprintf(stdout, "a:%s=%s ",
				 format_lit(vp, a),
				 format_ival(get_l(vp,a)));
		    enif_fprintf(stdout, "b:%s=%s ",
				 format_lit(vp, b),
				 format_ival(get_l(vp,b)));
		    enif_fprintf(stdout, "c:%s=%s\r\n",
				 format_lit(vp, c),
				 format_ival(get_l(vp,c)));
#endif
		    // either a or b are FALSE so the edge is
		    // ~b -> (a or c),  ~a -> (b or c)
		    if (get_l(vp, b) == I_FALSE) {
			edge_insert(vp, neg_l(a), c, cp->cix);
			edge_insert(vp, neg_l(c), a, cp->cix);
		    }
		    else {
			edge_insert(vp, neg_l(b), c, cp->cix);
			edge_insert(vp, neg_l(c), b, cp->cix);
		    }
		}
	    }
	}
	unwatch_clause(vp, cp);
	cp->flags &= ~CLAUSE_FLAG_UNWATCH;
	cp = cp->uwatch;
    }
    vp->unwatch = NULL;    
}


// bcp:
//  return false  when conflict is found
//         true   when no conflict is found
//
static ERL_NIF_TERM varp_bcp(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    
    vp->bcp_counter++;
    vp->num_conflicting = 0;

    vp->caller_env = env;
    bcp(vp);
    vp->caller_env = NULL;

    if (vp->unwatch)
	bcp_unwatch(vp);

    if (vp->level > vp->max_level)     vp->max_level = vp->level;
    if (vp->num_bound > vp->max_bound) vp->max_bound = vp->num_bound;
    
    if (vp->num_conflicting) {
	int i;
	vp->conflict_counter++;
	lqueue_clear(&vp->q);
	DBG("num conflicts = %d\r\n", vp->num_conflicting);
	activate_levels(vp, 1.0);
	for (i = 0; i < vp->num_conflicting; i++) {
	    cix_t cix = vp->conflicting_clauses[i];
	    clause_t* cp = get_clause(vp, cix);
	    if (cp != NULL)
		cp->flags &= ~CLAUSE_FLAG_CONFLICT;
	}
	return ATOM(false);
    }
    return ATOM(true);
}

// undo effects of nbcp 

static ERL_NIF_TERM varp_undo(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    while((level = vp->level) > 0) {
	unbind_level(vp, level);
	if (vp->undo[level].t == 1) {  // SET+EVAL
	    vp->undo[level].decision = neg_l(vp->undo[level].decision);
	    vp->undo[level].t = 2;     // UNDO+NEG
	    return ATOM(true);
	}
	else if (vp->undo[level].t == 3) {  // NEG+EVAL
	    init_level(vp, level);
	}
	vp->level--;
    }
    return ATOM(false);
}

// nbcp:
//  return false  when conflict is found
//         true   when model is found
//
static ERL_NIF_TERM varp_nbcp(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i, ix;
    int level;
    lit_t xp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    
    level = vp->level;
    DBG("nbcp: level=%d, t=%d, ix=%d, decision=%d\r\n",
	level, vp->undo[level].t, vp->undo[level].ix,
	vp->undo[level].decision);
    
    if (vp->undo[level].t == 2) { // UNDO+NEG
	put_l(vp, vp->undo[level].decision, I_TRUE, -1, -1, level);
	vp->undo[level].t = 3;    // NEG+EVAL
	vp->caller_env = env;
	vp->num_conflicting = 0;
	ix = vp->undo[level].ix;
	goto bcp;
    }
    else if (vp->undo[level].t == 1) { // continue SET+EVAL
	vp->caller_env = env;
	vp->num_conflicting = 0;
	ix = vp->undo[level].ix;
	goto bcp;
    }
    
    if (vp->undo[level].t == 0)  // UNDEF - clear decision
	vp->undo[level].decision = L_FALSE(vp);
    if ((ix = order_next(vp, 1, 0)) == 0)
	return ATOM(true);  // model
    vp->caller_env = env;
    vp->num_conflicting = 0;
    if (level == 0)
	goto bcp;
next:
    xp = vindex_l(vp, vp->order_map[ix]);
    vp->undo[level].decision = xp;
    vp->undo[level].t = 1;    // SET+EVAL
    vp->undo[level].ix = ix;
    put_l(vp, xp, I_TRUE, -1, -1, level);
bcp:
    vp->bcp_counter++;
    DBG("BCP %ld, level=%d\r\n", vp->bcp_counter, vp->level);
    bcp(vp);
    if (vp->unwatch) bcp_unwatch(vp);
    if (vp->level > vp->max_level) vp->max_level = vp->level;
    if (vp->num_bound > vp->max_bound) vp->max_bound = vp->num_bound;    
    
    if (vp->num_conflicting == 0) {
	if ((ix = order_next(vp, ix+1, 0)) == 0) {
	    vp->caller_env = NULL;
	    return ATOM(true);  // model 
	}
	set_level(vp, level+1);
	level = vp->level;
	goto next;
    }

    // conflict found
    vp->caller_env = NULL;
    vp->conflict_counter++;    

    lqueue_clear(&vp->q);
    DBG("num conflicts = %d\n", vp->num_conflicting);
    if (vp->atype == mvsids)
	activate_levels(vp, 1.0);
    for (i = 0; i < vp->num_conflicting; i++) {
	cix_t cix = vp->conflicting_clauses[i];
	clause_t* cp = get_clause(vp, cix);
	if (cp != NULL)
	    cp->flags &= ~CLAUSE_FLAG_CONFLICT;
    }
    return ATOM(false);
}

// get information
static ERL_NIF_TERM varp_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (argv[1] == ATOM(bcp_counter)) {
	return enif_make_uint64(env, vp->bcp_counter);
    }
    if (argv[1] == ATOM(level)) {
	return enif_make_uint(env, vp->level);
    }
    if (argv[1] == ATOM(conflict_counter)) {
	return enif_make_uint64(env, vp->conflict_counter);
    }    
    if (argv[1] == ATOM(max_clause_length)) {
	return enif_make_int(env, MAX_CLAUSE_LENGTH);
    }
    if (argv[1] == ATOM(max_conflicting)) {
	return enif_make_int(env, vp->max_conflicting);
    }
    if (argv[1] == ATOM(number_of_conflicting_clauses)) {
	return enif_make_int(env, vp->num_conflicting);
    } 
    if (argv[1] == ATOM(number_of_variables)) {
	return enif_make_int(env, vp->vnum);
    }
    if (argv[1] == ATOM(number_of_clauses)) {
	return enif_make_int(env, get_number_of_clauses(vp));
    }
    if (argv[1] == ATOM(number_of_edges)) {
	return enif_make_int(env, vp->nedge);
    }
    if (argv[1] == ATOM(number_of_dead_clauses)) {
	return enif_make_int(env, vp->cdead);
    }
    if (argv[1] == ATOM(number_of_dead_edges)) {
	return enif_make_int(env, vp->edead);
    }    
    if (argv[1] == ATOM(number_of_learned_clauses)) {
	return enif_make_int(env, vp->cnum[1]);
    }    
    if (argv[1] == ATOM(number_of_bound_variables)) {
	return enif_make_int(env, vp->num_bound);
    }
    if (argv[1] == ATOM(number_of_unbound_variables)) {
	return enif_make_int(env, vp->vnum - vp->num_bound);
    }
    if (argv[1] == ATOM(clause_n_counter)) {
	return enif_make_uint64(env, vp->counter[CLAUSE_N]);
    }
    if (argv[1] == ATOM(clause_2_counter)) {
	return enif_make_uint64(env, vp->counter[CLAUSE_2]);
    }
    if (argv[1] == ATOM(clause_3_counter)) {
	return enif_make_uint64(env, vp->counter[CLAUSE_3]);
    }
    if (argv[1] == ATOM(clause_d_counter)) {
	return enif_make_uint64(env, vp->counter[CLAUSE_D]);
    }
    if (argv[1] == ATOM(edge_2_counter)) {
	return enif_make_uint64(env, vp->counter[EDGE_2]);
    }
    if (argv[1] == ATOM(edge_d_counter)) {
	return enif_make_uint64(env, vp->counter[EDGE_D]);
    }
    if (argv[1] == ATOM(grow)) {
	return enif_make_uint(env, vp->grow);
    }
    if (argv[1] == ATOM(size)) {
	return enif_make_uint(env, vp->vsize);
    }
    if (argv[1] == ATOM(qtype)) {
	switch(vp->qtype) {
	case lifo: return ATOM(lifo);
	case fifo: return ATOM(fifo);
	case recursive: return ATOM(recursive);
	default: return ATOM(undefined);
	}
    }
    if (argv[1] == ATOM(max_level)) {
	return enif_make_int(env, vp->max_level);
	vp->max_level = 0;
    }
    if (argv[1] == ATOM(max_bound)) {
	return enif_make_int(env, vp->max_bound);
	vp->max_bound = 0;
    }    
    if (argv[1] == ATOM(literal_size)) {
	return enif_make_uint(env, 8*sizeof(lit_t));
    }
    if (argv[1] == ATOM(literal_integer)) {
#ifdef LIT_INTEGER
	return ATOM(true);
#else
	return ATOM(false);
#endif
    }
    if (argv[1] == ATOM(value_packing)) {
#ifdef PACKED_VALUE
	return enif_make_uint(env, PACKED_VALUE);
#else
	return ATOM(undefined);
#endif
    }
    if (argv[1] == ATOM(edge)) {
	return make_boolean(env, vp->edge);
    }
    if (argv[1] == ATOM(xref)) {
	return make_boolean(env, vp->xref);
    }
    if (argv[1] == ATOM(activity)) {
	switch(vp->atype) {
	case mvsids: return ATOM(mvsids);
	case cvsids: return ATOM(cvsids);
	case off:	    
	default:
	     return ATOM(off);
	}
    }
    return enif_make_badarg(env);
}


// set config
static ERL_NIF_TERM varp_config(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

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
static int cmp_abs_lit QSORT_ARGS(const void* ap,const void* bp,void* arg)
{
    (void) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);

    if (a == b) return 0;
#ifdef LIT_INTEGER
    if (INDEX(a) == INDEX(b)) {
	if (SIGN(a)) return -1;
	return 1;
    }
    else if (INDEX(a) == 0)  // TRUE > *
	return 1;
    else if (INDEX(b) == 0)
	return -1;
    else
	return INDEX(a) - INDEX(b);
#else
    if (a->var == b->var) {
	if (a->sign) return -1;
	else return 1;
    }
    if (a->var->vix == 0)
	return 1;
    else if (b->var->vix == 0)
	return -1;
    else
	return a->var->vix - b->var->vix;
#endif
}

#ifdef USE_CLAUSE_SHUFFLE

typedef struct
{
    lit_t lit;
    int32_t key;
} shuffle_key_t;

static int cmp_shuffle QSORT_ARGS(const void* a, const void* b,void* arg)
{
    UNUSED(arg);
    return ((shuffle_key_t*)a)->key - ((shuffle_key_t*)b)->key;
}

#endif


// sort literal, remove duplicates trim and return new size
static size_t sort_clause_array(varp_t* vp, lit_t* lit, size_t size, bool_t raw)
{
    int i;
    unsigned Tc=0, Fc=0;

    // PRINT_LIT_ARRAY("   src", lit, size);

    // replace level 0 variables with constants
    if (!raw) {
	for (i = 0; i < (int)size; i++) {
	    if ((lit[i] == L_TRUE(vp)) || (lit[i] == L_FALSE(vp)))
		;
	    else {
		literal_t* lp = l2ll(vp, lit[i]);
		if (lp->var->level == 0) {  // since we never undo level 0
		    switch(get_ll(vp,lp)) {
		    case I_TRUE:  lit[i] = L_TRUE(vp); break;
		    case I_FALSE: lit[i] = L_FALSE(vp); break;
		    case I_BOUND:
		    case I_UNDEF:
		    default: break;
		    }
		}
	    }
	}
    }
    // PRINT_LIT_ARRAY("   filt0", lit, size);
    
    // sort all literals by absolute value
    QSORT(lit, size, sizeof(lit_t), cmp_abs_lit, vp);

    // PRINT_LIT_ARRAY(" sorted", lit, size);

    // remove TRUE literals
    i = size-1;
    while((i >= 0) && (lit[i] == L_TRUE(vp))) { i--; size--; Tc++; }
    // PRINT_LIT_ARRAY("  del-T", lit, size);

    // remove FALSE literals
    while((i >= 0) && (lit[i] == L_FALSE(vp))) { i--; size--; Fc++; }
    // PRINT_LIT_ARRAY("  del-F", lit, size);

    // remove duplicates
    {
	unsigned u=0,v=0,w=0;
	while(v < size) {
	    while((w < size) && (lit[v] == lit[w])) w++;
	    if ((u >= 1) && (lit[u-1] == neg_l(lit[v]))) {
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
    if (size == 0) {
	if ((Tc==0) && (Fc>0))
	    lit[size++] = L_FALSE(vp);
    }
    if (Tc>0) // add the T constant to the gate
	lit[size++] = L_TRUE(vp);

    // PRINT_LIT_ARRAY("   dest", lit, size);
    return size;
}


static ERL_NIF_TERM add_clause_array(ErlNifEnv* env, varp_t* vp,
				     int si, lit_t* lit, size_t size)
{
    clause_t* cp;
    cix_t cix;
    uint32_t hvalue;
    
    size = sort_clause_array(vp, lit, size, false);
    
    // set watch points
    if (lit[size-1] == L_TRUE(vp))
	return ATOM(true);

    if (size == 1) {  // unit
	if (lit[0] == L_FALSE(vp))
	    return ATOM(false);
	put_l(vp, lit[0], I_TRUE, -1, -1, 0);
	return ATOM(true);
    }

#ifdef USE_CLAUSE_FIND
    // check if clause is already installed!!!
    // FIXME: allow only if clause_hash is set?
    if ((cix = clause_find(vp, lit, size)) >= 0) {
	enif_fprintf(stdout, "Found clause %d size=%ld\r\n", cix, size);
	return enif_make_tuple2(env, ATOM(true),
				enif_make_int(env, cix));
    }
#endif

    // shuffle literals - possibly make watch literal chains shorter?
#ifdef USE_CLAUSE_SHUFFLE
    {
	int i;
	shuffle_key_t skey[size];
	for (i = 0; i < (int)size; i++) {
	    skey[i].lit = lit[i];
	    skey[i].key = arc4_random(&vp->as);
	}
	QSORT(skey, size, sizeof(shuffle_key_t), cmp_shuffle, 0);
	for (i = 0; i < (int)size; i++)
	    lit[i] = skey[i].lit;
    }
    PRINT_LIT_ARRAY("shuffle", lit, size);
#endif
    if ((cp = clause_alloc(vp, size)) == NULL)
	goto error;
    hvalue = (uint32_t) literal_array_hash(vp, lit, size);
    if ((cix = clause_insert(vp, si, cp, hvalue)) == CLAUSE_NONE)
	goto error;
    memcpy(cp->lit, lit, sizeof(lit_t)*size);
    
    switch(size) {
    case 2: cp->select = 0; break; // 0 = 2 clause
    case 3: cp->select = 1; break; // 1 = 3 clause
    default: cp->select = 2; break; // 2 = n clause
    }
	
    switch (link_clause(vp, cp)) {
    case -1:
	goto error;
    case 0:
	update_clause_degree(vp, cp, 1);
	if ((vp->atype != off) && (si > 0))
	    update_clause_activity(vp, cp, 1.0f);
	return enif_make_tuple2(env, ATOM(false), make_cix(env, cix));
    case 1:
	update_clause_degree(vp, cp, 1);
	if ((vp->atype != off) && (si > 0))
	    update_clause_activity(vp, cp, 1.0f);
	return enif_make_tuple2(env, ATOM(true), make_cix(env, cix));
    default:
	goto error;
    }

error:
    if (cp != NULL) clause_free(vp, cp);
    return enif_make_badarg(env);
}

//
// add_clause(vp, [x1, ..., xn])
// add_clause(vp, [x1, ..., xn], si)
//
static ERL_NIF_TERM varp_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int size;
    unsigned int si = 0;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;    
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (argc == 3) {
	if (!enif_get_uint(env, argv[2], &si) || (si > NUM_CSET))
	    return enif_make_badarg(env);
    }

    list = argv[1];
    size = 0;
    while(enif_get_list_cell(env, list, &head, &tail)) {
	size++;
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);
    else {
	ERL_NIF_TERM ret;
	lit_t literals[size];
	lit_t* lpp = &literals[0];
	
	list = argv[1];
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    if (!vif_get_lit(env, vp, head, lpp))
		return enif_make_badarg(env);
	    lpp++;
	    list = tail;
	}
	vp->caller_env = env;
	ret = add_clause_array(env, vp, si, literals, size);
	vp->caller_env = NULL;
	return ret;
    }
}


// find_clause(vp, x1, ..., xn) -> index | false
// find_clause(vp, [x1, ..., xn]) -> index | false
//
static ERL_NIF_TERM varp_find_clause(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);    
    varp_t* vp;
    int size;
    cix_t cix;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    list = argv[1];
    size = 0;
    while(enif_get_list_cell(env, list, &head, &tail)) {
	size++;
	list = tail;
    }
    if (!enif_is_empty_list(env, list))
	return enif_make_badarg(env);
    else {
	lit_t literals[size];
	lit_t* lpp = &literals[0];
	
	list = argv[1];
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    if (!vif_get_lit(env, vp, head, lpp))
		return enif_make_badarg(env);
	    lpp++;
	    list = tail;
	}
	size = sort_clause_array(vp, literals, size, true);
	if ((cix=clause_find(vp, literals, size)) == CLAUSE_NONE)
	    return ATOM(false);
	return enif_make_int(env, (int)cix);
    }
}

//
// compress_clause(vp,ClauseIndex::integer()|[integer()]) ->
//  binary().
//
static ERL_NIF_TERM varp_compress_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t  cix;
    clause_t* cp;
    ERL_NIF_TERM bin;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix)) {
	ERL_NIF_TERM list;
	ERL_NIF_TERM head, tail;
	int csize = 0;
	int x;

	list = argv[1];
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    if (!enif_get_int(env, head, &x))
		return enif_make_badarg(env);
	    csize++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
	else {
	    uint8_t buffer[5*csize];
	    unsigned char* binptr;
	    int n = 0;

	    list = argv[1];
	    while(enif_get_list_cell(env, list, &head, &tail)) {
		enif_get_int(env, head, &x);
		n += compress_int(x, &buffer[n]);
		list = tail;
	    }
	    binptr = enif_make_new_binary(env, n, &bin);
	    memcpy(binptr, buffer, n);
	}
    }
    else {
	if ((cp = get_clause(vp, cix)) == NULL) {
	    enif_make_new_binary(env, 0, &bin);
	}
	else {
	    lit_t* lit = cp->lit;
	    size_t csize = cp->size;
	    uint8_t buffer[5*csize];
	    unsigned char* binptr;
	    int n = 0;
	    int i;
	    
	    for (i = 0; i < (int)csize; i++) {
		int x = export_l(lit[i]);
		n += compress_int(x, &buffer[n]);
	    }
	    buffer[n++] = 0;
	    binptr = enif_make_new_binary(env, n, &bin);
	    memcpy(binptr, buffer, n);
	}
    }
    return bin;
}

static void unlink_clause(varp_t* vp, clause_t* cp)
{
    if ((cp->size == 2) && vp->edge) {
	lit_t* lit  = cp->lit;
	edge_remove(vp, neg_l(lit[0]), lit[1], cp->cix);
	edge_remove(vp, neg_l(lit[1]), lit[0], cp->cix);
    }
    unwatch_clause(vp, cp);      // remove watched literals
    if (vp->xref)
	unxref_clause(vp, cp);
}

static void remove_clause(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	unlink_clause(vp, cp);
	update_clause_degree(vp, cp, -1);
	clause_free(vp, cp);
    }
}

// delete a clause by index or literal list
// may only delete clauses on level 0!
static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t cix;
    clause_t* cp;
    unsigned si;
    int ix;
    clause_t** cm;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix)) {
	int size;
	ERL_NIF_TERM list;
	ERL_NIF_TERM head, tail;

	list = argv[1];
	size = 0;
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    size++;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
	else {
	    lit_t literals[size];
	    lit_t* lpp = &literals[0];
	
	    list = argv[1];
	    while(enif_get_list_cell(env, list, &head, &tail)) {
		if (!vif_get_lit(env, vp, head, lpp))
		    return enif_make_badarg(env);
		lpp++;
		list = tail;
	    }
	    size = sort_clause_array(vp, literals, size, true);
	    if ((cix=clause_find(vp, literals, size)) == CLAUSE_NONE)
		return enif_make_badarg(env);
	}
    }

    if (vp->level != 0)
	return enif_make_badarg(env);

    si = GET_SI(cix);
    ix = GET_IX(cix);

    if ((cp = get_clause(vp,cix)) == NULL)
	return enif_make_badarg(env);

    remove_clause(vp, cp);

    ASSERT(get_clause(vp, cix) == NULL);

    // check if we have a hole at the end, update cnext
    cm = vp->clause_map[si];
    if (ix+1 == (int)vp->cnext[si]) {  // we remove the last clause
	while((ix>0) && (cm[ix-1] == NULL))
	    ix--;
	vp->cnext[si] = ix;
    }
    return ATOM(ok);
}

// may only clean clause on level 0!
static ERL_NIF_TERM varp_clean_clause(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t cix;
    clause_t* cp;
    lit_t* lit;
    size_t size;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_make_badarg(env);
    if ((cp = get_clause(vp,cix)) == NULL)
	return ATOM(ok);

    size = cp->size;
    lit  = cp->lit;

    DBG("cleanup: clause %u, size=%lu\r\n", cix, size);

    unlink_clause(vp, cp);
    if (cp->flags & CLAUSE_FLAG_DEAD) goto remove;
    size = sort_clause_array(vp, lit, size, false);
    if (lit[size-1] == L_TRUE(vp))
	goto remove;
    if ((size == 1) && (lit[0] == L_FALSE(vp)))
	goto error;
    cp->size = size;

    link_clause(vp, cp);
    return ATOM(ok);
    
remove:
    DBG("  %lu-removed\r\n", size);
    set_clause(vp, cix, NULL);
    clause_free(vp, cp);
    return ATOM(ok);

error:
    return enif_make_badarg(env);    
}



// may only clean literal on level 0!
static ERL_NIF_TERM varp_clean_edges(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;
    edge_t* ep;
    edge_t** epp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_ll(env, vp, argv[1], &lp))
	return enif_make_badarg(env);

    epp = &lp->elist;
    while((ep = *epp) != NULL) {
	if (get_l(vp, ep->l) != I_UNDEF) {
	    *epp = ep->next;
	    varp_free(&vp->edge_allocator, ep);
	}
	else
	    epp = &(ep->next);
    }
    return ATOM(ok);
}

// del unused clauses is used for garbage collection and may
// only be called during a restart. i.e no bindings may be present
// so level must be = 0
// cmp_use sort according to falling bcp_counter stamp
// so that the newest and recently used clauses are sorted
// first.
static int cmp_stamp QSORT_ARGS(const void* a, const void* b,void* arg)
{
    UNUSED(arg);
    clause_t* ca = *(clause_t**)a;
    clause_t* cb = *(clause_t**)b;

    if (ca == NULL) {
	if (cb == NULL) return 0;
	return 1;
    }
    else if (cb == NULL)
	return  -1;
    else  if (cb->stamp < ca->stamp) return -1;
    else if (cb->stamp > ca->stamp) return 1;
    return 0;
}

// use remap (reverse map) to update cix in cross reference after
// sorting clauses.
static void remap_xref(literal_t* lp, unsigned int si, int* remap, int n)
{
    UNUSED(n);
    xref_t* xp = lp->xfirst;

    while(xp != NULL) {
	if (GET_SI(xp->cix) == si) {
	    int ix = GET_IX(xp->cix);
	    xp->cix = MAKE_CIX(si, remap[ix]);
	}
	xp = xp->next;
    }
}

static void remap_edge(literal_t* lp, unsigned int si, int* remap, int n)
{
    UNUSED(n);    
    edge_t* ep = lp->elist;
    while(ep != NULL) {
	if (GET_SI(ep->cix) == si) {
	    int ix = GET_IX(ep->cix);
	    ep->cix = MAKE_CIX(si, remap[ix]);
	}
	ep = ep->next;
    }
}

//
// Sort and "compact" clause put all "holes" (NULL clauses)
// at the end and update cnext and cnum to match cleanup
//
static ERL_NIF_TERM varp_sort_clauses(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int si;
    int n;
    clause_t** cm;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &si) || (si >= NUM_CSET))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_make_badarg(env);
    if (vp->cnext[si] == 0)
	return ATOM(ok);

    n = (int)vp->cnext[si];
    cm = vp->clause_map[si];
    QSORT(cm, n, sizeof(clause_t*), cmp_stamp, vp);

    {
	int ix;
	int rmap[n];
	int h = 0;
	// cleanup the holes
	while(n && (vp->clause_map[si][n-1] == NULL)) {
	    h++;
	    n--;
	}
	if (h > 0) {
	    enif_fprintf(stdout, "%d HOLES removed\r\n", h);
	}
	vp->cnext[si] = n;

	for (ix = 0; ix < n; ix++) {
	    int jx = GET_IX(cm[ix]->cix);
	    rmap[jx] = ix;  // build reverse map
	    cm[ix]->cix = MAKE_CIX(si,ix);
	}

	// now map all xrefs and edges
	if (vp->xref) {
	    int i;
	    for (i = 1; i < (int)vp->vnext; i++) {
		remap_xref(&vp->var_map[i]->lit[0], si, rmap, n);
		remap_xref(&vp->var_map[i]->lit[1], si, rmap, n);
	    }
	}
	if (vp->edge) {
	    int i;
	    for (i = 1; i < (int)vp->vnext; i++) {
		remap_edge(&vp->var_map[i]->lit[0], si, rmap, n);	    
		remap_edge(&vp->var_map[i]->lit[1], si, rmap, n);
	    }
	}	
    }
    return ATOM(ok);
}

static ERL_NIF_TERM varp_clauseset_size(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int si;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &si) || (si > NUM_CSET))
	return enif_make_badarg(env);    
    return enif_make_uint(env, vp->cnext[si]);
}

static ERL_NIF_TERM varp_clauseset_offset(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    varp_t* vp;
    unsigned si;
    unsigned offs;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &si) || (si >= NUM_CSET))
	return enif_make_badarg(env);
    if (argc == 3) {
	if (!enif_get_uint(env, argv[2], &offs))
	    return enif_make_badarg(env);
	vp->coffs[si] = offs;
	return ATOM(ok);
    }
    return enif_make_uint(env, vp->coffs[si]);
}
  
static ERL_NIF_TERM varp_clause_first(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    unsigned si;
    clause_t** cm;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &si) || (si >= NUM_CSET))
	return enif_make_badarg(env);
    i = vp->coffs[si];
    cm = vp->clause_map[si];
    while(i < (int)vp->cnext[si]) {
	if (cm[i] != NULL) {
	    return make_cix(env, MAKE_CIX(si,i));
	}
	i++;
    }
    return ATOM(false);
}

static ERL_NIF_TERM varp_clause_next(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int cix;
    int ix, si, n;
    clause_t** cm;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    if ((si = GET_SI(cix)) >= NUM_CSET)
	return enif_make_badarg(env);
    ix = GET_IX(cix)+1;
    n  = (int)vp->cnext[si];
    cm = vp->clause_map[si];
    while(ix < n) {
	if (cm[ix] != NULL) {
	    return make_cix(env, MAKE_CIX(si,ix));
	}
	ix++;
    }
    return ATOM(false);
}

//
// get_clause(vp,ClauseIndex::integer(),SkipLiteral::literl(),Raw::boolean())->
//  [literal()] | true | false.
//
// returns
//     false      clause does not exist
//     true       when clause is dead (contains true)
//     []         when contradictory (or L/t if Skip=L and clause = [L])
//     [L1...Ln]  a clause, without the Skip literal, if set.
//
static ERL_NIF_TERM varp_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM list;
    int i;
    bool_t raw;
    literal_t* lp;
    ERL_NIF_TERM skip;
    cix_t  cix;
    lit_t* lit;
    size_t csize;
    clause_t* cp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);
    
    if (argv[2] == ATOM(undefined))
	skip = ATOM(undefined);
    else if (!vif_get_literal(env, vp, argv[2], &lp))
	return enif_make_badarg(env);
    else
	skip = external_ll(env,lp);
    if (!vif_get_boolean(env, argv[3], &raw))
	return enif_make_badarg(env);

    if ((cp = get_clause(vp, cix)) == NULL)
	return ATOM(false);
    
    lit = cp->lit;
    csize = cp->size;
    list = enif_make_list(env, 0);

    for (i = csize-1; i >= 0; i--) {
	ERL_NIF_TERM elem = external_l(env, lit[i]);
	if (elem != skip) {
	    if (raw) {  // debug
		list = enif_make_list_cell(env, elem, list);	    
	    }
	    else {
		literal_t* lp = l2ll(vp, lit[i]);
		if (lp->var->level <= 0) {  // constant level
		    switch(get_ll(vp,lp)) {
		    case I_TRUE: // FIXME: should not be empty list!!!
			return enif_make_list(env, 0);
		    case I_FALSE:  // skip FALSE constants
			break;
		    case I_UNDEF:
		    case I_BOUND:
		    default:
			list = enif_make_list_cell(env, elem, list);
			break;
		    }
		}
		else {
		    list = enif_make_list_cell(env, elem, list);		
		}
	    }
	}
    }
    return list;
}

// get status/watch0/watch1/watch
static ERL_NIF_TERM varp_clause_info(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varp_t* vp;
    cix_t cix;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);
    if ((cp = get_clause(vp, cix)) == NULL)
	return enif_make_badarg(env);	

    if (argv[2] == ATOM(status)) {
	if (cp->flags & CLAUSE_FLAG_DEAD)
	    return ATOM(dead);
	else if (cp->flags & CLAUSE_FLAG_CONFLICT)
	    return ATOM(conflict);
	else if (cp->flags & CLAUSE_FLAG_INQUEUE)
	    return ATOM(inqueue);
	else
	    return ATOM(ok);
    }
    if (argv[2] == ATOM(watch0))
	return enif_make_long(env,cp->wl[0].p);
    if (argv[2] == ATOM(watch1)) 
	return enif_make_long(env,cp->wl[1].p);
    if (argv[2] == ATOM(watch))
	return enif_make_tuple2(env,
				enif_make_long(env,cp->wl[0].p),
				enif_make_long(env,cp->wl[1].p));
    return enif_make_badarg(env);
}

static ERL_NIF_TERM varp_use_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    clause_t* cp;
    varp_t* vp;
    cix_t cix;   
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);
    if ((cp = get_clause(vp, cix)) == NULL)
	return enif_make_badarg(env);
    cp->stamp = vp->bcp_counter;
    return ATOM(ok);
}

static ERL_NIF_TERM varp_clauseset_xref(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);    
    varp_t* vp;
    bool_t enable;
    bool_t was_enabled;
    unsigned int si;
    int i;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &si) || (si >= NUM_CSET))
	return enif_make_badarg(env);
    if (!vif_get_boolean(env, argv[2], &enable))
	return enif_make_badarg(env);

    was_enabled = vp->xref;
    
    if (enable && !vp->xref) {
	// xref all clauses
	vp->xref = true;
	for (i = 0; i < (int)vp->cnext[si]; i++)
	    xref_clause(vp, vp->clause_map[si][i]);
    }
    else if (!enable && vp->xref) {
	// tear down xref
	for (i = 0; i < (int)vp->cnext[si]; i++)
	    unxref_clause(vp, vp->clause_map[si][i]);	
	vp->xref = false;
    }
    return make_boolean(env, was_enabled);
}

static ERL_NIF_TERM varp_decay(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    double decay;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    
    if (!vif_get_number(env, argv[1], &decay))
	return enif_make_badarg(env);
    activity_decay(vp, decay);
    return ATOM(ok);
}

static int vif_get_sub_flag(ErlNifEnv* env, ERL_NIF_TERM term, uint32_t* flag)
{
    UNUSED(env);
    if (term == ATOM(variable))
	*flag = SUB_FLAG_VAR;    
    else if (term == ATOM(atom))
	*flag = SUB_FLAG_ATOM;
    else if (term == ATOM(number_of_variables))
	*flag = SUB_FLAG_NUM_VARS;
    else if (term == ATOM(number_of_bound_variables))
	*flag = SUB_FLAG_NUM_BOUND;
    else if (term == ATOM(number_of_clauses))
	*flag = SUB_FLAG_NUM_CLAUSES;
    else if (term == ATOM(number_of_dead_clauses))
	*flag = SUB_FLAG_NUM_DEAD;
    else if (term == ATOM(max_level))
	*flag = SUB_FLAG_MAX_LEVEL;
    else if (term == ATOM(max_bound))
	*flag = SUB_FLAG_MAX_BOUND;    
    else
	return 0;
    return 1;
}

static int vif_get_sub_flags(ErlNifEnv* env, ERL_NIF_TERM term, uint32_t* flags)
{
    ERL_NIF_TERM list = term;    
    uint32_t fs = 0;

    if (enif_is_atom(env, term)) {
	if (!vif_get_sub_flag(env, term, &fs))
	    return 0;
    }
    else {
	ERL_NIF_TERM head, tail;

	while(enif_get_list_cell(env, list, &head, &tail)) {
	    uint32_t f;	
	    if (!vif_get_sub_flag(env, head, &f))
		return 0;
	    fs |= f;
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return 0;	
    }
    *flags = fs;
    return 1;
}

//
// FIXME: set flag(s) that indicate what kind of messages
// that are of interest.
//    assignment
//    substitution
//    statistics
//
static ERL_NIF_TERM varp_subscribe(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    uint32_t flags;
    subscription_t* sp;
    int r;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (!vif_get_sub_flags(env, argv[1], &flags))
	return enif_make_badarg(env);	

    if ((sp = varp_alloc(&vp->sub_allocator)) == NULL)
	return enif_make_badarg(env);
    r = enif_monitor_process(env, vp, enif_self(env,&sp->pid), &sp->mon);
    if (r != 0) {
	// r < 0 no down callback, r > 0 process not alive
	varp_free(&vp->sub_allocator, sp);
	return enif_make_badarg(env);
    }
    sp->flags = flags;
    // link in first
    sp->next = vp->subs;
    vp->subs = sp;
	
    return ATOM(ok);	
}

static ERL_NIF_TERM make_edge_list(ErlNifEnv* env, varp_t* vp,
				  literal_t* lp, ERL_NIF_TERM list)
{
    UNUSED(vp);
    edge_t* pl = lp->elist;
    while(pl) {
	ERL_NIF_TERM elem = make_cix(env, pl->cix);
	list = enif_make_list_cell(env, elem, list);
	pl = pl->next;
    }
    return list;
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
	    ERL_NIF_TERM elem = make_cix(env, cp->cix);
	    list = enif_make_list_cell(env, elem, list);
	    wl = wl->next;
	}
	if (vp->edge) {
	    list = make_edge_list(env, vp, neg_ll(lp), list);
	    list = make_edge_list(env, vp, lp, list);
	}
    }
    else if (argv[2] == ATOM(literal)) {
	xref_t* xp = lp->xfirst;
	while(xp) {
	    if (get_clause(vp, xp->cix) != NULL) {
		ERL_NIF_TERM elem = make_cix(env, xp->cix);
		list = enif_make_list_cell(env, elem, list);
	    }
	    xp = xp->next;
	}
    }
    else if (argv[2] == ATOM(variable)) {
	variable_t* var = lp->var;
	int i;

	for (i = 0; i < 2; i++) {
	    xref_t* xp = var->lit[i].xfirst;
	    while(xp) {
		if (get_clause(vp, xp->cix) != NULL) {
		    ERL_NIF_TERM elem = make_cix(env, xp->cix);
		    list = enif_make_list_cell(env, elem, list);
		}
		xp = xp->next;
	    }
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


// get_descision(Vp, Level [,ToggleValue])
// return decision "literal" on Level

static ERL_NIF_TERM varp_get_decision(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    int toggle = 3;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0) || (level > vp->level))
	return enif_make_badarg(env);
    if (argc >= 3) {
	if (!enif_get_int(env, argv[2], &toggle) || (toggle<0))
	    return enif_make_badarg(env);
    }
    if ((vp->undo[level].t >= toggle) ||
	(vp->undo[level].decision == L_FALSE(vp)))
	return ATOM(f);
    else
	return enif_make_int(env, export_l(vp->undo[level].decision));
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
    bool_t clause_info = false;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0))
	return enif_make_badarg(env);
    if (!vif_get_boolean(env, argv[2], &clause_info))
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
    bool_t clause_info = false;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &count) || (count < 0))
	return enif_make_badarg(env);
    if (!vif_get_boolean(env, argv[2], &clause_info))
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

// get_number_of_bindings(Vp, Level) -> unsigned()
// return number of bindings on Level

static ERL_NIF_TERM varp_get_number_of_bindings(ErlNifEnv* env, int argc,
						const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    variable_t* bp;    
    int nbound = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level < 0) ||
	(level >= (int)vp->unum))
	return enif_make_badarg(env);
    bp = vp->undo[level].bs;
    while(bp != NULL) {
	nbound++;
	bp = bp->next;
    }
    return enif_make_uint(env, nbound);
}

// create all tracing NIFs
#ifdef NIF_TRACE

#define NIF(name, arity, func) \
static ERL_NIF_TERM trace##_##func##_##arity(ErlNifEnv* env, int argc,const ERL_NIF_TERM argv[]) \
{ \
    ERL_NIF_TERM result;					\
    enif_fprintf(stdout, "ENTER %s/%d\r\n", (name),(arity));	\
    result = func(env, argc, argv);				\
    enif_fprintf(stdout, "LEAVE %s/%d\r\n", (name),(arity));	\
    return result;						\
}

NIF_LIST
#undef NIF

#endif


static void load_atoms(ErlNifEnv* env)
{
    // Load atoms
    LOAD_ATOM(t);
    LOAD_ATOM(f);    
    LOAD_ATOM(ok);
    LOAD_ATOM(true);
    LOAD_ATOM(false);
    LOAD_ATOM(undefined);
    LOAD_ATOM(default);
    LOAD_ATOM(grow);
    LOAD_ATOM(size);
    LOAD_ATOM(error);
    LOAD_ATOM(inqueue);
    LOAD_ATOM(dead);
    LOAD_ATOM(status);
    LOAD_ATOM(watch);
    LOAD_ATOM(watch0);
    LOAD_ATOM(watch1);
    LOAD_ATOM(literal);
    LOAD_ATOM(variable);
    LOAD_ATOM(atom);
    LOAD_ATOM(flags);
    LOAD_ATOM(activity);
    LOAD_ATOM(degree);
    LOAD_ATOM(user);
    LOAD_ATOM(mvsids);
    LOAD_ATOM(cvsids);
    LOAD_ATOM(off);
    
    // info
    LOAD_ATOM(max_clause_length);
    LOAD_ATOM(max_conflicting);
    LOAD_ATOM(number_of_conflicting_clauses);
    LOAD_ATOM(number_of_clauses);
    LOAD_ATOM(number_of_dead_clauses);
    LOAD_ATOM(number_of_edges);
    LOAD_ATOM(number_of_dead_edges);    
    LOAD_ATOM(number_of_learned_clauses);    
    LOAD_ATOM(number_of_variables);
    LOAD_ATOM(number_of_bound_variables);
    LOAD_ATOM(number_of_unbound_variables);    
    LOAD_ATOM(clause_n_counter);
    LOAD_ATOM(clause_d_counter);
    LOAD_ATOM(clause_2_counter);
    LOAD_ATOM(clause_3_counter);
    LOAD_ATOM(edge_2_counter);
    LOAD_ATOM(edge_d_counter);    
    LOAD_ATOM(bcp_counter);
    LOAD_ATOM(conflict_counter);    
    LOAD_ATOM(unit);
    LOAD_ATOM(use);
    LOAD_ATOM(reset);
    LOAD_ATOM(level);
    LOAD_ATOM(max_level);
    LOAD_ATOM(max_bound);
    LOAD_ATOM(symbol);    
    LOAD_ATOM(xref);
    LOAD_ATOM(clause_hash);    
    LOAD_ATOM(implication);    
    LOAD_ATOM(implication_clause);
    LOAD_ATOM(implication_pos);
    LOAD_ATOM(is_atom);
    LOAD_ATOM(edge);
    LOAD_ATOM_STRING(exclamation_mark, "!");
    LOAD_ATOM(literal_size);
    LOAD_ATOM(literal_integer);    
    LOAD_ATOM(value_packing);

// misc
    LOAD_ATOM(qtype);
    LOAD_ATOM(fifo);
    LOAD_ATOM(lifo);
    LOAD_ATOM(recursive);
    LOAD_ATOM(varp);    
// exceptions
    LOAD_ATOM(system_limit);
}

static void varp_down(ErlNifEnv* env, void* obj,
		      ErlNifPid* pid, ErlNifMonitor* mon)
{
    UNUSED(env);
    UNUSED(pid);    
    varp_t* vp = (varp_t*) obj;
    subscription_t** spp = &vp->subs;
    
    DBG("varp_down called\r\n");

    while(*spp) {
	subscription_t* sp = *spp;
	if (enif_compare_monitors(mon, &sp->mon) == 0) {
#ifdef DEBUG
	    char buf[80];
	    enif_snprintf(buf, sizeof(buf), "process %T died",
			  enif_make_pid(env, &sp->pid));
	    enif_fprintf(stdout, "%s\r\n", buf);
#endif
	    *spp = sp->next;
	    varp_free(&vp->sub_allocator, sp);
	    return;
	}
	spp = &(sp)->next;
    }
}

static void varp_dtor(ErlNifEnv* env, void* obj)
{
    UNUSED(env);
    varp_t* vp = (varp_t*) obj;
#ifdef DEBUG_MEM
    enif_fprintf(stdout, "allocated memory before dtor = %ld\r\n",
	   varp_allocated);
#endif    
    cleanup(vp);
#ifdef DEBUG_MEM
    enif_fprintf(stdout, "allocated memory after dtor = %ld\r\n",
		 varp_allocated);
#endif
}

static void varp_stop(ErlNifEnv* env, void* obj,
		      ErlNifEvent event, int is_direct_call)
{
    UNUSED(env);
    varp_t* vp = (varp_t*) obj;
    UNUSED(vp);
    UNUSED(event);
    UNUSED(is_direct_call);    
    DBG("varp_stop called\r\n");
    // clean up an event (close it)
}

static int varp_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    UNUSED(env);
    UNUSED(load_info);
    ErlNifResourceTypeInit rinit;

    rinit.dtor = varp_dtor;
    rinit.stop = varp_stop;
    rinit.down = varp_down;

    // Create resource types
    varp_res = enif_open_resource_type_x(env, "varp", &rinit,
					 ERL_NIF_RT_CREATE,
					 &tried);
    load_atoms(env);
    *priv_data = 0;
    return 0;
}

static int varp_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
			ERL_NIF_TERM load_info)
{
    ErlNifResourceFlags tried;
    UNUSED(load_info);
    ErlNifResourceTypeInit rinit;

    rinit.dtor = varp_dtor;
    rinit.stop = varp_stop;
    rinit.down = varp_down;
    
    varp_res = enif_open_resource_type_x(env, "varp", &rinit,
					 ERL_NIF_RT_CREATE |
					 ERL_NIF_RT_TAKEOVER,
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
