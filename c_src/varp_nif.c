//
// NIF library for running watched literals clauses
//

#ifdef __linux__
#define _GNU_SOURCE
#endif

#if defined(__WIN32__) || defined(_WIN32)
#include <windows.h>
#include <malloc.h>
#endif

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <stddef.h>
#include <time.h>
#include <errno.h>
#include <memory.h>
#include <limits.h>
#include <math.h>
#include <float.h>
#include "erl_nif.h"

#define DOUBLE_ORDER
#include "cdlist.h"
#include "slist.h"
#include "dlist.h"
#include "dynarr.h"
#include "dynvar.h"
#include "dynvec.h"

#include "xnif_funcs.h"

#define EPSILON (4*FLT_EPSILON) // 1.19e-07

#include "vsn.h"

#ifndef VARP_VSN
#define VARP_VSN "0.0.0-unknown"
#endif

#define DYN_SYMTAB_INIT  8
#define DYN_HASHTAB_INIT 8
#define DYN_UNDO_INIT    7
#define DYN_MARK_INIT    8

#define MAX_BCP_DEPTH  1000

// Erlang is 1 based Python is 0 based
#ifdef PYNIF
#define TUPLEINDEX(i) (i)
#else
#define TUPLEINDEX(i) ((i)+1)
#endif

//
// configurations
// NIF_TRACE
// ASSERTIONS         various sanity test in runtime (during test)
// DEBUG              various output during debug
// DEBUG_BCP          print clauses during bcp
// DEBUG_NBCP         print level information during nbcp
// DEBUG_ORDER        print order handling info
// VALIDATE_TWL       check TWL data structures after clause changes
// LIT_SIZE           literals are represented as integers, size=8,16,32,64
//

#define LIT_SIZE 32

// #define NIF_TRACE
// #define DEBUG
//#define DEBUG_BCP
//#define DEBUG_NBCP
//#define DEBUG_ORDER

//#define ASSERTIONS
//#define VALIDATE_TWL
//#define VALIDATE_MODEL


#ifdef ASSERTIONS
// #define NDEBUG
#include <assert.h>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

#define false 0
#define true  1

typedef uint8_t bool_t;

#if defined(__WIN32__) || defined(_WIN32)
#define TYPEOF(x) decltype(x)
#else
#define TYPEOF(x) __typeof__(x)
#endif

typedef enum {
    q_lifo = 0,
    q_fifo = 1,
    q_recursive = 2
} qtype_t;

typedef enum {
    m_none = 0,
    m_local = 1,
    m_global = 2,
    m_recursive = 3
} minimize_t;

// counters
#define CLAUSE_MON_COUNTER    0   // cp->select
#define CLAUSE_2_COUNTER      1   // cp->select
#define CLAUSE_3_COUNTER      2   // cp->select
#define CLAUSE_N_COUNTER      3   // cp->select
#define BCP_COUNTER           4   // number of bcp
#define CLAUSE_DEAD_COUNTER   5   // count number of dead clauses
#define CONFLICT_COUNTER      6   // number of conflicts
#define PROPAGATION_COUNTER   7   // number of propgations
#define DECISION_COUNTER      8   // number of decisions
#define MARK_COUNTER          9   // number of marks
#define NUM_COUNTERS 10

// #define COUNT(vp, cnt)
#define COUNT(vp, cnt) vp->counter[(cnt)]++

// use LSB bit to signal negation, this makes it easy
// to use cantor pair encoding since literals have as
// low numbers as possible

typedef enum {
    I_UNDEF = 0,  // 00
    I_BOUND = 1,  // 01
    I_TRUE  = 2,  // 10
    I_FALSE = 3   // 11
} ival_t;

// ival encoding
#define I_UNPACK(x)      ((x)&0x3)
#define I_PACK(x)        ((x)&0x3)
#define I_NEG(x)         ((x)^1)
#define I_CONST(x)       ((x)&2)
#define I_SIGN(x)        ((x)&1)

// literal encoding
#define IMPORT(x)      (((x)<0) ? (((-(x))<<1)|1) : ((x)<<1))
#define EXPORT(y)      (((y)&1) ? -((int)((y)>>1)) : ((int)((y)>>1)))
#define INDEX(x)       ((x)>>1)   // variable index
#define L_NEG(x)       ((x)^1)    // negate literals
#define L_VAR(x)       ((x)&(~1)) // get positive literal (var)
#define L_SIGN(x)      ((x)&1)    // sign=1 if negative, positive otherwise
#define MAKE_LIT(v,neg) (((v)<<1)+(neg))

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

#define DBG1(...) do { fprintf(stderr, __VA_ARGS__); fflush(stderr); } while(0)
#define DBG0(...)

#ifdef DEBUG
#define DBG(...) do { fprintf(stderr, __VA_ARGS__); fflush(stderr); } while(0)
#else
#define DBG(...)
#endif

#if defined(DEBUG_BCP)
#define DBG_BCP(...) enif_fprintf(stdout, __VA_ARGS__)
#else
#define DBG_BCP(...)
#endif

#if defined(DEBUG_NBCP)
#define DBG_NBCP(...) enif_fprintf(stdout, __VA_ARGS__)
#else
#define DBG_NBCP(...)
#endif

#if defined(DEBUG_ORDER)
#define DBG_ORDER(...) enif_fprintf(stdout, __VA_ARGS__)
#else
#define DBG_ORDER(...)
#endif

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

#define UNUSED(x) (void)(x)

static int varp_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varp_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data,
			ERL_NIF_TERM load_info);
static void varp_unload(ErlNifEnv* env, void* priv_data);

#define NIF_LIST \
    NIF( "new",                 1,  varp_new )	 \
    NIF( "clone",               2,  varp_clone ) \
    NIF( "info",                2,  varp_info )	  \
    NIF( "config",              3,  varp_config )	\
    NIF( "add_variable",        1,  varp_add_variable ) \
    NIF( "add_variable",        2,  varp_add_variable ) \
    NIF( "add_variable",        3,  varp_add_variable ) \
    NIF( "add_variables",       2,  varp_add_variables ) \
    NIF( "add_variables",       3,  varp_add_variables ) \
    NIF( "add_variables",       4,  varp_add_variables ) \
    NIF( "value",               2,  varp_value ) \
    NIF( "level",               1,  varp_level)	\
    NIF( "bound",               2,  varp_bound )	\
    NIF( "bind",                2,  varp_bind )		\
    NIF( "decide",              2,  varp_decide )	\
    NIF( "subst",               3,  varp_subst )	      \
    NIF( "implication_clause",  2,  varp_implication_clause ) \
    NIF( "implication_level",   2,  varp_implication_level )  \
    NIF( "conflicting_clause",  2,  varp_conflicting_clause ) \
    NIF( "is_variable",         2,  varp_is_variable ) \
    NIF( "is_bound",            2,  varp_is_bound ) \
    NIF( "is_equal",            3,  varp_is_equal ) \
    NIF( "isused",              2,  varp_is_used ) \
    NIF( "isused",              3,  varp_is_used )   \
    NIF( "isatom",              2,  varp_is_atom ) \
    NIF( "isatom",              3,  varp_is_atom )   \
    NIF( "push",                1,  varp_push_level ) \
    NIF( "pop",                 1,  varp_pop_level ) \
    NIF( "pop",                 2,  varp_pop_level ) \
    NIF( "bcp",                 1,  varp_bcp ) \
    NIF( "bcp",                 2,  varp_bcp )	\
    NIF( "bcp",                 3,  varp_bcp )	\
    NIF( "nbcp",                1,  varp_nbcp ) \
    NIF( "vbcp",                2,  varp_vbcp ) \
    NIF( "vbcp",                3,  varp_vbcp ) \
    NIF( "undo",                1,  varp_undo ) \
    NIF( "add_clause",          2,  varp_add_clause ) \
    NIF( "add_clause",          3,  varp_add_clause ) \
    NIF( "get_clause",          2,  varp_get_clause ) \
    NIF( "get_clause",          3,  varp_get_clause ) \
    NIF( "get_clause",          4,  varp_get_clause ) \
    NIF( "get_clause",          5,  varp_get_clause )  \
    NIF( "find_clause",         2,  varp_find_clause ) \
    NIF( "compress_clause",     2,  varp_compress_clause )  \
    NIF( "clause_info",         3,  varp_clause_info )  \
    NIF( "variable_info",       3,  varp_variable_info )  \
    NIF( "literal_info",        3,  varp_literal_info ) \
    NIF( "del_clause",          2,  varp_del_clause )  \
    NIF( "clean_clause",        2,  varp_clean_clause )  \
    NIF( "get_clauses",         3,  varp_get_clauses ) \
    NIF( "get_decision",        2,  varp_get_decision ) \
    NIF( "get_undo_state",      2,  varp_get_undo_state ) \
    NIF( "get_bindings",        1,  varp_get_bindings )	  \
    NIF( "get_bindings",        2,  varp_get_bindings ) \
    NIF( "get_bindings",        3,  varp_get_bindings ) \
    NIF( "get_bindings",        4,  varp_get_bindings ) \
    NIF( "get_nbindings",       3,  varp_get_nbindings ) \
    NIF( "get_nbindings",       4,  varp_get_nbindings ) \
    NIF( "get_number_of_bindings", 2,  varp_get_number_of_bindings ) \
    NIF( "order_sort",          2,  varp_order_sort ) \
    NIF( "order_sort",          3,  varp_order_sort ) \
    NIF( "order_sort",          4,  varp_order_sort ) \
    NIF( "order_first",         2,  varp_order_first ) \
    NIF( "order_last",          2,  varp_order_last ) \
    NIF( "next_unbound",        1,  varp_next_unbound )  \
    NIF( "next_unbound",        2,  varp_next_unbound )  \
    NIF( "queue_first",         1,  varp_queue_first )	\
    NIF( "queue_next",          2,  varp_queue_next ) \
    NIF( "queue_clear",         1,  varp_queue_clear ) \
    NIF( "add_symbol",          3,  varp_add_symbol) \
    NIF( "find_symbol",         2,  varp_find_symbol ) \
    NIF( "first_symbol",        1,  varp_first_symbol ) \
    NIF( "next_symbol",         2,  varp_next_symbol ) \
    NIF( "del_symbol",          2,  varp_del_symbol) \
    NIF( "use_clause",          2,  varp_use_clause ) \
    NIF( "bump",                3,  varp_bump )     \
    NIF( "subscribe",           2,  varp_subscribe ) \
    NIF( "clauseset_size",      2,  varp_clauseset_size ) \
    NIF( "clauseset_offset",    2,  varp_clauseset_offset ) \
    NIF( "clauseset_offset",    3,  varp_clauseset_offset ) \
    NIF( "clauseset_sort",      2,  varp_clauseset_sort )   \
    NIF( "clauseset_first",     2,  varp_clauseset_first )  \
    NIF( "clauseset_next",      2,  varp_clauseset_next )   \
    NIF( "conflict",            3,  varp_conflict )	  \
    NIF( "conflict",            4,  varp_conflict )	  \
    NIF( "minimize",            2,  varp_minimize )	  \
    NIF( "minimize",            3,  varp_minimize )	  \
    NIF( "move_clause",         3,  varp_move_clause ) \
    NIF( "unmark",              1,  varp_unmark ) \
    NIF( "mark",                2,  varp_mark ) \
    NIF( "mark",                3,  varp_mark ) \
    NIF( "intersect_marks",     2,  varp_intersect_marks ) \
    NIF( "intersect_var",       4,  varp_intersect_var ) \
    NIF( "get_marked",          2,  varp_get_marked) \
    NIF( "rand",                1,  varp_rand) \
    NIF( "noop",                1,  varp_noop )

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

#define MAX_INT32         0x7fffffff
#define MAX_UINT32        0xffffffff
#define MAX_CONFLICTING   1024

#define DEFAULT_MAP_SIZE  1024

#define MAX_MAP_SIZE       (1024*1024)   // max inital size
#define MAX_MAP_EXPAND     (256*1024)    // max expand

#define HEAP_BLOCK_SIZE      (512*1024)
#define MAX_HEAP_ALLOC_SIZE  (HEAP_BLOCK_SIZE - sizeof(heap_t))
#define HEAP_ALIGN           sizeof(void*)

#define AMASK(ptr,align) (((intptr_t)(ptr)) & ((align)-1))
#define ALIGN(ptr,align) ((((intptr_t) (ptr))+(align)-1) & ~((align)-1))
#define PAD(ptr,align)   (((align)-AMASK(ptr,align)) & ((align)-1))

#define ABS(x) (((x)<0) ? (-(x)) : (x))

#define	RANDOMDEV	"/dev/urandom"

typedef struct _heap_t
{
    slink_t  link;              // next heap block link
    uint8_t* current;           // must be aligned
    uint8_t* end;
    uint8_t base[0];
} heap_t;

// objects may be slist/dlist or cdlist
typedef struct _object_t
{
    uint8_t data[sizeof(cdlink_t)];
} object_t;

typedef struct _allocator_t
{
    size_t size;         // object size
    slist_t heap_list;   // heaps of data
    slist_t free_list;   // list of free objects
} allocator_t;

// Dirty scheduler stack size is set to 40K default?
#define ONSTACK_LIMIT (64*1024)

#define ON_STACK(n) ((n) < ONSTACK_LIMIT)

#if defined(__WIN32__) || defined(_WIN32)

#define ALLOC_STACK(onstk,n)  ((onstk) ? _malloca((n)) : malloc((n)))
#define FREE_STACK(onstk,ptr) if ((onstk)) _freea((ptr)); else free((ptr))
#else
#define ALLOC_STACK(onstk,n) ((onstk) ? alloca((n)) : malloc((n)))
#define FREE_STACK(onstk,ptr)  if (!(onstk)) free((ptr))
#endif

#define STK_BEGIN(type,name,n) do { int name##_onstack = ON_STACK((n)); type* name = ALLOC_STACK(name##_onstack,sizeof(type)*(n)); do {
#define STK_LEAVE(name) goto L##name
#define STK_END0(name) } while(0); FREE_STACK(name##_onstack,(name)); } while(0)
#define STK_END(name)  } while(0); L##name: FREE_STACK(name##_onstack,(name)); } while(0)

#if LIT_SIZE == 8
typedef uint8_t lit_t;
#define VLIMIT 0x7e
#elif LIT_SIZE == 16
typedef uint16_t lit_t;
#define VLIMIT 0x7ffe
#elif LIT_SIZE == 32
typedef uint32_t lit_t;
#define VLIMIT 0x07ffffff
#elif LIT_SIZE == 64
typedef uint64_t lit_t;
#define VLIMIT 0x07ffffff
#endif

#define LIT_TRUE   ((lit_t)0)
#define LIT_FALSE  ((lit_t)1)
#define LIT_NONE   ((lit_t)-1)

typedef uint16_t markbits_t;

#define VAR_MARKL   0x0001  // literal is on mark stack
#define VAR_MARK0   0x0002
#define VAR_MARK1   0x0004
#define VAR_MARKN   0x0008
#define LIT_MARK0   0x0010
#define LIT_MARK1   0x0020
#define LIT_MARKQ   0x0080  // literal is inq
#define VAR_ATOM    0x0100
#define VAR_USED    0x0200

typedef struct _literal_t
{
    struct _wlink_t* wlist;    // list of watch positions
    dynarray_t* xref;          // (cix_t) cross references when enabled
    dynarray_t* sref;          // (sref_t) list of symbol/pos references
} literal_t;

typedef uint32_t cix_t;             // clause index type <<set:2,index:30>>
typedef int32_t  pos_t;             // literal position type (-1 = invalid)
#define CLAUSE_NONE  ((cix_t) -1)
#define CLAUSE_TRUE  ((cix_t) -2)   // never stored, just returned
#define CLAUSE_FALSE ((cix_t) -3)   // never stored, just returned
#define MAKE_CIX(si,ix)  ((((cix_t)(si))<<30)|(ix))
#define GET_SI(cix)      ((int)(((cix)>>30) & 3))
#define GET_IX(cix)      ((cix)&0x3FFFFFFFL)

typedef struct _sref_t
{
    struct _symbol_t* sp;
    int pos;
} sref_t;

#define LIT_POS 0
#define LIT_NEG 1

typedef struct _varlev_t
{
    cix_t   implication_clause;    
    int32_t level;
    ival_t  phase;
} varlev_t;

typedef struct _variable_t     // :cdlink_t in cdlist_t
{
    cdlink_t link;
    uint32_t ix;                 // variable index
    lit_t    bl;                 // bound literal | LIT_NONE
    literal_t lit[2];            // literal containers LIT_POS=0 LIT_NEG=1
} variable_t;

typedef struct _symbol_t // :dlink - dlist
{
    dlink_t link;
    uint32_t hvalue;          // symbol hash
    struct {
	unsigned is_term:1;   // either name is a term or name is binary string
	unsigned is_scalar:1; // if simple variable
    };
    uint8_t* data;            // raw data
    size_t   size;            // raw len
    dynvar(lit_t*, lit);      // array of literals
} symbol_t;

typedef struct _wlink_t
{
    struct _wlink_t* next;
} wlink_t;

// #define USE_CLAUSE_SEGMENTS
#define CLAUSE_BITS    24
#define MAX_CLAUSE_SEGMENT_SIZE ((1 << CLAUSE_BITS)-1)
#define MAX_CLAUSE_OFFSET MAX_CLAUSE_SEGMENT_SIZE
#define DEF_SEGMENT_SIZE (1 << 20)

// sizeof wlink should be 4 on 32 bit machine or 8 on 64 bit machine
// 32 bit machine alignement should be 2*4 = 8 bytes
// 64 bit machine alignement should be 2*8 = 16 bytes
#define CLAUSE_ALIGNMENT (2*sizeof(wlink_t))

typedef struct _clause_t
{
    wlink_t    wl[2];        // ALIGNED watch point 1&2+links (DO NOT MOVE!)
    cix_t      cix;          // clause id (index) 0..n-1  (<< 1)
    uint32_t   size;         // number of literals in lit
    uint32_t hvalue;         // clause hash value
    struct {
	unsigned offset:CLAUSE_BITS;  // offset to segment start
	unsigned dead:1;      // clause is dead
	unsigned conflict:1;  // conflict list
	unsigned watched:1;   // clause is watched
	unsigned unwatch:1;   // clause is scheduled to be unwatched
	unsigned delete:1;    // marked for deletion
	unsigned dynamic:1;   // not in a segment
	unsigned select:2;    // 0=mon,1=2-clause,2=3-clause,3=n_clause	
    };
    uint64_t stamp;          // last used time (bcp_counter clock)
    lit_t lit[];             // literal array
} clause_t;

#define MAX_CLAUSE_LENGTH ((MAX_CLAUSE_SEGMENT_SIZE-CLAUSE_ALIGNMENT)/sizeof(clause_t))

// clause_t storage
typedef struct _clause_segment_t  // :slink_t in slist
{
    struct _clause_segment_t* next;
    uint32_t nallocated;  // number of clauses stored
    uint32_t ndeleted;    // number of clauses marked for deletion
    uint32_t size;        // number of bytes allocated in data
    int      si;          // segment index = DELTA/GAMMA/BETA/ALPHA
    uint8_t* ptr;         // allocation point
    uint8_t* end;         // end of data point
    uint8_t  data[];      // clause data storage
} clause_segment_t;

// hash structure
typedef struct _hlink_t // :slink_t in slist_t
{
    slink_t link;
    uint32_t hvalue;
    cix_t cix;
} hlink_t;

typedef enum {
    uUNDEF   = 0,
    uSET     = 1,
    uTOGGLE  = 2,
    uDONE    = 3
} bnd_state_t;

typedef struct _bindings_t
{
    lit_t decision;            // decision literal or L_FALSE
    ival_t value;              // decision value
    bnd_state_t t;             // used by undo
    int    offs;               // start offset in vp->bnd_map
    int    size;               // number of bindings from offset
} bindings_t;

#define bindings_at(vp,level) ((vp)->bnd_map + (vp)->bnd[level].offs)
#define bindings(vp,up) (vp->bnd_map + (up)->offs)

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
#define SUB_FLAG_NUM_CLAUSES 0x0040    // report number of clauses
#define SUB_FLAG_NUM_DEAD    0x0080    // report number of dead clauses
#define SUB_FLAG_MAX_LEVEL   0x0100    // report max level sinc last
#define SUB_FLAG_MAX_BOUND   0x0200    // report max bound variables since last
#define SUB_FLAG_NUM_SUBST   0x0400    // report number of susbstitutions
#define SUB_FLAG_MIN_LEVEL   0x0100    // report min level (at conflict)
#define SUB_FLAG_NUM_CONFL   0x0200    // report number of conflicts
#define SUB_FLAG_NUM_PROP    0x0400    // report number of propagations
#define SUB_FLAG_NUM_DECI    0x0800    // report number of decisions
#define SUB_FLAG_NUM_BCP     0x1000    // report number of decisions

typedef struct _subscription_t {   // :dlink_t in dlist_t
    dlink_t link;
    ErlNifPid pid;                 // the subscriber pid
    ErlNifMonitor mon;             // monitor the pid
    uint32_t      flags;           // subscription flags
} subscription_t;

#define DELTA 0    // permanent clause set
#define GAMMA 1    // learnt clause set
#define BETA  2    // temporary clause set
#define ALPHA 3    // temporary clause set

#define NUM_CSET 4

typedef struct _varp_config_t
{
    qtype_t  qtype;      // literal queue is fifo/lifo/recursive
    bool_t   xref;       // xref used or not    
    bool_t   hash;       // clause has or not
    bool_t   vsids;      // variable state independent decaying sum
    bool_t   use_phase;  // use saved phase
    bool_t   all_used;   // all variables are used
    ival_t   init_phase; // initial phase selection (TRUE|FALSE|UNDEF)
    size_t   vsize;
    size_t   csize;
    uint64_t seed;
} varp_config_t;

typedef struct _varp_new_opt_t {
    varp_config_t config;
} varp_new_opt_t;

typedef struct _varp_clone_opt_t {
    varp_config_t config;
    // one bit per clauseset to clone
    // default = (1 << DELTA)
    int clauseset;
    // clone all bindings upto level (including)
    int level;
    // clone queue
    bool_t queue;
} varp_clone_opt_t;

typedef struct _varp_t {
    varp_config_t opt;        // varp configs
    uint32_t cnum[NUM_CSET];  // number of clauses (not counting holes)
    uint32_t coffs[NUM_CSET]; // offset for clause iterator
    uint32_t cfree[NUM_CSET]; // number of clauses marked as free
    uint32_t cdead[NUM_CSET]; // number of dead clauses (level=0)

    uint64_t counter[NUM_COUNTERS];

    int num_conflicting;      // number of conflicting clauses saved
    int max_conflicting;      // max number of conflicting <= MAX_CONFLICTING
    cix_t conflicting_clauses[MAX_CONFLICTING];

    dynvar(variable_t**, var_map);
    dynvar(lit_t*,       bnd_map);  // literal value bindings

    dynvar(markbits_t*, lit_mark);  // mark bits for every literal
    dynvar(uint8_t*, lit_value); // ivals for every lit_t value
    uint16_t*    lit_overlay;    // literal overlay access (not neg and pos)
    dynvar(varlev_t*, var_lev);  // implication clause (reason)/leve and phase

    dynvar(lit_t*, mark_stack);  // list/stack of marked variables
    
    size_t       snum;          // number of symbols in symbol hash table
    dynvar(dlist_t*,symtab);    // symbol hash table (of symbol_t*)
    size_t       hnum;          // number of clauses in clause hashtab
    dynvar(slist_t*,hashtab);   // clause hash table (of hlink_t*)
    dynvec(clause_t**,clauseset,NUM_CSET); // array of clausesets, entries may be null
    size_t num_segs;
    clause_segment_t* clauseseg[NUM_CSET];  // allocation sets
    cdlist_t     order_list;    // doubly linked order list
    variable_t*  top;           // first unbound variable

    dynvar(clause_t**, unwatch); // clauses to unwatch (check after bcp) 
    dynvar(bindings_t*,bnd);     // stack of bindings, one for each level
    size_t       num_bound;     // #bound variables (not current level)
    size_t       num_subst;     // #substitions < #bound
    size_t       max_bound;     // max bound variables since last check
    int32_t      level;         // current undo level
    int32_t      max_level;     // statistics max level since last check
    int32_t      min_level;     // statistics min level since last check

    dynvar(lit_t*, q);          // queue/stack of literals

    variable_t constant;

    arc4_stream_t as;              // random stream
    uint8_t asb;                   // random byte for init_phase=UNDEF
    int phase_shift;               // shift counter
    int report_index;              // next index to report for log_permanent
    dlist_t subs;                  // list of subscriptions

    ErlNifEnv*      msg_env;       // message environment
    ErlNifEnv*      caller_env;    // message environment

    dynvar(lit_t*, tlit);          // temporary clause
    dynvar(lit_t*, ulit);          // temporary clause

    allocator_t dyn_allocator;     // heap storage for dyn_t
    allocator_t var_allocator;     // heap storage for variable_t
    allocator_t sym_allocator;     // heap storage for symbols_t
    allocator_t sub_allocator;     // heap storage for subscription_t
    allocator_t hlink_allocator;   // heap storage for hlink_t
} varp_t;

#define LL_TRUE(vp)    (&(vp)->constant.lit[LIT_POS])
#define LL_FALSE(vp)   (&(vp)->constant.lit[LIT_NEG])


#define MIN(a,b) (((a)<(b)) ? (a) : (b))
#define MAX(a,b) (((a)>(b)) ? (a) : (b))
#define SWAP_INT(a,b) do { \
	int _t = (a); a=(b); b=(_t);		\
    } while(0)

ErlNifResourceType* varp_res;

static cix_t add_clause_array(varp_t* vp, int si,
			      lit_t* lit, size_t size, bool_t put_unit);

void print_clause(varp_t* vp, char* label, clause_t* cp);
void print_lit_array(char* label, lit_t* lit, size_t size);

static char* bnd_state_name[] = {
    [uUNDEF]  = "undef",
    [uSET]    = "set",
    [uTOGGLE] = "toggle",
    [uDONE]   = "done"
};


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


#define EQUAL_KEY(env, name, arg)				\
    (((arg) == ATOM(name)) || (equal_string(env, ATOM(name), arg)))

DECL_ATOM(alpha);
DECL_ATOM(atom);
DECL_ATOM(beta);
DECL_ATOM(bcp_counter);
DECL_ATOM(clause_2_counter);
DECL_ATOM(clause_3_counter);
DECL_ATOM(clause_d_counter);
DECL_ATOM(clause_n_counter);
DECL_ATOM(clause_m_counter);
DECL_ATOM(conflict_counter);
DECL_ATOM(propagation_counter);
DECL_ATOM(decision_counter);
DECL_ATOM(mark_counter);
DECL_ATOM(conflict);
DECL_ATOM(dead);
DECL_ATOM(default);
DECL_ATOM(delta);
DECL_ATOM(done);
DECL_ATOM(error);
DECL_ATOM(exclamation_mark);
DECL_ATOM(false);
DECL_ATOM(fifo);
DECL_ATOM(flags);
DECL_ATOM(gamma);
DECL_ATOM(hash);
DECL_ATOM(implication);
DECL_ATOM(implication_clause);
DECL_ATOM(inqueue);
DECL_ATOM(is_atom);
DECL_ATOM(is_used);
DECL_ATOM(jump);
DECL_ATOM(length);
DECL_ATOM(level);
DECL_ATOM(lifo);
DECL_ATOM(literal);
DECL_ATOM(literal_integer);
DECL_ATOM(literal_size);
DECL_ATOM(local);
DECL_ATOM(global);
DECL_ATOM(mark);
DECL_ATOM(max_bound);
DECL_ATOM(max_conflicting);
DECL_ATOM(max_level);
DECL_ATOM(min_level);
DECL_ATOM(number_of_bound_variables);
DECL_ATOM(number_of_clauses);
DECL_ATOM(number_of_conflicting_clauses);
DECL_ATOM(number_of_dead_clauses);
DECL_ATOM(number_of_learnt_clauses);
DECL_ATOM(number_of_subst_variables);
DECL_ATOM(number_of_unbound_variables);
DECL_ATOM(number_of_variables);
DECL_ATOM(number_of_conflicts);
DECL_ATOM(number_of_propagations);
DECL_ATOM(number_of_decisions);
DECL_ATOM(number_of_bcps);
DECL_ATOM(off);
DECL_ATOM(phase);
DECL_ATOM(init_phase);
DECL_ATOM(qtype);
DECL_ATOM(queue);
DECL_ATOM(recursive);
DECL_ATOM(reset);
DECL_ATOM(set);
DECL_ATOM(size);
DECL_ATOM(status);
DECL_ATOM(symbol);
DECL_ATOM(system_limit);
DECL_ATOM(memory_limit);
DECL_ATOM(toggle);
DECL_ATOM(true);
DECL_ATOM(turbo);
DECL_ATOM(undefined);
DECL_ATOM(unit);
DECL_ATOM(use);
DECL_ATOM(use_phase);
DECL_ATOM(all_used);
DECL_ATOM(value_packing);
DECL_ATOM(variable);
DECL_ATOM(varp);
DECL_ATOM(watch);
DECL_ATOM(xref);
DECL_ATOM(vsids);
DECL_ATOM(none);
DECL_ATOM(log2);
DECL_ATOM(log10);
// DECL_ATOM(rank);
DECL_ATOM(next);
DECL_ATOM(version);
DECL_ATOM(seed);
// sort
DECL_ATOM(identity);
DECL_ATOM(p_identity);
DECL_ATOM(n_identity);
DECL_ATOM(e_identity);
DECL_ATOM(random);
DECL_ATOM(p_random);
DECL_ATOM(n_random);
DECL_ATOM(e_random);
DECL_ATOM(degree);
DECL_ATOM(p_degree);
DECL_ATOM(n_degree);
DECL_ATOM(e_degree);
DECL_ATOM(rank);
DECL_ATOM(p_rank);
DECL_ATOM(n_rank);
DECL_ATOM(e_rank);
// memory stats
DECL_ATOM(memory_literal_size);
DECL_ATOM(memory_clause_size);
DECL_ATOM(memory_variable_size);
DECL_ATOM(memory_symbol_size);
DECL_ATOM(memory_size);

#define VARP_ALLOC(n)       enif_alloc((n))
#define VARP_REALLOC(ptr,n) enif_realloc((ptr),(n))
#define VARP_FREE(ptr)      enif_free((ptr))

static heap_t* new_heap_block(size_t size)
{
    heap_t* hp;
    if ((hp = VARP_ALLOC(size + HEAP_ALIGN - 1)) == NULL)
	return NULL;
    hp->current = hp->base + PAD(hp->base,HEAP_ALIGN);
    hp->end     = hp->current + (size - sizeof(heap_t));
    return hp;
}

static void* heap_alloc(slist_t* list, size_t obj_size)
{
    heap_t* hp;
    void* ptr;

    if (obj_size > (HEAP_BLOCK_SIZE - sizeof(heap_t)))
	return NULL;
    if (slist_is_empty(list))
	hp = slist_insert_first(list, new_heap_block(HEAP_BLOCK_SIZE));
    else {
	hp = slist_first(list);
	if (hp->current + obj_size >= hp->end)
	    hp = slist_insert_first(list, new_heap_block(HEAP_BLOCK_SIZE));
    }
    ptr = hp->current;
    hp->current += obj_size;
    return ptr;
}

static void heap_cleanup(slist_t* list)
{
    heap_t* hp = slist_first(list);
    while (hp != NULL) {
	heap_t* hp_next = slist_next(hp);
	VARP_FREE(hp);
	hp = hp_next;
    }
}

static int allocator_init(allocator_t* ap, size_t size)
{
    ap->size = ALIGN(size, HEAP_ALIGN);
    slist_init(&ap->heap_list);
    slist_init(&ap->free_list);
    return 0;
}

static void allocator_cleanup(allocator_t* ap)
{
    heap_cleanup(&ap->heap_list);
    slist_init(&ap->heap_list);
    slist_init(&ap->free_list);
}

static void* obj_alloc(allocator_t* ap)
{
    if (slist_is_empty(&ap->free_list))
	return heap_alloc(&ap->heap_list, ap->size);
    return slist_take_first(&ap->free_list);
}

static void obj_free(allocator_t* ap, void* ptr)
{
    slist_insert_last(&ap->free_list, ptr);
}

// make sure there are at least n "free" objects to
// allocate from
static int obj_pre_alloc(allocator_t* ap, size_t n)
{
    heap_t* hp;    
    size_t m;
    size_t size;
    int i;
    
    // check number of elements are on free list
    m = slist_length(&ap->free_list);
    if (m >= n) return 0;
    n -= m;

    // check number of elements that can be allocated from current heap
    if ((hp = slist_first(&ap->heap_list)) != NULL) {
	size_t r = (hp->end - hp->current) / ap->size;
	for (i = 0; i < (int)r; i++) {
	    void* obj = heap_alloc(&ap->heap_list, ap->size);
	    obj_free(ap, obj);
	}
	n -= r;
    }

    // now create big segement for rest of the objects
    size = n * ap->size;
    if (size < HEAP_BLOCK_SIZE)
	size = HEAP_BLOCK_SIZE;
    if ((hp = new_heap_block(size)) == NULL)
	return -1;
    // printf("add heap block size = %ld\n", size);
    slist_insert_first(&ap->heap_list, hp);
    return (int) n;
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
    int i;
    struct {
	time_t t;
	uint8_t rnd[128 - sizeof(time_t)];
    } rdat;

    memset(&rdat, 0, sizeof(rdat));

    rdat.t = time(0);

#if defined(__WIN32__) || defined(_WIN32)
    for (i = 0; i < (int) sizeof(rdat.rnd); i++)
	rdat.rnd[i] = i;
#else
    {
	FILE* f;
	if ((f = fopen(RANDOMDEV, "r")) != NULL) {
	    int r = fread(rdat.rnd, 1, sizeof(rdat.rnd), f);
	    (void) r;
	    fclose(f);
	}
    }
#endif
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

static void varp_set_seed(varp_t* vp, uint64_t seed)
{
    vp->opt.seed = seed;
    if (!seed)
	arc4_stir(&vp->as);
    else {
	arc4_init(&vp->as);
	arc4_add_random(&vp->as, (uint8_t*)&seed, sizeof(seed));
    }
}

static int equal_string(ErlNifEnv* env, ERL_NIF_TERM atm, ERL_NIF_TERM arg)
{
    char buf[256];
    ERL_NIF_TERM xatm;
    // fixme: hash all atoms at load time
    if (enif_get_string(env, arg, buf, sizeof(buf), ERL_NIF_LATIN1) <= 0)
	return 0;
    if (!enif_make_existing_atom(env, buf, &xatm, ERL_NIF_LATIN1))
	return 0;
    return (atm == xatm);
}

// return 2^r when 2^r > size
static size_t next_pow2(size_t size)
{
    bool_t is_pow2 = (size>0) && ((size & (size-1)) == 0);
    size_t next_size;

    next_size = is_pow2 ? size : 1;
    while(next_size <= size)
	next_size *= 2;
    return next_size;
}

static dynarray_t* dynarray_create(varp_t* vp, size_t capacity, size_t width)
{
    dynarray_t* dp;

    if ((dp = obj_alloc(&vp->dyn_allocator)) != NULL) {
	if (dynarray_init(dp, capacity, width) < 0) {
	    obj_free(&vp->dyn_allocator, dp);
	    return NULL;
	}
    }
    return dp;
}

static dynarray_t* dynarray_empty(varp_t* vp, size_t width)
{
    return dynarray_create(vp, 0, width);
}

static void dynarray_destroy(varp_t* vp, dynarray_t* dp)
{
    if (dp) {
	dynarray_clear(dp);
	obj_free(&vp->dyn_allocator, dp);
    }
}

//
// li is converted into a unsigned representation of
// li < 0 :  2*-li + 1
// li >=0 :  2*li
//
// then li is written as b0...bl
//
#define EXT  0x80
#define MASK  0x7f

#if defined(__WIN32__) || defined(_WIN32)
static int CLZ(int x)
{
    int count = sizeof(x)*8;
    while(x) {
	x >>= 1;
	count--;
    }
    return count;
}
#else
#define CLZ(x)      __builtin_clz((x))
#endif

static int compress_int(int li, uint8_t* ptr)
{
    int len;
    uint8_t* ptr0 = ptr;

    li = (li < 0) ? ((-li)<<1)+1 : li << 1;
    len = sizeof(int)*8 - CLZ(li);
    while(len > 7) {
	*ptr++ = (li & MASK) + EXT;
	li >>= 7;
	len -= 7;
    }
    *ptr++ = (li & MASK);
    return (int)(ptr-ptr0);
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

// Clause pointer from wlink_t pointer
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
    return vp->clauseset[GET_SI(index)][GET_IX(index)];
}

static inline void set_clause(varp_t* vp, cix_t index, clause_t* cp)
{
#ifdef DEBUG
    if (cp == NULL)
	enif_fprintf(stdout, "set_clause %d[%d] = NULL\r\n",
		    GET_SI(index),GET_IX(index));
    else
	print_clause(vp, "set_clause", cp);
#endif
    vp->clauseset[GET_SI(index)][GET_IX(index)] = cp;
}

static size_t get_number_of_clauses(varp_t* vp)
{
    size_t cnum = 0;
    int si;
    for (si = 0; si < NUM_CSET; si++)
	cnum += vp->cnum[si];
    return cnum;
}

// check if literal is negated
//static inline int is_neg_ll(literal_t* lp)
//{
//    return lp->neg;
//}

// return the variable from literal pointer
//static inline variable_t* ll2v(literal_t* lp)
//{
//    return (variable_t*)
//	(((uint8_t*)(lp)) -
//	 (sizeof(variable_t) - (is_neg_ll(lp) ? sizeof(literal_t) :
//				2*sizeof(literal_t))));
//}

// negate a literal
//static inline literal_t* neg_ll(literal_t* lp)
//{
//    return is_neg_ll(lp) ? (lp - 1) : (lp + 1);
//}

static inline literal_t* vindex_ll(varp_t* vp, int i)
{
    ASSERT(i != 0);
    return &vp->var_map[ABS(i)]->lit[(i<0)];
}

static inline lit_t vindex_l(varp_t* vp, int i)
{
    UNUSED(vp);
    return (lit_t) IMPORT(i);
}

static inline int is_neg_l(lit_t l)
{
    return L_SIGN(l);
}

static inline int is_constant_l(varp_t* vp, lit_t l)
{
    UNUSED(vp);
    return ((l == LIT_TRUE) || (l == LIT_FALSE));
}

static inline int export_l(lit_t l)
{
    return EXPORT(l);
}

static inline ERL_NIF_TERM external_l(ErlNifEnv* env,lit_t l)
{
    if (l == LIT_TRUE)
	return enif_make_boolean(env, true);
    else if (l == LIT_FALSE)
	return enif_make_boolean(env, false);
    else
	return enif_make_int(env, export_l(l));
}

static inline lit_t neg_l(lit_t l)
{
    return L_NEG(l);
}

static inline literal_t* l2ll(varp_t* vp, lit_t xl)
{
    return &vp->var_map[INDEX(xl)]->lit[L_SIGN(xl)];
}

// access variable from lit_t
static inline variable_t* var_l(varp_t* vp, lit_t l)
{
    return vp->var_map[INDEX(l)];
}

static inline ival_t get_vv(varp_t* vp, variable_t* var)
{
    return (ival_t) vp->lit_value[(var->ix)<<1];
}

static inline void clr_vv(varp_t* vp, variable_t* var)
{
    vp->lit_overlay[var->ix] = (I_UNDEF << 8) | I_UNDEF;    
}

static inline void bnd_vv(varp_t* vp, variable_t* var)
{
    vp->lit_overlay[var->ix] = (I_BOUND << 8) | I_BOUND;        
}

static inline void set_vv(varp_t* vp, variable_t* var, ival_t ivalue)
{
#if BYTE_ORDER == LITTLE_ENDIAN
    vp->lit_overlay[var->ix] = (I_NEG(ivalue)<<8) | ivalue;
#else
    vp->lit_overlay[var->ix] = (ivalue<<8) | I_NEG(ivalue);
#endif
}

static inline void clr_value(varp_t* vp, lit_t xp)
{
    vp->lit_overlay[INDEX(xp)] = (I_UNDEF << 8) | I_UNDEF;    
}

static inline void set_value(varp_t* vp, lit_t xp, ival_t ivalue)
{
#if BYTE_ORDER == LITTLE_ENDIAN
    vp->lit_overlay[INDEX(xp)] = (I_NEG(ivalue)<<8) | ivalue;
#else
    vp->lit_overlay[INDEX(xp)] = (ivalue<<8) | I_NEG(ivalue);
#endif
}

static inline void set_lev_phase(varp_t* vp, lit_t xp,
				 int level, cix_t cix, ival_t phase)
{
    varlev_t* vlp = &vp->var_lev[INDEX(xp)];
    vlp->level = level;
    vlp->implication_clause = cix;
    vlp->phase = phase;
}

static inline void set_lev(varp_t* vp, lit_t xp, int level, cix_t cix)
{
    varlev_t* vlp = &vp->var_lev[INDEX(xp)];
    vlp->level = level;
    vlp->implication_clause = cix;
}

static inline ival_t get_value(varp_t* vp, lit_t l)
{
    return vp->lit_value[l];
}

static inline lit_t resolve_lit(varp_t* vp, lit_t xl)
{
    lit_t yl;
    while ((yl = vp->var_map[INDEX(xl)]->bl) != LIT_NONE)
	xl = is_neg_l(xl) ? L_NEG(yl) : yl;
    return xl;
}

static inline int phase_export(varp_t* vp, variable_t* var)
{
    return (vp->var_lev[var->ix].phase == I_FALSE) ? -var->ix : var->ix;
}

static inline ival_t decide_phase(varp_t* vp, lit_t xp)
{
    ival_t v;
    if (vp->opt.use_phase) { // use "saved" phase
	v = vp->var_lev[INDEX(xp)].phase;
    }
    else
	v = vp->opt.init_phase;
    if (v == I_UNDEF) {
	uint8_t asb = vp->asb;
	int shr = vp->phase_shift;
	if (shr >= 8) {
	    vp->asb = asb = arc4_getbyte(&vp->as);
	    shr = 0;
	}
	v = ((asb >> shr) & 1) ? I_TRUE : I_FALSE;
	vp->phase_shift = shr+1;
    }
    return v;
}

static inline int variable_is_bound(varp_t* vp, variable_t* var)
{
    return get_vv(vp, var) != I_UNDEF;
}

static inline int variable_is_unbound(varp_t* vp, variable_t* var)
{
    return get_vv(vp, var) == I_UNDEF;
}


// return the lit that the variable is bound to
static inline lit_t lit_vv(varp_t* vp, variable_t* var)
{
    ival_t ival = get_vv(vp, var);
    ASSERT(I_CONST(ival));
    return (ival == I_FALSE) ?
	vindex_l(vp, -var->ix) : vindex_l(vp, var->ix);
}

// return the lit that the variable is bound to
static inline lit_t lit_l(varp_t* vp, lit_t xl)
{
    lit_t  vl = L_VAR(xl);
    ival_t ival = get_value(vp, vl);
    ASSERT(I_CONST(ival));
    return (ival == I_FALSE) ? L_NEG(vl) : vl;
}

static inline int lit_markb(varp_t* vp, lit_t xl)
{
    return vp->lit_mark[xl];
}

// check that all markbits are set
static inline int is_marked(varp_t* vp, lit_t xl, markbits_t markbits)
{
    return (vp->lit_mark[xl] & markbits) == markbits;
}

static inline void set_mark(varp_t* vp, lit_t xl, markbits_t markbits)
{
    vp->lit_mark[xl] |= markbits;
}

static inline void clr_mark(varp_t* vp, lit_t xl, markbits_t markbits)
{
    vp->lit_mark[xl] &= ~markbits;
}

// return 1 if marked 0 otherwise
static inline int lit_mark_if_unmarked(varp_t* vp, lit_t xl, markbits_t markbit)
{
    if (!(vp->lit_mark[xl] & markbit)) {
	vp->lit_mark[xl] |= markbit;
	return 1;
    }
    return 0;
}

static inline void add_mark(varp_t* vp, lit_t xl, markbits_t markbits)
{
    lit_t vl = L_VAR(xl);
    if (!is_marked(vp, vl, VAR_MARKL)) {
	dynvar_append(vp->mark_stack, &vl);
	set_mark(vp, vl, VAR_MARKL);
    }
    set_mark(vp, vl, markbits);    
}


static inline void mark0_lit(varp_t* vp, lit_t xl)
{
    lit_t vl = L_VAR(xl);
    if (!is_marked(vp, vl, VAR_MARK0)) {
	add_mark(vp, vl, VAR_MARK0);
	if (is_neg_l(xl))
	    set_mark(vp, vl, VAR_MARKN);
    }
}

// set mark1 when mark0 is set and correct sign is set
static inline void add_mark1_lit(varp_t* vp, lit_t xl)
{
    lit_t vl = L_VAR(xl);
    if (is_marked(vp, vl, VAR_MARK0)) { // must be marked
	int neg = is_marked(vp, vl, VAR_MARKN);
	if (is_neg_l(xl) == neg)
	    set_mark(vp, vl, VAR_MARK1);
    }
}

static inline void unmark_var(varp_t* vp, variable_t* var)
{
    lit_t xl = MAKE_LIT(var->ix, 0);
    clr_mark(vp, xl, VAR_MARKL|VAR_MARK0|VAR_MARK1|VAR_MARKN);
}

// return true iff variable is marked as used or
// variable does occur in some clause
static inline int variable_is_used(varp_t* vp, variable_t* var)
{
    lit_t xl = MAKE_LIT(var->ix, 0);
    return vp->opt.all_used || is_marked(vp, xl, VAR_USED);
}

static inline int variable_is_unused(varp_t* vp, variable_t* var)
{
    return !variable_is_used(vp, var);
}

static inline int lit_is_atom(varp_t* vp, lit_t xl)
{
    return is_marked(vp, L_VAR(xl), VAR_ATOM);
}

// clear before use!  clear all marks and clear mark list
static void unmark_all(varp_t* vp)
{
    size_t nmarked = dynvar_size(vp->mark_stack);
    int i;

    for (i = 0; i < (int)nmarked; i++) {
	lit_t vl = vp->mark_stack[i];
	clr_mark(vp, vl, VAR_MARKL|VAR_MARK0|VAR_MARK1|VAR_MARKN);
    }
    dynvar_resize(vp->mark_stack, 0);
}

static void clear_conflict_marks(varp_t* vp,cix_t* cixv, size_t len)
{
    while(len--) {
	clause_t* cp = get_clause(vp, *cixv++);
	cp->conflict = 0;
    }
}

static uint32_t djb_hash(uint8_t* ptr, size_t len)
{
    uint32_t h = 5381;
    while(len--)
	h = ((h << 5) + h) + (*ptr++);
    return h;
}

// Hash function is : length(L) + [SUM i] Li^2  (mod 2^32)

static inline uint32_t literal_hash_add(uint32_t hvalue, lit_t l)
{
    int32_t li = export_l(l);
    return hvalue + 1 + li*li;
}

static inline uint32_t literal_hash_del(uint32_t hvalue, lit_t l)
{
    int32_t li = export_l(l);
    return hvalue - 1 - li*li;
}

static uint32_t literal_array_hash(varp_t* vp, lit_t* lit, size_t size)
{
    UNUSED(vp);
    uint32_t hvalue = 0;

    while(size--) {
	lit_t l = *lit++;
	ASSERT(l != LIT_TRUE);
	if (l == LIT_FALSE)  // count as zero
	    continue;
	hvalue = literal_hash_add(hvalue, l);
    }
    return hvalue;
}

char* symbol_strname(symbol_t* sp)
{
    if (sp->is_term)
	return "term"; // fixme format term!
    else
	return (char*) sp->data;
}

// format the name of the first symbol alias
char* literal_strname(literal_t* lp)
{
    sref_t* sr = dynarray_element(lp->sref, 0);
    if (sr != NULL)
	return symbol_strname(sr->sp);
    else
	return "";
}

// format the name of the first symbol alias
char* variable_strname(variable_t* var)
{
    return literal_strname(&var->lit[LIT_POS]);
}

// FIXME make thread safe
char* format_variable(variable_t* var)
{
    static char vn1[32];
    static char vn2[32];
    static char* varname = vn2;
    
    varname = (varname == vn1) ? vn2 : vn1;

    if (dynarray_element(var->lit[LIT_POS].sref, 0) != NULL)
	snprintf(varname, sizeof(vn1), "%s", variable_strname(var));
    else
	snprintf(varname, sizeof(vn1), "%d", var->ix);
    return varname;
}

// FIXME make thread safe
char* format_lit(varp_t* vp, lit_t xl)
{
    static char ln1[32];
    static char ln2[32];
    static char* litname = ln2;
    literal_t* lp;    
    char* sign = "";

    if (xl == LIT_TRUE) return "t";
    if (xl == LIT_FALSE) return "f";

    litname = (litname == ln1) ? ln2 : ln1;
    if (is_neg_l(xl)) {
	sign = "!";
	xl = neg_l(xl);
    }
    lp = l2ll(vp, xl);
    if (dynarray_element(lp->sref, 0) != NULL)
	snprintf(litname, sizeof(ln1), "%s%s", sign, literal_strname(lp));
    else
	snprintf(litname, sizeof(ln1), "%s$%d", sign, INDEX(xl));
    return litname;    
}

// FIXME make thread safe
char* indent(int level)
{
    static char buffer[257];
    int n = MIN(128-1, 2*level);
    memset(buffer, ' ', 2*n);
    buffer[n] = '\0';
    return buffer;
}

char* format_ival(ival_t v)
{
    switch(v) {
    case I_UNDEF: return "u";
    case I_FALSE: return "f";
    case I_TRUE:  return "t";
    case I_BOUND:  return "b";
    default: return "?";
    }
}

void print_lit(lit_t l)
{
    if (l == LIT_TRUE)
	enif_fprintf(stdout, "t");
    else if (l == LIT_FALSE)
	enif_fprintf(stdout, "f");
    else if (L_SIGN(l))
	enif_fprintf(stdout, "-%d", INDEX(l));
    else
	enif_fprintf(stdout, "%d", INDEX(l));
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

void print_sym_array(varp_t* vp, lit_t* lit, size_t size)
{
    if (size == 0)
	enif_fprintf(stdout, "[]");
    else {
	unsigned k;
	enif_fprintf(stdout, "[");
	enif_fprintf(stdout, "%s", format_lit(vp, lit[0]));
	for (k=1; k<size; k++)
	    enif_fprintf(stdout, ",%s", format_lit(vp, lit[k]));
	enif_fprintf(stdout, "]");
    }
}

void print_sym_array_nl(varp_t* vp, lit_t* lit, size_t size)
{
    print_sym_array(vp, lit,size);
    enif_fprintf(stdout, "\r\n");
}

void print_clause(varp_t* vp, char* label, clause_t* cp)
{
    unsigned k;
    enif_fprintf(stdout, "%s %d:%d (t=%ld) [%d/%s",
		 label, GET_SI(cp->cix), GET_IX(cp->cix),
		 cp->stamp, export_l(cp->lit[0]),
		 format_ival(get_value(vp,cp->lit[0])));
    for (k=1; k<cp->size; k++)
	enif_fprintf(stdout, ",%d/%s",
		     export_l(cp->lit[k]),
		     format_ival(get_value(vp,cp->lit[k])));
    enif_fprintf(stdout, "]\r\n");
}

void print_sym_clause(varp_t* vp, char* label, clause_t* cp)
{
    enif_fprintf(stdout, "%s id=%d:%d ",
		 label, GET_SI(cp->cix), GET_IX(cp->cix));
    print_sym_array(vp, cp->lit, cp->size);
    if (cp->dead)
	enif_fprintf(stdout, " dead");
    enif_fprintf(stdout, "\r\n");
}


static inline void wlink_clear(wlink_t* wlp)
{
    wlp->next = NULL;
}

static inline void wlink_link(varp_t* vp, wlink_t* wlp, lit_t xl)
{
    literal_t* lp = l2ll(vp, xl);
    wlp->next = lp->wlist;  // link literal
    lp->wlist = wlp;
}

// FIXME: make constant
static void wlink_unlink(varp_t* vp, clause_t* cp, lit_t xl)
{
    UNUSED(vp);
    literal_t* lp = l2ll(vp, xl);
    wlink_t** wlp = &lp->wlist;
    wlink_t* wl;

    while((wl = *wlp) && (clause_pointer(wl) != cp))
	wlp = &(wl->next);
    if (wl != NULL) {
	*wlp = wl->next;  // unlink
	wl->next = NULL;  // do we need to clear this?
    }
}

// remove the 2-WL watch points
static void clause_unwatch(varp_t* vp, clause_t* cp)
{
    if (cp->watched) {
	wlink_unlink(vp, cp, cp->lit[0]);
	wlink_unlink(vp, cp, cp->lit[1]);
	cp->watched = 0;
    }
}

static void schedule_unwatch_clause(varp_t* vp, clause_t* cp)
{
    if (!cp->unwatch) {
	dynvar_append(vp->unwatch, &cp);
	cp->unwatch = 1;
    }
}

static inline void lqueue_insert(varp_t* vp, lit_t xl)
{
    if (lit_mark_if_unmarked(vp, xl, LIT_MARKQ)) {
	int i = dynvar_size(vp->q);
	dynvar_resize(vp->q, i+1);
	vp->q[i] = xl;
    }
}

// always get from head of list(queue)
static inline lit_t lqueue_deq(varp_t* vp)
{
    int i;
    if ((i = dynvar_size(vp->q)) > 0) {
	lit_t xl = vp->q[i-1];
	dynvar_resize(vp->q, i-1);
	clr_mark(vp, xl, LIT_MARKQ);
	return xl;
    }
    return LIT_FALSE;
}

static void lqueue_clear(varp_t* vp)
{
    int i;
    int n = dynvar_size(vp->q);
    for (i = 0; i < n; i++)
	clr_mark(vp, vp->q[i], LIT_MARKQ);
    dynvar_resize(vp->q, 0);
}

// since level size is not included in num_bound we
// must add number of bindings on current level
//
static inline size_t get_num_bound(varp_t* vp)
{
    bindings_t* bp = &vp->bnd[vp->level];
    return vp->num_bound + bp->size;
}

static inline void set_max_bound(varp_t* vp)
{
    size_t n = get_num_bound(vp);
    if (n > vp->max_bound)
	vp->max_bound = n;
}

static inline size_t get_and_reset_max_bound(varp_t* vp)
{
    size_t n = vp->max_bound;
    vp->max_bound = 0;
    return n;
}

static inline void set_max_level(varp_t* vp)
{
    if (vp->level > vp->max_level)
	vp->max_level = vp->level;
}

// Get max level reset and return
static inline int32_t get_and_reset_max_level(varp_t* vp)
{
    int32_t level = vp->max_level;
    vp->max_level = 0;
    return level;
}

static inline void set_min_level(varp_t* vp)
{
    if (vp->level < vp->min_level)
	vp->min_level = vp->level;
}

// Get min level reset and return
static inline int32_t get_and_reset_min_level(varp_t* vp)
{
    int32_t level = vp->min_level;
    vp->min_level = MAX_INT32;  // yes max!
    return level;
}

static ERL_NIF_TERM make_cix(ErlNifEnv* env,cix_t cix)
{
    if (cix == CLAUSE_NONE)
	return enif_make_int(env, -1);
    else
	return enif_make_ulong(env, cix);
}

static int get_num_subscribers(varp_t* vp)
{
    return dlist_length(&vp->subs);
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
    ERL_NIF_TERM sub_info_keys[12] = {
	ATOM(number_of_variables),
	ATOM(number_of_bound_variables),
	ATOM(number_of_clauses),
	ATOM(number_of_dead_clauses),
	ATOM(max_level),
	ATOM(max_bound),
	ATOM(number_of_subst_variables),
	ATOM(min_level),
	ATOM(number_of_conflicts),
	ATOM(number_of_propagations),
	ATOM(number_of_decisions),
	ATOM(number_of_bcps),
    };
    ERL_NIF_TERM values[12] = {
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
	ATOM(undefined),
    };

    if (flags & SUB_FLAG_NUM_VARS)
	values[0] = enif_make_int(env, dynvar_size(vp->var_map)-1);
    if (flags & SUB_FLAG_NUM_BOUND)
	values[1] = enif_make_int(env, get_num_bound(vp));
    if (flags & SUB_FLAG_NUM_CLAUSES)
	values[2] = enif_make_int(env, get_number_of_clauses(vp));
    if (flags & SUB_FLAG_NUM_DEAD) {
	int n = vp->cdead[DELTA]+vp->cdead[GAMMA]+
	    vp->cdead[BETA]+vp->cdead[ALPHA];
	values[3] = enif_make_int(env, n);
    }
    if (flags & SUB_FLAG_MAX_LEVEL) {
	int val = get_and_reset_max_level(vp);
	values[4] = enif_make_int(env, val);
    }
    if (flags & SUB_FLAG_MAX_BOUND) {
	size_t val = get_and_reset_max_bound(vp);
	values[5] = enif_make_int(env, val);
    }
    if (flags & SUB_FLAG_NUM_SUBST)
	values[6] = enif_make_int(env, vp->num_subst);
    if (flags & SUB_FLAG_MIN_LEVEL) {
	int32_t val = get_and_reset_min_level(vp);
	if (val == MAX_INT32)
	    values[7] = ATOM(undefined);
	else
	    values[7] = enif_make_int(env, val);
    }
    if (flags & SUB_FLAG_NUM_CONFL)
	values[8] = enif_make_uint64(env, vp->counter[CONFLICT_COUNTER]);
    if (flags & SUB_FLAG_NUM_PROP)
	values[9] = enif_make_uint64(env, vp->counter[PROPAGATION_COUNTER]);
    if (flags & SUB_FLAG_NUM_DECI)
	values[10] = enif_make_uint64(env, vp->counter[DECISION_COUNTER]);
    if (flags & SUB_FLAG_NUM_BCP)
	values[11] = enif_make_uint64(env, vp->counter[BCP_COUNTER]);    
    return enif_make_map_from_arrays(env, sub_info_keys, values, 12, info);
}

static void log_permanent(varp_t* vp, lit_t xl, lit_t yl)
{
    ErlNifEnv* env = vp->msg_env;
    subscription_t* sp = dlist_first(&vp->subs);

    while (sp != NULL) {
	if ((sp->flags & SUB_FLAG_VAR) ||
	    ((sp->flags & SUB_FLAG_ATOM) && lit_is_atom(vp, xl))) {
	    ERL_NIF_TERM xt;
	    ERL_NIF_TERM yt;
	    ERL_NIF_TERM bnd = ATOM(false);
	    ERL_NIF_TERM info;
	    ERL_NIF_TERM msg;

	    if (yl == LIT_NONE) {
		xt = external_l(env,xl);
		bnd = xt;
	    }
	    else { // lit_is_atom(vp,yl)
		yt = external_l(env,yl);
		xt = external_l(env,xl);
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
	sp = dlist_next(sp);
    }
}

static inline void print_top(varp_t* vp, char* where)
{
    if (vp->top == NULL)
	enif_fprintf(stdout, "%s: top = NULL\r\n", where);
    else 
	enif_fprintf(stdout, "%s: top = %d\r\n", where, vp->top->ix);
}

// this is called when undo'ing a variable
static inline void order_unbind(varp_t* vp, lit_t xl)
{
    clr_value(vp, xl);

    if (vp->top == NULL)
	vp->top = var_l(vp, xl);
    else {
	variable_t* var = var_l(vp, xl);
	if (cdlist_is_before(var, vp->top))
	    vp->top = var;
    }
}

static inline void order_set_top(varp_t* vp, variable_t* var)
{
    if ((vp->top == NULL) || cdlist_is_before(var, vp->top)) {
	vp->top = var;
	// print_top(vp, "order_set_top");
    }
}

// move top if variable is unbound and used then check if variable
static inline void order_move_top(varp_t* vp, variable_t* var)
{
    if (variable_is_unbound(vp, var) && variable_is_used(vp, var)) {
	order_set_top(vp, var);
    }
}

// remove var from order list, update top if needed
static void order_remove(varp_t* vp, variable_t* var)
{
    if (var == vp->top) { // move top if var == top
	if (cdlist_is_last(&vp->order_list, var)) {
	    vp->top = cdlist_prev(var);
	    enif_fprintf(stdout, "set top = %d\r\n", vp->top->ix);
	}
	else {
	    vp->top = cdlist_next(var); // maybe NULL!
	    // print_top(vp, "order_remove");
	}
    }
    cdlist_remove(&vp->order_list, var);
}

static void order_insert_first(varp_t* vp, variable_t* var)
{
    cdlist_insert_first(&vp->order_list, var);
    order_move_top(vp, var);
}

static void order_insert_before(varp_t* vp,variable_t* anchor,variable_t* var)
{
    cdlist_insert_before(&vp->order_list, anchor, var);
    order_move_top(vp, var);
}

// insert var before top and move top if var is unbound
static inline void order_move_before_top(varp_t* vp, variable_t* var)
{
    if (vp->top == NULL) {
	order_remove(vp, var);
	order_insert_first(vp, var);
    }
    else if (var != vp->top) {
	order_remove(vp, var);
	order_insert_before(vp, vp->top, var);
    }
}

// set top when we lost track of it
static int setup_top(varp_t* vp)
{
    variable_t* var = cdlist_first(&vp->order_list);
    while((var != NULL) &&
	  (variable_is_bound(vp, var) || variable_is_unused(vp, var)))
	var = cdlist_next(var);
    vp->top = var;
    // print_top(vp, "setup_top");
    if (var != NULL)
	return var->ix;
    return 0;
}

// get next unbound literal from top
static int next_unbound(varp_t* vp)
{
    variable_t* var;
    if ((var = vp->top) != NULL) {
	while((var != NULL) &&
	      (variable_is_bound(vp, var) || variable_is_unused(vp, var)))
	    var = cdlist_next(var);
	vp->top = var;
	if (var != NULL)
	    return var->ix;
    }
    return 0;
}

static int next_unbound_after(varp_t* vp, variable_t* var)
{
    if (cdlist_is_last(&vp->order_list, var))
	return 0;
    var = cdlist_next(var);
    while((var != NULL) &&
	  (variable_is_bound(vp, var) || variable_is_unused(vp, var)))
	var = cdlist_next(var);
    if (var != NULL)
	return var->ix;
    return 0;
}

static wlink_t** watch_list(varp_t* vp, lit_t xl)
{
    literal_t* xp = l2ll(vp, xl);
    return &xp->wlist;
}

// level=0 work
// after evaluation of a literal in the L literal queue
// schedule all clauses in cross referenced from !L to
// be killed.

static void kill_clauses(varp_t* vp, lit_t xl)
{
    literal_t* xp = l2ll(vp, xl);
    cix_t* xptr = dynarray_element(xp->xref, 0);
    size_t  len  = dynarray_size(xp->xref);

    DBG_BCP("%sKill %s\r\n", indent(vp->level), format_lit(vp, xl));

    while(len--) {
	clause_t* cp = get_clause(vp, *xptr);
	if (cp && !cp->dead) { // not already dead
	    cp->dead = 1;
	    vp->cdead[GET_SI(cp->cix)]++;
	    schedule_unwatch_clause(vp, cp);
	}
	xptr++;
    }
}

static inline void push_l(varp_t* vp, lit_t xp, int level)
{
    bindings_t* bp;
    ASSERT(get_value(vp, xp) == I_UNDEF);
    bp = &vp->bnd[level];
    bindings(vp, bp)[bp->size++] = xp;
}

static inline void put_nq_l(varp_t* vp, lit_t xp, ival_t ivalue,
			    cix_t cix, int level)
{
    DBG_BCP("%sPut %s=%s @%d\r\n", indent(level), format_lit(vp,xp),
	    format_ival(ivalue), level);
    ASSERT(level >= 0);
    ASSERT(var_l(vp, xp)->bl == LIT_NONE);
    ASSERT(!I_CONST(get_value(vp, xp)));

    push_l(vp, xp ^ I_SIGN(ivalue), level);
    ivalue ^= L_SIGN(xp);
    set_value(vp, xp, ivalue);
    set_lev_phase(vp, xp, level, cix, ivalue);
}

static inline void put_l(varp_t* vp, lit_t xl, ival_t ivalue,
			 cix_t cix, int level)
{
    put_nq_l(vp, xl, ivalue, cix, level);
    if (ivalue == I_TRUE)
	lqueue_insert(vp, neg_l(xl));
    else if (ivalue == I_FALSE)
	lqueue_insert(vp, xl);
}

static void init_level(varp_t* vp, int level)
{
    ASSERT(level < (int)dynvar_size(vp->undo));

    DBG_ORDER("%sInit_level @%d\r\n", indent(level), level);
    vp->bnd[level].decision = LIT_FALSE;
    vp->bnd[level].t  = uUNDEF;
    vp->bnd[level].offs = 0;
    vp->bnd[level].size = 0;
}

// resize binding stack to include 'level'
static int resize_levels(varp_t* vp, size_t level)
{
    size_t n = dynvar_size(vp->bnd);
    int i;
    if (dynvar_resize(vp->bnd, level+1) < 0)
	return -1;
    for (i = (int)n; i <= (int)level; i++)
	init_level(vp, i);
    return 0;
}

// pop level
static int pop_level(varp_t* vp)
{
    int cur = vp->level;
    int level = cur-1;
    
    if (level >= 0) {
	vp->num_bound -= vp->bnd[level].size;
	vp->level = level;
	set_min_level(vp);
	DBG("%sPop_level: @%d, t=%s, decision=%s\r\n",
	    indent(level), level, bnd_state_name[vp->bnd[level].t],
	    format_lit(vp, vp->bnd[level].decision));
    }
    return level;
}

// push level, return the starting level
static int push_level(varp_t* vp)
{
    int cur = vp->level;
    int level = cur+1;
    
    if (level >= (int)dynvar_size(vp->bnd))
	resize_levels(vp, level);
    vp->bnd[level].offs = vp->bnd[cur].offs + vp->bnd[cur].size;
    vp->num_bound += vp->bnd[cur].size;
    vp->level = level;
    set_max_level(vp);

    DBG("%sPush_level: @%d, t=%s, decision=%s\r\n",
	indent(level), level, bnd_state_name[vp->bnd[level].t],
	format_lit(vp, vp->bnd[level].decision));
    return cur;
}

static void unbind_level(varp_t* vp, int level)
{
    bindings_t* bp = &vp->bnd[level];
    int size = bp->size;
    lit_t* bpv = bindings(vp, bp);
    int i;
    
    DBG_ORDER("%sUnbind_level @%d\r\n", indent(level), level);

    // unbind in bind order 
    for (i = size-1; i >= 0; i--) {
	lit_t xl = bpv[i];
	ASSERT(var_l(vp, xl)->bl == LIT_NONE);
	DBG_BCP("%sUnbind %s\r\n",indent(level),format_lit(vp,xl));
	// remember phase, but skip decision
	// (may have to check that bvp[0] really is a decision)
	// if ( i>0 ) var_l(vp, xl)->phase = 2|L_SIGN(xl);
	order_unbind(vp, xl);
	set_lev(vp, xl, -1, CLAUSE_NONE);
    }
    vp->bnd[level].size = 0;
}

static void ll_init(literal_t* lp, variable_t* var, bool_t neg)
{
    lp->wlist    = NULL;
    lp->xref     = NULL;
    lp->sref     = NULL;
}

static void var_init(varp_t* vp, variable_t* var, int ix)
{
    var->ix         = ix;
    var->bl         = LIT_NONE;
    clr_vv(vp, var);
    ll_init(&var->lit[LIT_POS], var, false);
    ll_init(&var->lit[LIT_NEG], var, true);
}

// return 1 if literal array a is equal to literal array b, return 0 otherwise
// LIT_MARK0
static int clause_is_equal(varp_t* vp, lit_t* a, lit_t* b, int size)
{
    int i;
    int all_marked = 1;

    // unordered compare
    for (i = 0; i < size; i++)  // mark all in A
	set_mark(vp, a[i], LIT_MARK0);
    for (i = 0; all_marked && (i < size); i++)
	all_marked = is_marked(vp, b[i], LIT_MARK0);
    for (i = 0; i < size; i++)  // mark all in A
	clr_mark(vp, a[i], LIT_MARK0);
    return all_marked;
}

// allocate / resize clause hash table
static int hashtab_grow(varp_t* vp)
{
    size_t size0 = dynvar_size(vp->hashtab);
    size_t size  = next_pow2(size0);
    int i;

    if (dynvar_resize(vp->hashtab, size) < 0)
	return -1;
    // move elements that rehash to the upper part
    for (i = 0; i < (int)size0; i++) {
	slist_iter_t iter;
	slist_iter_init(&iter, &vp->hashtab[i]);

	while(!slist_iter_eol(&iter)) {
	    hlink_t* hp = slist_iter_current(&iter);
	    int j = hp->hvalue & (size-1);  // hash with new size
	    if (i == j) // element stay
		slist_iter_next(&iter);
	    else { // element move to new location j=(i+2^r) (top half)
		slist_iter_remove(&iter);
		slist_insert_last(&vp->hashtab[j], hp);
	    }
	}
    }
    return 0;
}

static int hlink_insert(varp_t* vp, hlink_t* hp)
{
    int i;
    if (vp->hnum+1 >= dynvar_size(vp->hashtab)) {
	if (hashtab_grow(vp) < 0)
	    return -1;
    }
    i = hp->hvalue & (dynvar_size(vp->hashtab)-1);
    slist_insert_last(&vp->hashtab[i], hp);
    vp->hnum++;
    return 0;
}

static int hash_unlink(varp_t* vp, clause_t* cp)
{
    int i = cp->hvalue & (dynvar_size(vp->hashtab)-1);
    slist_iter_t iter;
    slist_iter_init(&iter, &vp->hashtab[i]);

    while(!slist_iter_eol(&iter)) {
	hlink_t* hp = slist_iter_current(&iter);    
	if (hp->cix == cp->cix) {
	    slist_iter_remove(&iter);
	    obj_free(&vp->hlink_allocator, hp);
	    return 0;
	}
	slist_iter_next(&iter);
    }
    DBG("clause %d not found in hash table\r\n", cp->cix);
    return -1;
}

static hlink_t* hlink_lookup(varp_t* vp,lit_t* lit,size_t size,uint32_t hvalue)
{
    size_t hsize = dynvar_size(vp->hashtab);
    if (hsize > 0) {
	int i = hvalue & (hsize-1);
	slist_iter_t iter;
	slist_iter_init(&iter, &vp->hashtab[i]);

	while(!slist_iter_eol(&iter)) {
	    hlink_t* hp = slist_iter_current(&iter); 
	    if (hp->hvalue == hvalue) {
		clause_t* cp = get_clause(vp, hp->cix);
		ASSERT(cp != NULL);
		if ((cp->size == size) && clause_is_equal(vp,lit,cp->lit,size))
		    return hp;
	    }
	    slist_iter_next(&iter);
	}
    }
    return NULL;
}

#ifdef USE_CLAUSE_SEGMENTS
// demo code to scan all clauses in a segment
static void scan_seg_clauses(varp_t* vp, clause_segment_t* seg)
{
    int i;
    uint8_t* ptr = seg->data;
    
    for (i = 0; i < (int)seg->nallocated; i++) {
	clause_t* cp;
	ptr = (uint8_t*) ALIGN(ptr, CLAUSE_ALIGNMENT);
	cp = (clause_t*) ptr;
	// do something to cp
	ptr += sizeof(clause_t) + sizeof(lit_t)*cp->size;
    }
}
#endif

#ifdef USE_CLAUSE_SEGMENTS
static clause_segment_t* new_clause_segment(varp_t* vp, int si,
					    size_t segment_size)
{
    clause_segment_t* seg;

    if (segment_size > MAX_CLAUSE_SEGMENT_SIZE)
	return NULL;

    if ((seg = VARP_ALLOC(sizeof(clause_segment_t)+segment_size)) != NULL) {
	seg->next = NULL;
	seg->nallocated = 0;
	seg->ndeleted = 0;
	seg->si = si;
	seg->size = segment_size;
	seg->ptr = seg->data;
	seg->end = seg->data + segment_size; // outside!
	vp->num_segs++;
	printf("num_segs = %ld\r\n", vp->num_segs);
    }
    return seg;
}
#endif

#ifdef USE_CLAUSE_SEGMENTS
static clause_t* clause_seg_alloc(varp_t* vp, int si, size_t size)
{
    size_t nbytes = sizeof(clause_t) + sizeof(lit_t)*size;    
    clause_segment_t* segp;
    clause_t* cp;
    uint8_t* ptr;

    if ((segp = vp->clauseseg[si]) == NULL)
	segp = vp->clauseseg[si] = new_clause_segment(vp, si, DEF_SEGMENT_SIZE);
    if (segp->ptr + nbytes + CLAUSE_ALIGNMENT > segp->end) {
	clause_segment_t* segp1;
	segp1 = new_clause_segment(vp, si, DEF_SEGMENT_SIZE);
	segp1->next = segp;
	vp->clauseseg[si] = segp1;
	segp = segp1;
    }
    ptr = (uint8_t*) ALIGN(segp->ptr, CLAUSE_ALIGNMENT);
    cp  = (clause_t*) ptr;
    cp->offset = ptr - segp->data;
    cp->dynamic = 0;
    segp->ptr = ptr + nbytes;
    segp->nallocated++;
    return cp;
}
#endif

static clause_t* clause_dyn_alloc(varp_t* vp, size_t size)
{
    size_t nbytes = sizeof(clause_t) + sizeof(lit_t)*size;
    clause_t* cp;
#if defined(__WIN32__) || defined(_WIN32)
    if ((cp = _aligned_malloc(nbytes, CLAUSE_ALIGNMENT)) == NULL) {
      return NULL;
    }
#else
    if (posix_memalign((void**)&cp, CLAUSE_ALIGNMENT, nbytes) != 0) {
	// fixme: maybe handler return value as errno...
	return NULL;
    }
#endif
    cp->dynamic = 1;
    cp->offset = 0;
    return cp;
}

static clause_t* clause_alloc(varp_t* vp, int si, size_t size)
{
    UNUSED(vp);
    clause_t* cp;

    if (size < 1)
	return NULL;

    if (size <= MAX_CLAUSE_LENGTH) {
#ifdef USE_CLAUSE_SEGMENTS
	cp = clause_seg_alloc(vp, si, size);
#else
	cp = clause_dyn_alloc(vp, size);
#endif
    }
    else
	cp = clause_dyn_alloc(vp, size);

    if ((((intptr_t)cp) & (CLAUSE_ALIGNMENT-1)) != 0) {
	printf("clause aligment error\n");
    }

    if (cp != NULL) {
	wlink_clear(&cp->wl[0]);
	wlink_clear(&cp->wl[1]);
	cp->size = size;
	cp->select = (size > 3) ? 3 : size-1;
	cp->dead = 0;
	cp->conflict = 0;
	cp->watched = 0;
	cp->unwatch = 0;
	cp->delete = 0;
    }
    return cp;
}

static void clause_free(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	cix_t cix = cp->cix;
	int si = GET_SI(cix);
	if ((si != ALPHA) && vp->opt.hash)
	    hash_unlink(vp, cp);
	set_clause(vp, cix, NULL);
	vp->cnum[si]--;
	if (cp->dynamic) {
#if defined(__WIN32__) || defined(_WIN32)
	    _aligned_free(cp);
#else
	    free(cp);
#endif	    
	}
	else {
	    clause_segment_t* segp = (clause_segment_t*)
		((uint8_t*)cp) - (cp->offset + sizeof(clause_segment_t));
	    cp->delete = 1;    // marked for deletion
	    segp->ndeleted++;
	    ASSERT(si == segp->si);
	    vp->cfree[si]++;
	    // if (ndeleted == nallocted) reset block
	    // if (clause was last allocated) back poinrt
	    // if (ndeleted > 0.5*nallocated) collect
	}
    }
}

static clause_t* clause_copy(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	clause_t* copy;
	if ((copy = clause_alloc(vp, GET_SI(cp->cix), cp->size)) == NULL)
	    return NULL;
	memcpy(copy->lit, cp->lit, cp->size*sizeof(lit_t));
	return copy;
    }
    return NULL;
}

// if clause is already installed return index to installed clause if success
// return CLAUSE_NONE otherwise

static cix_t clauseset_find(varp_t* vp, lit_t* lit, size_t size,
		     int si, uint32_t hvalue)
{
    int i;
    int n = (int)dynvec_size(vp->clauseset, si);
    for (i = 0; i < n; i++) {
	clause_t* cp = get_clause(vp, MAKE_CIX(si,i));
	if ((cp != NULL) &&
	    (cp->size == size) &&
	    (cp->hvalue == hvalue) &&
	    clause_is_equal(vp, lit, cp->lit, size)) {
	    return cp->cix;
	}
    }
    return CLAUSE_NONE;
}

cix_t clause_find(varp_t* vp, lit_t* lit, size_t size)
{
    uint32_t hvalue = literal_array_hash(vp, lit, size);

    if (vp->opt.hash) {
	hlink_t* hp;
	if ((hp = hlink_lookup(vp,lit,size,hvalue)) != NULL)
	    return hp->cix;
    }
    else {
	int si;
	DBG("warning slow clause_find in use\r\n");
	for (si = 0; si < NUM_CSET; si++) {
	    cix_t cix;
	    if ((cix = clauseset_find(vp,lit,size,si,hvalue)) != CLAUSE_NONE)
		return cix;
	}
    }
    return CLAUSE_NONE;
}

static int clause_hash_insert(varp_t* vp, clause_t* cp)
{
    hlink_t* hp;

    if ((hp = obj_alloc(&vp->hlink_allocator)) == NULL)
	return -1;
    hp->hvalue = cp->hvalue;
    hp->cix  = cp->cix;
    return hlink_insert(vp, hp);
}

// insert all clauses in a clauseset
static int clauseset_hash_insert(varp_t* vp, int si)
{
    int i;
    size_t n = dynvec_size(vp->clauseset, si);

    DBG("clauseset_hash_insert: si=%dm n=%ld\r\n", si, n);

    for (i = 0; i < (int)n; i++) {
	clause_t* cp = get_clause(vp, MAKE_CIX(si,i));
	if (cp != NULL) {
	    if (clause_hash_insert(vp, cp) < 0)
		return -1;
	}
    }
    return 0;
}

static cix_t clause_insert(varp_t* vp, int si, clause_t* cp, uint32_t hvalue)
{
    uint32_t ix = dynvec_size(vp->clauseset, si);
    cix_t cix = MAKE_CIX(si,ix);

    cp->cix    = cix;
    cp->stamp  = vp->counter[BCP_COUNTER];
    cp->hvalue = hvalue;

    if (dynvec_resize(vp->clauseset, si, ix+1) < 0)
	return CLAUSE_NONE;

    vp->cnum[si]++;
    set_clause(vp, cix, cp);
    if ((si != ALPHA) && vp->opt.hash) { // alphas are not hashed
	if (clause_hash_insert(vp, cp) < 0)
	    return CLAUSE_NONE;
    }
    return cix;
}

static int vif_get_size_t(ErlNifEnv* env,ERL_NIF_TERM arg, size_t* sp)
{
    ErlNifUInt64 value;

    if (!enif_get_uint64(env, arg, &value))
	return 0;
    *sp = value;
    return 1;
}

static int vif_get_si(ErlNifEnv* env, ERL_NIF_TERM arg, int* si)
{
    (void) env;
    int value;

    if (enif_get_int(env, arg, &value)) {
	if ((value >= NUM_CSET) || (value < 0))
	    return 0;
	*si = value;
    }
    else if (EQUAL_KEY(env, delta, arg))
	*si = DELTA;
    else if (EQUAL_KEY(env, gamma, arg))
	*si = GAMMA;
    else if (EQUAL_KEY(env, alpha, arg))
	*si = ALPHA;
    else if (EQUAL_KEY(env, beta, arg))
	*si = BETA;
    else
	return 0;
    return 1;
}

// get primitive lit value
static int vif_get_l(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, lit_t* l)
{
    int x;

    if (enif_is_true(env, arg))
	*l = LIT_TRUE;
    else if (enif_is_false(env, arg))
	*l = LIT_FALSE;
    else if (enif_get_int(env, arg, &x)) {
	if (x == 0)
	    return 0;
	else if (ABS(x) < (int)dynvar_size(vp->var_map))
	    *l = vindex_l(vp, x);
	else {
	    DBG("literal %d out of range\r\n", x);
	    return 0;
	}
    }
    else
	return 0;
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
    lit_t xl;
    if (!vif_get_l(env, vp, arg, &xl))
	return 0;
    *xp = resolve_lit(vp, xl);
    return 1;
}

static int vif_get_variable(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg,
			    variable_t** vpp)
{
    variable_t* var;
    lit_t xl;    
    if (!vif_get_v(env, vp, arg, &var))
	return 0;
    while((xl = var->bl) != LIT_NONE)
	var = var_l(vp, xl);
    *vpp = var;
    return 1;
}

static int vif_get_cix(ErlNifEnv* env,varp_t* vp,ERL_NIF_TERM term,cix_t* cixp)
{
    unsigned int cix;
    int ix, si;
    if (!enif_get_uint(env, term, &cix))
	return 0;
    si = GET_SI(cix);
    if ((ix = GET_IX(cix)) >= (int)dynvec_size(vp->clauseset,si))
	return 0;
    *cixp = cix;
    return 1;
}

// read a clause - list of literals
static int vif_get_lit_list(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM list,
		     int* lenp, lit_t* clause)
{
    if (clause == NULL) {
	unsigned int len;
	if (!enif_get_list_length(env, list, &len)) {
	    *lenp = -1;
	    return 0;
	}
	*lenp = len;
	return 1;
    }
    else {
	int i;
	int n = *lenp;
	int r = 1;
	STK_BEGIN(ERL_NIF_TERM, elem, n) {
	    if (!enif_get_list(env, list, lenp, elem)) {
		r = 0;
		STK_LEAVE(elem);
	    }
	    n = *lenp;
	    for (i = 0; i < n; i++) {
		if (!vif_get_lit(env, vp, elem[i], &clause[i])) {
		    r = 0;
		    STK_LEAVE(elem);
		}
	    }
	} STK_END(elem);
	return r;
    }
}

static ERL_NIF_TERM make_lit(ErlNifEnv* env, lit_t xl)
{
    return enif_make_int(env, export_l(xl));
}

// Read a list or tuple of literals into vp->tlit!
// return length in lenp
static int vif_load_tlit(ErlNifEnv* env,varp_t* vp,int* lenp,ERL_NIF_TERM arg)
{
    unsigned int n;
    int len;
    const ERL_NIF_TERM* elem;
    
    if (enif_get_list_length(env, arg, &n)) {
	dynvar_resize(vp->tlit, n);
	len = n;  // known length
	if (!vif_get_lit_list(env, vp, arg, &len, vp->tlit))
	    return 0;
	*lenp = len;
	return 1;
    }
    else if (enif_get_tuple(env, arg, &len, &elem)) {
	int i;
	dynvar_resize(vp->tlit, (size_t) len);
	for (i = 0; i < len; i++) {
	    if (!vif_get_lit(env, vp, elem[i], &vp->tlit[i]))
		return 0;
	}
	*lenp = len;
	return 1;
    }
    return 0;
}


// Read a list or tuple of literals into vp->ulit!
// return length in lenp
static int vif_load_ulit(ErlNifEnv* env,varp_t* vp,int* lenp,ERL_NIF_TERM arg)
{
    unsigned int n;
    int len;
    const ERL_NIF_TERM* elem;
    
    if (enif_get_list_length(env, arg, &n)) {
	dynvar_resize(vp->ulit, n);
	len = n;  // known length
	if (!vif_get_lit_list(env, vp, arg, &len, vp->ulit))
	    return 0;
	*lenp = len;
	return 1;
    }
    else if (enif_get_tuple(env, arg, &len, &elem)) {
	int i;
	dynvar_resize(vp->ulit, (size_t) len);
	for (i = 0; i < len; i++) {
	    if (!vif_get_lit(env, vp, elem[i], &vp->ulit[i]))
		return 0;
	}
	*lenp = len;
	return 1;
    }
    return 0;
}

// cleanup symbols elements but leave in place
static void symtab_slot_cleanup(dlist_t* list)
{
    dlist_iter_t iter;

    dlist_iter_init(&iter, list);
    while(!dlist_iter_end(&iter)) {
	symbol_t* sp = dlist_iter_current(&iter);
	VARP_FREE(sp->data);
	dynvar_clear(sp->lit);
	dlist_iter_next(&iter);
    }
}

static void cleanup(varp_t* vp)
{
    int si;
    int i;

    if (vp->symtab) {
	size_t size = dynvar_size(vp->symtab);
	for (i = 0; i < (int)size; i++)
	    symtab_slot_cleanup(&vp->symtab[i]);
	dynvar_clear(vp->symtab);
    }

    for (i = 1; i < (int)dynvar_size(vp->var_map); i++) {
	dynarray_destroy(vp, vp->var_map[i]->lit[0].xref);
	dynarray_destroy(vp, vp->var_map[i]->lit[1].xref);
	dynarray_destroy(vp, vp->var_map[i]->lit[0].sref);
	dynarray_destroy(vp, vp->var_map[i]->lit[1].sref);	
    }

    dynvar_clear(vp->var_map);
    dynvar_clear(vp->bnd_map);

    dynvar_clear(vp->lit_mark);
    dynvar_clear(vp->lit_value);
    vp->lit_overlay = NULL;

    dynvar_clear(vp->var_lev);

    dynvar_clear(vp->mark_stack);

    // turn off, avoid free all hash links clause_free
    dynvar_clear(vp->hashtab);
    vp->hnum = 0;
    vp->opt.hash = false; // avoid unlink in clause_free

    for (si = 0; si < NUM_CSET; si++) {
	clause_segment_t* seg;
	if (vp->clauseset[si] != NULL) {
	    clause_t** cm = vp->clauseset[si];
	    size_t n = dynvec_size(vp->clauseset,si);
	    int i;
	    for (i = 0; i < (int)n; i++) {
		clause_t* cp = cm[i];
		clause_free(vp, cp);
	    }
	}
	dynarray_clear(&vp->clauseset_dyn_[si]);
	vp->clauseset[si] = NULL;
	seg = vp->clauseseg[si];
	while(seg != NULL) {
	    clause_segment_t* seg_next = seg->next;
	    ASSERT(seg->nallocated == seg->ndeleted);
	    VARP_FREE(seg);
	    seg = seg_next;
	}
	vp->clauseseg[si] = NULL;
    }

    dynvar_clear(vp->bnd);
    dynvar_clear(vp->tlit);
    dynvar_clear(vp->ulit);

    allocator_cleanup(&vp->dyn_allocator);
    allocator_cleanup(&vp->var_allocator);
    allocator_cleanup(&vp->sym_allocator);
    allocator_cleanup(&vp->sub_allocator);
    allocator_cleanup(&vp->hlink_allocator);
}


static void default_config(varp_config_t* conf)
{
    conf->qtype = q_recursive;
    conf->xref  = false;
    conf->hash  = false;
    conf->vsids = true;
    conf->init_phase = I_TRUE;
    conf->use_phase = false;
    conf->all_used  = false;
    conf->vsize  = DEFAULT_MAP_SIZE;
    conf->csize  = DEFAULT_MAP_SIZE;
    conf->seed   = 0;
}

static int vif_config(ErlNifEnv* env,
		      const ERL_NIF_TERM key,
		      const ERL_NIF_TERM value,
		      varp_config_t* opt)
{
    if (EQUAL_KEY(env, size, key)) {
	if (EQUAL_KEY(env, default, value))
	    opt->vsize = DEFAULT_MAP_SIZE;
	else if (!vif_get_size_t(env, value, &opt->vsize))
	    return 0;
	else if ((opt->vsize < 2) || (opt->vsize > MAX_MAP_SIZE))
	    return 0;
    }
    else if (EQUAL_KEY(env, qtype, key) && EQUAL_KEY(env, fifo, value)) {
	opt->qtype = q_fifo;
    }
    else if (EQUAL_KEY(env, qtype, key) && EQUAL_KEY(env, lifo, value)) {
	opt->qtype = q_lifo;
    }
    else if (EQUAL_KEY(env, qtype, key) && EQUAL_KEY(env, recursive, value)) {
	opt->qtype = q_recursive;
    }
    else if (EQUAL_KEY(env, xref, key) && enif_is_true(env, value)) {
	opt->xref = true;
    }
    else if (EQUAL_KEY(env, xref, key) && enif_is_false(env, value)) {
	opt->xref = false;
    }
    else if (EQUAL_KEY(env, vsids, key) && enif_is_true(env, value)) {
	opt->vsids = true;
    }
    else if (EQUAL_KEY(env, vsids, key) && enif_is_false(env, value)) {
	opt->vsids = false;
    }
    else if (EQUAL_KEY(env, hash, key) && enif_is_true(env, value)) {
	opt->hash = true;
    }
    else if (EQUAL_KEY(env, hash, key) && enif_is_false(env, value)) {
	opt->hash = false;
    }
    else if (EQUAL_KEY(env, use_phase, key) && enif_is_true(env, value)) {
	opt->use_phase = true;
    }
    else if (EQUAL_KEY(env, use_phase, key) && enif_is_false(env, value)) {
	opt->use_phase = false;
    }
    else if (EQUAL_KEY(env, all_used, key) && enif_is_true(env, value)) {
	opt->all_used = true;
    }
    else if (EQUAL_KEY(env, all_used, key) && enif_is_false(env, value)) {
	opt->all_used = false;
    }
    else if (EQUAL_KEY(env, init_phase, key) && enif_is_true(env, value)) {
	opt->init_phase = I_TRUE;
    }
    else if (EQUAL_KEY(env, init_phase, key) && enif_is_false(env, value)) {
	opt->init_phase = I_FALSE;
    }
    else if (EQUAL_KEY(env, init_phase, key) && enif_is_undefined(env, value)) {
	opt->init_phase = I_UNDEF;
    }
    else if (EQUAL_KEY(env, seed, key)) {
	uint64_t seed;
	if (!enif_get_uint64(env, value, &seed))
	    return 0;
	opt->seed = seed;
    }     
    else
	return 0;
    return 1;
}

static int vif_new_config(ErlNifEnv* env,
			  const ERL_NIF_TERM key,
			  const ERL_NIF_TERM value,
			  varp_new_opt_t* opt)
{
    if (!vif_config(env, key, value, &opt->config))
	return 0;
    return 1;
}

static int vif_clone_config(ErlNifEnv* env,
			    const ERL_NIF_TERM key,
			    const ERL_NIF_TERM value,
			    varp_clone_opt_t* opt)
{
    if (!vif_config(env, key, value, &opt->config)) {
	if (EQUAL_KEY(env, level, key)) {
	    int level;
	    if (!enif_get_int(env, value, &level)) return 0;
	    if (level < -1) return 0;
	    opt->level = level;
	    return 0;
	}
	else if (EQUAL_KEY(env, set, key)) {
	    int si;
	    if (!vif_get_si(env, value, &si)) {
		int len = 4; // max 4 elements
		ERL_NIF_TERM set[4];
		int i;
		if (!enif_get_list(env, value, &len, set))
		    return 0;
		for (i = 0; i < (int) len; i++) {
		    if (!vif_get_si(env, set[i], &si))
			return 0;
		    opt->clauseset |= (1 << si);
		}
		return 1;
	    }
	    opt->clauseset |= (1 << si);
	    return 1;
	}
	else if (EQUAL_KEY(env, queue, key)) {
	    int queue;
	    if (!enif_get_boolean(env, value, &queue))
		return 0;
	    opt->queue = queue;
	    return 1;
	}
    }
    return 0;
}

static int parse_new_opts(ErlNifEnv* env,ERL_NIF_TERM map,varp_new_opt_t* opt)
{
    ERL_NIF_TERM key, value;
    ErlNifMapIterator iter;

    if (!enif_map_iterator_create(env, map, &iter, ERL_NIF_MAP_ITERATOR_FIRST))
	return 0;

    while (enif_map_iterator_get_pair(env, &iter, &key, &value)) {
	if (!vif_new_config(env, key, value, opt)) {
	    enif_map_iterator_destroy(env, &iter);
	    return 0;
	}
	enif_map_iterator_next(env, &iter);
    }
    enif_map_iterator_destroy(env, &iter);
    return 1;
}

// return hash slot for symbol given table size
static inline int symbol_slot(symbol_t* sp, size_t size)
{
    return sp->hvalue & (size-1);
}

static int symtab_grow(varp_t* vp)
{
    size_t size0 = dynvar_size(vp->symtab);
    size_t size  = next_pow2(size0);
    int i;
    int slot;
    
    DBG("symtab_grow\r\n");

    if (dynvar_resize(vp->symtab, size) < 0)
	return -1;
    for (i = 0; i < (int)(size-size0); i++)
	dlist_init(&vp->symtab[size0+i]);

    // move elements that rehash the lower part and move elements
    // that rehash to the upper part
    for (slot = 0; slot < (int)size0; slot++) {
	symbol_t* sp = dlist_first(&vp->symtab[slot]);
	while (sp != NULL) {
	    int new_slot = symbol_slot(sp, size);
	    DBG("move from %d to %d\r\n", slot, new_slot);
	    if (slot == new_slot) // element stay
		sp = dlist_next(sp);
	    else {
		symbol_t* tmp = dlist_next(sp);
		dlist_remove(&vp->symtab[slot], sp);
		dlist_insert_last(&vp->symtab[new_slot], sp);
		sp = tmp;
	    }
	}
    }
    return 0;
}

static symbol_t* symbol_lookup(varp_t* vp, ErlNifBinary* bp,
			       uint32_t hvalue, bool_t is_term,
			       int* slotp)
{
    size_t hsize = dynvar_size(vp->symtab);
    if (hsize > 0) {
	int slot = hvalue & (hsize-1);
	// fixme: use dlist_iter!
	symbol_t* sp = dlist_first(&vp->symtab[slot]);
	while (sp != NULL) {
	    if ((sp->hvalue == hvalue) &&
		(sp->size == bp->size) &&
		(sp->is_term == is_term) &&
		(memcmp(sp->data, bp->data, bp->size) == 0)) {
		if (slotp) *slotp = slot;
		return sp;
	    }
	    sp = dlist_next(sp);
	}
    }
    return NULL;
}

// create a new symbol
static symbol_t* symbol_create(varp_t* vp, lit_t* lit, size_t n,
			       ErlNifBinary* bp,
			       uint32_t hvalue,
			       bool_t is_term,
			       bool_t is_scalar)
{
    symbol_t* sp;

    if ((sp = obj_alloc(&vp->sym_allocator)) == NULL)
	return NULL;
    sp->is_term = is_term;
    sp->is_scalar = is_scalar;
    sp->hvalue = hvalue;
    if (dynvar_init(sp->lit, n) < 0)
	return NULL;
    if (dynvar_resize(sp->lit, n) < 0)
	return NULL;
    memcpy(sp->lit, lit, sizeof(lit_t)*n);
    // copy term or binary (add +1 for nil termination)
    sp->data = VARP_ALLOC(bp->size+1);
    memcpy(sp->data, bp->data, bp->size);
    sp->data[bp->size] = '\0';
    sp->size = bp->size;
    DBG("create symbol '%s'\r\n", symbol_strname(sp));
    return sp;
}

// copy symbol from other context into vp
static symbol_t* symbol_copy(varp_t* vp, symbol_t* sp0)
{
    symbol_t* sp;
    size_t n;
    int i;
    if ((sp = obj_alloc(&vp->sym_allocator)) == NULL)
	return NULL;
    sp->is_term = sp0->is_term;
    sp->is_scalar = sp0->is_scalar;
    sp->hvalue = sp0->hvalue;
    n = dynvar_size(sp0->lit);
    if (dynvar_init(sp->lit, n) < 0)
	return NULL;
    if (dynvar_resize(sp->lit, n) < 0)
	return NULL;    
    // copy literals into new context
    for (i = 0; i < (int)n; i++) {
	int x = export_l(sp0->lit[i]);
	sp->lit[i] = vindex_l(vp, x);
    }
    // copy term or binary
    sp->data = VARP_ALLOC(sp0->size+1);
    memcpy(sp->data, sp0->data, sp0->size);
    sp->data[sp0->size] = '\0';
    sp->size = sp0->size;
    return sp;
}

// insert the symbol into the symbol table
static int symbol_insert(varp_t* vp,symbol_t* sp)
{
    int slot;
    if (vp->snum+1 >= dynvar_size(vp->symtab)) // rehash
	symtab_grow(vp);
    slot = symbol_slot(sp, dynvar_size(vp->symtab));
    dlist_insert_last(&vp->symtab[slot], sp);
    vp->snum++;
    DBG("inserted symbol '%s' slot = %d\r\n", symbol_strname(sp), slot);
    return 0;
}

static int sref_add(varp_t* vp, lit_t l, symbol_t* sp, int pos)
{
    literal_t* lp = l2ll(vp, l);
    sref_t* sr;

    if (lp->sref == NULL)
	lp->sref = dynarray_empty(vp, sizeof(sref_t));
    if ((sr = dynarray_add(lp->sref)) == NULL)
	return -1;
    sr->sp = sp;
    sr->pos = pos;
    return 0;
}

static int sref_del(varp_t* vp, lit_t l, symbol_t* sp, int pos)
{
    literal_t* lp = l2ll(vp, l);
    size_t n = dynarray_size(lp->sref);

    if (n > 0) {
	int i;
	for (i = 0; i < (int)n; i++) {
	    sref_t* sr = dynarray_element(lp->sref, i);
	    if ((sr->sp == sp) && (sr->pos == pos)) {
		dynarray_delete(lp->sref, i);
		return 0;
	    }
	}
    }
    return -1;  // not found
}

// setup data-structure used by vp
static int setup(varp_t* vp, varp_config_t* config)
{
    size_t vsize, csize;
    int i;

    vp->opt = *config;

    vsize = MAX(1, vp->opt.vsize);
    csize = vp->opt.csize;

    // vp->nmarked = 0;
    // vp->marked_head = NULL;
    // vp->marked_tailp = &(vp->marked_head);

    if (dynvar_init(vp->var_map, vsize) < 0)
	goto error;
    DBG("var_map init\r\n");

    dynvar_resize(vp->var_map, 1); // set size = 1 (include first constant)

    DBG("var_map resize\r\n");

    if (dynvar_init(vp->bnd_map, vsize) < 0)
	goto error;

    cdlist_init(&vp->order_list);
    vp->top = NULL;

    if (dynvar_init(vp->lit_mark, 2*vsize) < 0)
	goto error;
    memset(vp->lit_mark, 0, 2*vsize*sizeof(markbits_t));

    if (dynvar_init(vp->lit_value, 2*vsize) < 0)
	goto error;
    vp->lit_overlay = (uint16_t*) vp->lit_value;

    if (dynvar_init(vp->var_lev, vsize) < 0)
	goto error;
    for (i = 0; i < (int)vsize; i++) {
	vp->var_lev[i].level = -1;	
	vp->var_lev[i].implication_clause = CLAUSE_NONE;
	vp->var_lev[i].phase = vp->opt.init_phase;
    }
    if (dynvar_init(vp->mark_stack, DYN_MARK_INIT) < 0)
	goto error;
    if (dynvar_init(vp->symtab, DYN_SYMTAB_INIT) < 0)
	goto error;
    dynvar_resize(vp->symtab, DYN_SYMTAB_INIT);
    for (i=0; i < DYN_SYMTAB_INIT; i++)
	dlist_init(&vp->symtab[i]);
    vp->snum  = 0;

    if (dynvar_init(vp->hashtab, DYN_HASHTAB_INIT) < 0)
	goto error;
    
    vp->hnum  = 0;

    dynvec_init(vp->clauseset,DELTA, csize);
    dynvec_init(vp->clauseset,GAMMA, 0);
    dynvec_init(vp->clauseset,BETA,  0);
    dynvec_init(vp->clauseset,ALPHA, 0);

    vp->num_segs = 0;
    for (i = 0; i < NUM_CSET; i++) {
	vp->clauseseg[i] = NULL;
	vp->cnum[i]  = 0;
	vp->coffs[i] = 0;
	vp->cfree[i] = 0;
	vp->cdead[i] = 0;
    }

    if (dynvar_init(vp->tlit, 0) < 0)
	goto error;
    if (dynvar_init(vp->ulit, 0) < 0)
	goto error;    

    if (dynvar_init(vp->unwatch, 0) < 0)
	goto error;

    if (allocator_init(&vp->dyn_allocator, sizeof(dynarray_t)) < 0)
	goto error;
    if (allocator_init(&vp->var_allocator, sizeof(variable_t)) < 0)
	goto error;
    if (allocator_init(&vp->sym_allocator, sizeof(symbol_t)) < 0)
	goto error;
    if (allocator_init(&vp->sub_allocator, sizeof(subscription_t)) < 0)
	goto error;
    if (allocator_init(&vp->hlink_allocator, sizeof(hlink_t)) < 0)
	goto error;

    dynvar_init(vp->q, 0);

    dynvar_init(vp->bnd, 0);
    resize_levels(vp, DYN_UNDO_INIT);

    vp->num_bound = 0;
    vp->report_index = 0;
    dlist_init(&vp->subs);
    vp->level = 0;

    // transient statistics
    vp->max_level = 0;
    vp->min_level = MAX_INT32;
    vp->max_bound = 0;

    vp->max_conflicting = MAX_CONFLICTING;
    memset(vp->counter, 0, sizeof(vp->counter));
    
    var_init(vp, &vp->constant, 0);
    vp->var_map[0] = &vp->constant;
    set_vv(vp, &vp->constant, I_TRUE);

    arc4_init(&vp->as);
    varp_set_seed(vp, vp->opt.seed);
    vp->asb = 0;
    vp->phase_shift = 8;

    vp->msg_env = enif_alloc_env();
    vp->caller_env = NULL;

    return 0;
error:
    if (vp)
	cleanup(vp);
    return -1;
}

static ERL_NIF_TERM varp_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM varc;
    varp_new_opt_t opt;

    default_config(&opt.config);

    if (!parse_new_opts(env, argv[0], &opt))
	return enif_make_badarg(env);

    if (!(vp = enif_alloc_resource(varp_res, sizeof(varp_t))))
	goto error;
    memset(vp, 0, sizeof(varp_t));

    if (setup(vp, &opt.config) < 0)
	goto error;

    varc = enif_make_resource(env,vp);
    enif_release_resource(vp);

    return varc;
error:
    if (vp)
	enif_release_resource(vp);
    return enif_make_badarg(env);
}

static ERL_NIF_TERM symbol_term(ErlNifEnv* env, symbol_t* sp)
{
    ERL_NIF_TERM term;
    if (sp->is_term)
	enif_binary_to_term(env,sp->data,sp->size,&term,0);
    else {
	uint8_t* data = enif_make_new_binary(env, sp->size, &term);
	memcpy(data, sp->data, sp->size);
    }
    return term;
}

// add n variables return index to the first added
static int add_variables(varp_t* vp, size_t n)
{
    size_t k = dynvar_size(vp->var_map);
    size_t m = k + n;
    size_t cap = dynvar_capacity(vp->var_map);
    int i, j;

    if (dynvar_resize(vp->var_map, m) < 0)
	return -1;
    // only update rest of variable/values when capacity grows
    if (dynvar_capacity(vp->var_map) > cap) {
	// printf("var capacity = %ld\n", dynvar_capacity(vp->var_map));
	cap = dynvar_capacity(vp->var_map);
	if (dynvar_set_capacity(vp->bnd_map, cap) < 0)
	    return -1;
	if (dynvar_set_capacity(vp->lit_mark, 2*cap) < 0)
	    return -1;
	memset(vp->lit_mark+2*k, 0, 2*(cap-k)*sizeof(markbits_t));

	if (dynvar_set_capacity(vp->lit_value, 2*cap) < 0)
	    return -1;
	vp->lit_overlay = (uint16_t*) vp->lit_value;

	if (dynvar_set_capacity(vp->var_lev, cap) < 0)
	    return -1;
	for (i = k; i < (int)cap; i++) {
	    vp->var_lev[i].level = -1;	
	    vp->var_lev[i].implication_clause = CLAUSE_NONE;
	    vp->var_lev[i].phase = vp->opt.init_phase;
	}
    }

    obj_pre_alloc(&vp->var_allocator, n);
    // printf("pre_alloc = %ld\n", n);
    // printf("obj_alloc = %ld .. %ld\n", k, m);
    for (j = (int)k; j < (int)m; j++) {
	variable_t* var;
	if ((var = obj_alloc(&vp->var_allocator)) == NULL)
	    return -1;
	cdlist_insert_last(&vp->order_list, var);
	var_init(vp, var, j);
	vp->var_map[j] = var;
	if (vp->top == NULL)
	    vp->top = var;
    }
    // cdlist_renumber(&vp->order_list);
    return (int)k;
}

// varc:add_variable(Vp:varc()[,Atom:boolean()[,Used:boolen()]) -> integer()
static ERL_NIF_TERM varp_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    int is_atom = 0;
    int is_used = 0;
    markbits_t mark = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (argc >= 2) {
	if (!enif_get_boolean(env, argv[1], &is_atom))
	    return enif_make_badarg(env);
    }
    if (argc >= 3) {
	if (!enif_get_boolean(env, argv[2], &is_used))
	    return enif_make_badarg(env);
    }    
    if (dynvar_size(vp->var_map) >= VLIMIT)
	return enif_raise_exception(env, ATOM(system_limit));

    if ((i = add_variables(vp, 1)) < 0) {
	return enif_raise_exception(env, ATOM(memory_limit));
    }
    if (is_atom) mark |= VAR_ATOM;
    if (is_used) mark |= VAR_USED;
    set_mark(vp, MAKE_LIT(i,0), mark);
    return enif_make_int(env, i);
}

// varc:add_variable(Vp:varc(),Num:integer()
//         [,Atom:boolean()[,Used:boolean()]]) ->
//  {First:integer(),Last:integer()}
static ERL_NIF_TERM varp_add_variables(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    unsigned n;
    int is_atom = 0;
    int is_used = 0;
    int j;
    markbits_t mark = 0;    

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &n) || (n < 1))
	return enif_make_badarg(env);
    if (argc >= 3) {
	if (!enif_get_boolean(env, argv[2], &is_atom))
	    return enif_make_badarg(env);
    }
    if (argc >= 4) {
	if (!enif_get_boolean(env, argv[3], &is_used))
	    return enif_make_badarg(env);
    }    
    if (dynvar_size(vp->var_map)+(n-1) >= VLIMIT)
	return enif_raise_exception(env, ATOM(system_limit));

    if ((i = add_variables(vp, n)) < 0) {
	return enif_raise_exception(env, ATOM(memory_limit));
    }
    if (is_atom) mark |= VAR_ATOM;
    if (is_used) mark |= VAR_USED;
    
    j = i;
    while(n--) {
	set_mark(vp, MAKE_LIT(j,0), mark);
	j++;
    }
    return enif_make_tuple2(env,
			    enif_make_int(env, i),
			    enif_make_int(env, j-1));
}

// note is_scalar => n=1
static ERL_NIF_TERM add_symbol(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM sym,
			       lit_t* lit, size_t n, bool_t is_scalar)
{
    ErlNifBinary bin;
    uint32_t hvalue;
    bool_t is_term = false;
    symbol_t* sp;
    int i;
    
    if (!enif_inspect_iolist_as_binary(env, sym, &bin)) {
	if (!enif_term_to_binary(env, sym, &bin))
	    return enif_make_badarg(env);
	is_term = true;
    }

    hvalue = djb_hash(bin.data, bin.size);

    if ((sp = symbol_lookup(vp, &bin, hvalue, is_term, NULL)) != NULL) {
	if (is_term) enif_release_binary(&bin);
	if (n != dynvar_size(sp->lit))
	    return enif_make_badarg(env);
	for (i = 0; i < (int)n; i++) {
	    if (sp->lit[i] != lit[i])
		return enif_make_badarg(env);
	}
	return enif_make_ok(env);  // ok they are the same
    }

    if ((sp = symbol_create(vp, lit, n, &bin, hvalue,
			    is_term, is_scalar)) == NULL)
	return enif_make_badarg(env);

    if (symbol_insert(vp, sp) < 0)
	return enif_make_badarg(env);

    for (i = 0; i < (int)n; i++) {
	if (sref_add(vp, lit[i], sp, i) < 0) {
	    return enif_raise_exception(env, ATOM(memory_limit));
	}
    }
    return enif_make_ok(env);
}

// varc:add_symbol(Vp:varc(),x0()|[x1..xn],Symbol::term()) -> ok
static ERL_NIF_TERM varp_add_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    lit_t l;
    int len;
    ERL_NIF_TERM r = enif_make_ok(env);
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (vif_get_lit_list(env, vp, argv[1], &len, NULL)) {
	STK_BEGIN(lit_t, lit, len) {
	    if (!vif_get_lit_list(env, vp, argv[1], &len, lit)) {
		r = enif_make_badarg(env);
		STK_LEAVE(lit);
	    }
	    r = add_symbol(env, vp, argv[2], lit, len, false);
	} STK_END(lit);
    }
    else if (vif_get_lit(env, vp, argv[1], &l)) {
	r = add_symbol(env, vp, argv[2], &l, 1, true);
    }
    else {
	r = enif_make_badarg(env);
    }
    return r;
}

static int symbol_delete(varp_t* vp, symbol_t* sp)
{
    int slot = symbol_slot(sp, dynvar_size(vp->symtab));
    int i;
    size_t n;
    
    dlist_remove(&vp->symtab[slot], sp);
    VARP_FREE(sp->data);

    n = dynvar_size(sp->lit);
    for (i = 0; i < (int)n; i++) {
	if (sref_del(vp, sp->lit[i], sp, i) < 0)
	    return -1;
    }
    dynvar_clear(sp->lit);
    obj_free(&vp->sym_allocator, sp);
    vp->snum--;
    return 0;
}

// varc:add_symbol(Vp:varc(), Symbol::term()) -> ok
static ERL_NIF_TERM varp_del_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ErlNifBinary bin;
    uint32_t hash;
    bool_t is_term = false;
    symbol_t* sp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (!enif_inspect_iolist_as_binary(env, argv[1], &bin)) {
	if (!enif_term_to_binary(env, argv[1], &bin))
	    return enif_make_badarg(env);
	is_term = true;
    }

    hash = djb_hash(bin.data, bin.size);

    sp = symbol_lookup(vp, &bin, hash, is_term, NULL);
    if (is_term) enif_release_binary(&bin);
    if (sp != NULL) {
	if (symbol_delete(vp, sp) < 0)
	    return enif_make_badarg(env);
	return enif_make_ok(env);
    }
    return enif_make_boolean(env, false);
}

// varc:find_symbol(Vp:varc(),symbol()) -> false | lit() | [lit()]
static ERL_NIF_TERM varp_find_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ErlNifBinary bin;
    uint32_t hash;
    bool_t is_term = false;
    symbol_t* sp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (!enif_inspect_iolist_as_binary(env, argv[1], &bin)) {
	if (!enif_term_to_binary(env, argv[1], &bin))
	    return enif_make_badarg(env);
	is_term = true;
    }

    hash = djb_hash(bin.data, bin.size);

    sp = symbol_lookup(vp, &bin, hash, is_term, NULL);
    if (is_term) enif_release_binary(&bin);
    if (sp != NULL) {
	ERL_NIF_TERM r = ATOM(undefined);
	if (sp->lit) {
	    size_t n = dynvar_size(sp->lit);
	    if ((n == 1) && sp->is_scalar)
		return enif_make_int(env, export_l(sp->lit[0]));
	    STK_BEGIN(ERL_NIF_TERM, element, n) {
		int i;
		for (i = 0; i < (int)n; i++)
		    element[i] = enif_make_int(env, export_l(sp->lit[i]));
		r = enif_make_list_from_array(env, element, n);
	    } STK_END0(element);
	}
	return r;
    }
    return enif_make_boolean(env, false);
}

// varc:first_symbol(Vp:varc()) -> symbol()|false
static ERL_NIF_TERM varp_first_symbol(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int slot;
    size_t n;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vp->snum == 0)
	return enif_make_boolean(env, false);
    slot = 0;
    n = dynvar_size(vp->symtab);
    while((slot < (int)n) && (dlist_length(&vp->symtab[slot]) == 0))
	slot++;
    if (slot >= (int)n)
	return enif_make_boolean(env, false);
    return symbol_term(env, dlist_first(&vp->symtab[slot]));
}

// varc:next_symbol(Vp:varc()|symbol()) -> symbol()|false
static ERL_NIF_TERM varp_next_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ErlNifBinary bin;
    uint32_t hash;
    bool_t is_term = false;
    symbol_t* sp;
    int slot;
    size_t n;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (!enif_inspect_iolist_as_binary(env, argv[1], &bin)) {
	if (!enif_term_to_binary(env, argv[1], &bin))
	    return enif_make_badarg(env);
	is_term = true;
    }

    hash = djb_hash(bin.data, bin.size);

    sp = symbol_lookup(vp, &bin, hash, is_term, &slot);
    if (is_term) enif_release_binary(&bin);
    if (sp != NULL) {
	if ((sp = dlist_next(sp)) == NULL) {
	    slot++;
	    n = dynvar_size(vp->symtab);

	    while((slot < (int)n) && (dlist_length(&vp->symtab[slot]) == 0))
		slot++;
	    if (slot >= (int)n)
		return enif_make_boolean(env, false);
	    sp = dlist_first(&vp->symtab[slot]);
	}
	return symbol_term(env, sp);
    }
    return enif_make_boolean(env, false);    
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
	return enif_raise_exception(env, ATOM(variable));

    if (EQUAL_KEY(env, implication, argv[2])) {
	varlev_t* vlp = &vp->var_lev[var->ix];
	return enif_make_tuple2(env,
				make_cix(env, vlp->implication_clause),
				enif_make_int(env, vlp->level));
    }
    if (EQUAL_KEY(env, implication_clause, argv[2])) {
	varlev_t* vlp = &vp->var_lev[var->ix];
	return make_cix(env, vlp->implication_clause);
    }
    if (EQUAL_KEY(env, level, argv[2])) {
	varlev_t* vlp = &vp->var_lev[var->ix];
	return enif_make_int(env, vlp->level);
    }
    if (EQUAL_KEY(env, phase, argv[2])) {
	switch(vp->var_lev[var->ix].phase) {
	case I_TRUE: return enif_make_int(env, 1);
	case I_FALSE: return enif_make_int(env, -1);
	default: return enif_make_undefined(env);
	}
    }
    if (EQUAL_KEY(env, is_atom, argv[2])) {
	lit_t xl = MAKE_LIT(var->ix, 0);
	return enif_make_boolean(env, is_marked(vp, xl, VAR_ATOM));
    }
    if (EQUAL_KEY(env, is_used, argv[2])) {
	lit_t xl = MAKE_LIT(var->ix, 0);	
	return enif_make_boolean(env, is_marked(vp, xl, VAR_USED));
    }
    if (EQUAL_KEY(env, degree, argv[2])) {
	if (vp->opt.xref)
	    return enif_make_uint(env,
				  dynarray_size(var->lit[0].xref)+
				  dynarray_size(var->lit[1].xref));
	else
	    return enif_make_undefined(env);
    }
    if (EQUAL_KEY(env, symbol, argv[2])) {
	literal_t* lp = &var->lit[LIT_POS];
	size_t n = dynarray_size(lp->sref);
	ERL_NIF_TERM list = enif_make_list(env, 0);
	int i;
	
	for (i = 0; i < (int)n; i++) {
	    sref_t* sr = dynarray_element(lp->sref, i);
	    symbol_t* sp = sr->sp;
	    ERL_NIF_TERM term = symbol_term(env, sp);
	    term = enif_make_tuple2(env, term, enif_make_int(env, sr->pos));
	    list = enif_make_list_cell(env, term, list);
	}
	
	lp = &var->lit[LIT_NEG];
	n = dynarray_size(lp->sref);
	
	for (i = 0; i < (int)n; i++) {
	    sref_t* sr = dynarray_element(lp->sref, i);
	    symbol_t* sp = sr->sp;
	    ERL_NIF_TERM term = symbol_term(env, sp);
	    term = enif_make_tuple2(env, term, enif_make_int(env, sr->pos));
	    list = enif_make_list_cell(env, term, list);
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
    lit_t xl;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xl))
	return enif_make_badarg(env);
    
    if (EQUAL_KEY(env, mark, argv[2])) {
	return enif_make_int(env, lit_markb(vp, xl));
    }
    if (EQUAL_KEY(env, inqueue, argv[2])) {
	int val = is_marked(vp, xl, LIT_MARKQ);
	return enif_make_boolean(env, val);
    }
    if (EQUAL_KEY(env, degree, argv[2])) {
	if (vp->opt.xref) {
	    literal_t* lp = l2ll(vp, xl);    
	    return enif_make_uint(env, dynarray_size(lp->xref));
	}
	else
	    return enif_make_undefined(env);
    }
    if (EQUAL_KEY(env, xref, argv[2])) {
	if (!vp->opt.xref)
	    return ATOM(undefined);
	else {
	    ERL_NIF_TERM r;
	    literal_t* lp = l2ll(vp, xl);	    
	    size_t n = dynarray_size(lp->xref);
	    cix_t* xptr = dynarray_element(lp->xref, 0);
	    int i;
	    STK_BEGIN(ERL_NIF_TERM, element, n) {
		for (i = 0; i < (int)n; i++) {
		    element[i] = enif_make_uint(env,xptr[i]);
		}
		r = enif_make_list_from_array(env, element, n);
	    } STK_END0(element);
	    return r;
	}
    }
    if (EQUAL_KEY(env, symbol, argv[2])) {
	ERL_NIF_TERM list = enif_make_list(env, 0);
	literal_t* lp = l2ll(vp, xl);    	
	size_t n = dynarray_size(lp->sref);
	int i;
	
	for (i = 0; i < (int)n; i++) {
	    sref_t* sr = dynarray_element(lp->sref, i);
	    symbol_t* sp = sr->sp;
	    ERL_NIF_TERM term = symbol_term(env, sp);
	    term = enif_make_tuple2(env, term, enif_make_int(env, sr->pos));
	    list = enif_make_list_cell(env, term, list);
	}
	return list;
    }
    return enif_make_badarg(env);
}

void dump_order(char* label, varp_t* vp)
{
    int vn = (int)dynvar_size(vp->var_map);
    variable_t* var;

    enif_fprintf(stdout, "dump_order %s: |order-list|=%d,#num=%d,#bound=%d,#subst=%d,#unbound=%d\r\n",
		 label, cdlist_length(&vp->order_list),
		 vn-1, get_num_bound(vp), vp->num_subst,
		 (vn-1) - get_num_bound(vp));
    var = cdlist_first(&vp->order_list);
    while(var != NULL) {
	char* nmark = (var == vp->top) ? "*" : "";
	enif_fprintf(stdout, "[o=%.2f]%s%s=%s ",
		     var->link.order,
		     nmark,
		     format_lit(vp, vindex_l(vp, phase_export(vp,var))),
		     format_ival(get_vv(vp,var))
	    );
	var = cdlist_next(var);
    }
    enif_fprintf(stdout, "\r\n");
}

#ifdef ASSERTIONS
static bool_t valid_order(varp_t* vp)
{
    variable_t* var;
    variable_t* prev;
    bool_t first_unbound = false;
    bool_t result = true;

    if (vp->top != NULL) {
	if (variable_is_bound(vp, vp->top)) {
	    if ((dynvar_size(vp->var_map)-1) !=  get_num_bound(vp))
		enif_fprintf(stdout, "TOP is BOUND\r\n");
	}
    }
    prev = NULL;
    var = cdlist_first(&vp->order_list);
    while(var != NULL) {
	if ((prev != NULL) && !cdlist_is_after(var, prev)) {
	    enif_fprintf(stdout, "variable %s @%d is not ordered correct!\r\n",
			 format_variable(var), var->level);
	    dump_order("valid", vp);
	    return false;
	}
	if (!first_unbound && !variable_is_bound(vp, var)) {
	    first_unbound = true;
	    if ((vp->top != NULL) &&
		(var != vp->top) &&
		!cdlist_is_after(var, vp->top)) {
		enif_fprintf(stdout, "top is set incorrect!\r\n");
		dump_order("valid", vp);
		result = false;
	    }
	}
	prev = var;
	var = cdlist_next(var);
    }
    return result;
}
#endif

#ifdef VALIDATE_MODEL
static bool_t valid_model(varp_t* vp)
{
    variable_t* var;

    var = cdlist_first(&vp->order_list);
    while(var != NULL) {
	if (!variable_is_bound(vp, var)) {
	    enif_fprintf(stdout, "variable %s @%d not bound!\r\n",
			 format_variable(var), var->level);
	    return false;
	}
	var = cdlist_next(var);
    }
    return true;
}
#endif


// get next unbound literal in current sort order
static ERL_NIF_TERM varp_next_unbound(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    varp_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (argc == 1) {
	if ((i = next_unbound(vp)) != 0) {
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "next_unbound=%s@%d\r\n",
			 format_lit(vp, vindex_l(vp, i)), vp->level);
#endif
	    return enif_make_int(env, i);
	}
#ifdef VALIDATE_MODEL
	ASSERT(valid_model(vp));
#endif
    }
    else if (argc == 2) {
	variable_t* var;
	int xi;
	if (enif_get_int(env, argv[1], &xi) && (xi == 0)) {
	    if (vp->top == NULL)
		return enif_make_boolean(env, false);
	    else
		return enif_make_int(env, vp->top->ix);
	}
	else if (!vif_get_variable(env, vp, argv[1], &var))
	    return enif_raise_exception(env, ATOM(variable));
	if ((i = next_unbound_after(vp, var)) != 0) {
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "next_unbound=%s\r\n",
			 format_lit(vp, vindex_l(vp, i)));
#endif
	    return enif_make_int(env, i);
	}
    }
    return enif_make_boolean(env, false);
}

typedef enum {
    ORDER_UNDEFINED = 0,
    ORDER_IDENTITY  = 1,    // "input" order
    ORDER_RANDOM    = 2,    // "random" order
    ORDER_DEGREE    = 3,    // order according to occurence
    ORDER_RANK      = 4,    // 1/n1+...1/nk where ni is size of clause i
    ORDER_ACTIVITY   = 5,    // order according to conflict activity
} order_type_t;

typedef enum {
    ORDER_ASCEND     = 0,    // ascending order
    ORDER_DESCEND    = 1,    // descending order
    ORDER_INTERLEAVE = 2     // interleve order
} order_dir_t;

#ifdef DEBUG_ORDER
static const char* order_name[] = {
    [ORDER_UNDEFINED] = "undefined",
    [ORDER_IDENTITY] = "identity",
    [ORDER_RANDOM] = "random",
    [ORDER_DEGREE] = "degree",
    [ORDER_RANK] = "rank",
    [ORDER_ACTIVITY] = "activity",
};

static const char order_dir_char[] = {
    [ORDER_ASCEND] = '+',
    [ORDER_DESCEND] = '-',
    [ORDER_INTERLEAVE] = '='
};

#endif

// setup current degree for all literals in pkey/nkey
static void order_degree(varp_t* vp, float* pkey, float* nkey, int vn)
{
    int i, si;
    int vmax = vn;
    int vmin = -vmax;

    memset(pkey, 0, sizeof(float)*vn);
    memset(nkey, 0, sizeof(float)*vn);

    for (si = 0; si < NUM_CSET; si++) {
	int n = (int)dynvec_size(vp->clauseset,si);
	clause_t** cm = vp->clauseset[si];
	for (i = 0; i < n; i++) {
	    clause_t* cp = cm[i];
	    if (cp != NULL) {
		int n = cp->size;
		if (n > 0) {
		    int j;
		    for (j = 0; j < n; j++) {
			int x = export_l(cp->lit[j]);
			if ((x > 0) && (x < vmax))
			    pkey[x] += 1.0;
			else if ((x < 0) && (x > vmin))
			    nkey[-x] += 1.0;
		    }
		}
	    }
	}
    }
}

// scan through all variables and calculate the "rank"
// foreach literal calculate Rj = Sum(1/Ni) where ni is the
// size of the clause that the literal Lj is a member
static void order_rank(varp_t* vp, float* pkey, float* nkey, int vn)
{
    int i, si;
    int vmax = vn;
    int vmin = -vmax;

    memset(pkey, 0, sizeof(float)*vn);
    memset(nkey, 0, sizeof(float)*vn);

    for (si = 0; si < NUM_CSET; si++) {
	int n = (int)dynvec_size(vp->clauseset,si);
	clause_t** cm = vp->clauseset[si];
	for (i = 0; i < n; i++) {
	    clause_t* cp = cm[i];
	    if (cp != NULL) {
		int n = cp->size;
		if (n > 0) {
		    int j;
		    float r = 1/(float)n;
		    for (j = 0; j < n; j++) {
			int x = export_l(cp->lit[j]);
			if ((x > 0) && (x < vmax))
			    pkey[x] += r;
			else if ((x < 0) && (x > vmin))
			    nkey[-x] += r;
		    }
		}
	    }
	}
    }
}

static void order_identity(varp_t* vp, float* pkey, float* nkey, int vn)
{
    UNUSED(vp);
    int i;

    pkey[0] = nkey[0] = 0.0;
    for (i = 1; i < vn; i++) {
	pkey[i] = (float) i + 0.1;  // make the positive side "win"
	nkey[i] = (float) i;
    }
}

static void order_random(varp_t* vp, float* pkey, float* nkey, int vn)
{
    int i;
    pkey[0] = nkey[0] = 0.0;
    for (i = 1; i < vn; i++) {
	float v1 = arc4_random_uniform(&vp->as, 0x7fffff) / (float)0x7fffff;
	float v2 = arc4_random_uniform(&vp->as, 0x7fffff) / (float)0x7fffff;
	pkey[i] = v1;
	nkey[i] = v2;
    }
}

static void order_undefined(varp_t* vp, float* pkey, float* nkey, int vn)
{
    UNUSED(vp);
    memset(pkey, 0, sizeof(float)*vn);
    memset(nkey, 0, sizeof(float)*vn);
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
#elif defined(__WIN32__) || defined(_WIN32)
#define QSORT(base,nmemb,size,compar,arg) \
    qsort_s((base),(nmemb),(size),(compar),(arg))
#define QSORT_ARGS(a,b,arg) (arg, a, b)
#elif defined(__APPLE__)
#define QSORT(base,nmemb,size,compar,arg) \
    qsort_r((base),(nmemb),(size),(arg),(compar))
#define QSORT_ARGS(a,b,arg) (arg, a, b)
#endif

typedef struct _sort_param_t
{
    float* pkey[2];
    float* nkey[2];
    int* sort_key;
} sort_param_t;

static int cmpk(sort_param_t* kp, int ai, int bi, int k)
{
    float a = MAX(kp->pkey[k][ai],kp->nkey[k][ai]);
    float b = MAX(kp->pkey[k][bi],kp->nkey[k][bi]);
    if (a < b) return -1;
    else if (a > b) return 1;
    return 0;
}

static int cmp_keys QSORT_ARGS(const void* a, const void* b,void* arg)
{
    sort_param_t* kp = (sort_param_t*) arg;
    int k1 = kp->sort_key[0];
    int k2 = kp->sort_key[1];
    int ai = *((int*)a);
    int bi = *((int*)b);
    int r = 0;

    // k1=0 means key[k1] is undefined, k2=0 means key[k2] is undefined
    if (k1 > 0) {
	if ((r = cmpk(kp,ai,bi,k1-1)) != 0)
	    return r;
    }
    else if (k1 < 0) {
	if ((r = cmpk(kp,bi,ai,(-k1)-1)) != 0)
	    return r;
    }
    if (k2 > 0)
	r = cmpk(kp,ai,bi,k2-1);
    else if (k2 < 0)
	r = cmpk(kp,bi,ai,(-k2)-1);
    return r;
}

static int vif_get_order(ErlNifEnv* env, ERL_NIF_TERM arg,
			 order_type_t* orderp, order_dir_t* dirp)
{
    if (enif_is_undefined(env, arg)) {
	*orderp = ORDER_UNDEFINED;
	*dirp   = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, identity, arg)) {
	*orderp = ORDER_IDENTITY;
	*dirp   = ORDER_ASCEND;  // NOTE the default!
	return 1;
    }
    if (EQUAL_KEY(env, p_identity, arg)) {
	*orderp = ORDER_IDENTITY;
	*dirp = ORDER_ASCEND;
	return 1;
    }
    if (EQUAL_KEY(env, n_identity, arg)) {
	*orderp = ORDER_IDENTITY;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, e_identity, arg)) {
	*orderp = ORDER_IDENTITY;
	*dirp = ORDER_INTERLEAVE;
	return 1;
    }
    if (EQUAL_KEY(env, random, arg)) {
	*orderp = ORDER_RANDOM;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, p_random, arg)) {
	*orderp = ORDER_RANDOM;
	*dirp = ORDER_ASCEND;
	return 1;
    }
    if (EQUAL_KEY(env, n_random, arg)) {
	*orderp = ORDER_RANDOM;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, e_random, arg)) {
	*orderp = ORDER_RANDOM;
	*dirp = ORDER_INTERLEAVE;
	return 1;
    }
    if (EQUAL_KEY(env, degree, arg)) {
	*orderp = ORDER_DEGREE;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, p_degree, arg)) {
	*orderp = ORDER_DEGREE;
	*dirp = ORDER_ASCEND;
	return 1;
    }
    if (EQUAL_KEY(env, n_degree, arg)) {
	*orderp = ORDER_DEGREE;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, e_degree, arg)) {
	*orderp = ORDER_DEGREE;
	*dirp = ORDER_INTERLEAVE;
	return 1;
    }
    if (EQUAL_KEY(env, rank, arg)) {
	*orderp = ORDER_RANK;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, p_rank, arg)) {
	*orderp = ORDER_RANK;
	*dirp = ORDER_ASCEND;
	return 1;
    }
    if (EQUAL_KEY(env, n_rank, arg)) {
	*orderp = ORDER_RANK;
	*dirp = ORDER_DESCEND;
	return 1;
    }
    if (EQUAL_KEY(env, e_rank, arg)) {
	*orderp = ORDER_RANK;
	*dirp = ORDER_INTERLEAVE;
	return 1;
    }
    return 0;
}

static ERL_NIF_TERM varp_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    uint64_t arg = 0;
    int i, m, n;
    order_type_t order[2];
    order_dir_t dir[2];
    int r = 0;

    order[0] = order[1] = ORDER_UNDEFINED;
    dir[0] = dir[1] = ORDER_DESCEND;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!vif_get_order(env, argv[1], &order[0], &dir[0]))
	return enif_make_badarg(env);
    if (argc == 3) { // (key1,key2)  OR (key,arg)
	if (!vif_get_order(env, argv[2], &order[1], &dir[1])) {
	    if (!enif_get_uint64(env, argv[2], &arg))
		return enif_make_badarg(env);
	}
    }
    else if (argc == 4) { // (key1,key2,arg)
	if (!vif_get_order(env, argv[2], &order[1], &dir[1]))
	    return enif_make_badarg(env);
	if (!enif_get_uint64(env, argv[3], &arg))
	    return enif_make_badarg(env);
    }
    if (vp->level != 0)
	return enif_raise_exception(env, ATOM(level));

    if ((order[0] == ORDER_RANDOM) || (order[1] == ORDER_RANDOM)) {
	varp_set_seed(vp, arg);
    }
    // order undefined,x  ==  x
    if (order[0] == ORDER_UNDEFINED) {
	order[0] = order[1];
	dir[0]   = dir[1];
	order[1] = ORDER_UNDEFINED;
	dir[1]   = ORDER_DESCEND;
    }
    // order x,x == x
    if (order[0] == order[1]) {
	order[1] = ORDER_UNDEFINED;
	dir[1]   = ORDER_DESCEND;
    }

    n = (int)dynvar_size(vp->var_map);

    STK_BEGIN(float, nkey1, n) {
    STK_BEGIN(float, nkey2, n) {
    STK_BEGIN(float, pkey1, n) {
    STK_BEGIN(float, pkey2, n) {
    STK_BEGIN(int, sort_map, n) {
	float* nkey[2];
	float* pkey[2];
	int sort_key[2]; // sort order -1,-2,1,2 (0=not used)

	nkey[0] = nkey1; nkey[1] = nkey2;
	pkey[0] = pkey1; pkey[1] = pkey2;

	DBG_ORDER("order[0] = %c%s, order[1]=%c%s\r\n",
		  order_dir_char[dir[0]], order_name[order[0]],
		  order_dir_char[dir[1]], order_name[order[1]]);
	       
	for (i = 1; i < 3; i++) {
	    int k = i;
	    switch(order[i-1]) {
	    case ORDER_UNDEFINED:
		order_undefined(vp, pkey[k-1], nkey[k-1], n);
		k = 0; // NOTE k=0!
		break;
	    case ORDER_IDENTITY:
		order_identity(vp, pkey[k-1], nkey[k-1], n);
		break;
	    case ORDER_RANDOM:
		order_random(vp, pkey[k-1], nkey[k-1], n);
		break;
	    case ORDER_DEGREE:
		order_degree(vp, pkey[k-1], nkey[k-1], n);
		break;
	    case ORDER_RANK:
		order_rank(vp, pkey[k-1], nkey[k-1], n);
		break;
	    default:
		r = -1;
		STK_LEAVE(sort_map);
	    }
	    if (dir[i-1] == ORDER_DESCEND)
		k = -k;
	    sort_key[i-1] = k;
	}

	// install unbound variables
	m = 0;
	for (i = 1; i < n; i++) {
	    if (!variable_is_bound(vp, vp->var_map[i]))
		sort_map[m++] = i;
	}

	cdlist_init(&vp->order_list);
	vp->top = NULL;   // make sure we do not point on moved variables

	// sort unbound variables according to sort_keys
	if (m > 0) {
	    int i;
	    int k1, k2;
	    sort_param_t kp;

	    kp.pkey[0] = pkey[0];
	    kp.pkey[1] = pkey[1];
	    kp.nkey[0] = nkey[0];
	    kp.nkey[1] = nkey[1];
	    kp.sort_key = sort_key;

	    QSORT(sort_map, m, sizeof(int), cmp_keys, &kp);
	    // setup variable phases & order
	    k1 = sort_key[0];
	    k2 = sort_key[1];
	    
	    for (i = 0; i < m; i++) {
		int j = sort_map[i];
		variable_t* var = vp->var_map[j];
		float r = 0.0;
		// select positive or negative literal
		if (k1 > 0)
		    r = pkey[k1-1][j] - nkey[k1-1][j];
		else if (k1 < 0)
		    r = pkey[-k1-1][j] - nkey[-k1-1][j];
		if ((k2 != 0) && (fabs(r) < EPSILON)) {
		    if (k2 > 0)
			r = pkey[k2-1][j] - nkey[k2-1][j];
		    else /* if (k2 < 0) */
			r = pkey[-k2-1][j] - nkey[-k2-1][j];
		}
		vp->var_lev[var->ix].phase = (r >= 0.0) ? I_TRUE : I_FALSE;
		dlist_insert_last(&vp->order_list, var);
	    }
#if defined(DEBUG_ORDER)
	    dump_order("order_sort", vp);
#endif
	}
    } STK_END(sort_map);
    } STK_END0(pkey2);
    } STK_END0(pkey1);
    } STK_END0(nkey2);
    } STK_END0(nkey1);
    if (r < 0)
	return enif_make_badarg(env);
    cdlist_renumber(&vp->order_list);
    setup_top(vp);
    ASSERT(valid_order(vp));
    return enif_make_ok(env);
}

static ERL_NIF_TERM varp_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int len;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_raise_exception(env, ATOM(level));

    // vif_load_tlit?
    if (vif_get_lit_list(env, vp, argv[1], &len, NULL)) {
	ERL_NIF_TERM r = enif_make_ok(env);
	STK_BEGIN(lit_t, lit, len) {
	    int i;
	    if (!vif_get_lit_list(env, vp, argv[1], &len, lit)) {
		r = enif_make_badarg(env);
		STK_LEAVE(lit);
	    }
	    // insert all (reversed) first, will produce the correct order!
	    for (i = len-1; i >= 0; i--) {
		variable_t* var = var_l(vp, lit[i]);
		if (!cdlist_is_first(&vp->order_list, var)) {
		    dlist_remove(&vp->order_list, var);
		    dlist_insert_first(&vp->order_list, var);
		}
	    }
	} STK_END(lit);
	cdlist_renumber(&vp->order_list);
	setup_top(vp);
	ASSERT(valid_order(vp));
	return r;
    }
    return enif_make_badarg(env);
}

static ERL_NIF_TERM varp_order_last(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int len;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_raise_exception(env, ATOM(level));

    if (vif_get_lit_list(env, vp, argv[1], &len, NULL)) {
	ERL_NIF_TERM r = enif_make_ok(env);
	STK_BEGIN(lit_t, lit, len) {
	    int i;
	    if (!vif_get_lit_list(env, vp, argv[1], &len, lit)) {
		r = enif_make_badarg(env);
		STK_LEAVE(lit);
	    }
	    for (i = 0; i < (int)len; i++) {
		variable_t* var = var_l(vp, lit[i]);
		if (!cdlist_is_last(&vp->order_list, var)) {
		    dlist_remove(&vp->order_list, var);
		    dlist_insert_last(&vp->order_list, var);
		}
	    }
	} STK_END(lit);
	cdlist_renumber(&vp->order_list);
	setup_top(vp);
	ASSERT(valid_order(vp));
	return r;
    }
    return enif_make_badarg(env);
}

static ERL_NIF_TERM varp_level(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    return enif_make_int(env, vp->level);
}

//
// value(Vp,X) -> true|false|undefined.
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
	return enif_raise_exception(env, ATOM(literal));
    switch(get_value(vp, x)) {
    case I_TRUE:  return enif_make_boolean(env, true);
    case I_FALSE: return enif_make_boolean(env, false);
    case I_UNDEF: return enif_make_undefined(env);
    case I_BOUND: return enif_make_undefined(env);
    default: return enif_make_badarg(env);
    }
}



//
// bound(Vct,X) -> true|false|Y|undefined.
// like value(Vct,X) but also return bound variable
//
static ERL_NIF_TERM varp_bound(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xl;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_l(env, vp, argv[1], &xl))
	return enif_raise_exception(env, ATOM(literal));
    switch(get_value(vp, xl)) {
    case I_TRUE:  return enif_make_boolean(env, true);
    case I_FALSE: return enif_make_boolean(env, false);
    case I_UNDEF: return enif_make_undefined(env);
    case I_BOUND: return make_lit(env, resolve_lit(vp, xl));
    default: return enif_make_badarg(env);
    }
}


static ERL_NIF_TERM varp_implication_clause(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_raise_exception(env, ATOM(literal));
    return make_cix(env, vp->var_lev[INDEX(xp)].implication_clause);
}

static ERL_NIF_TERM varp_implication_level(ErlNifEnv* env, int argc,
					   const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;    
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_raise_exception(env, ATOM(literal));
    return make_cix(env, vp->var_lev[INDEX(xp)].level);    
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
	return enif_raise_exception(env, ATOM(variable));
    return enif_make_boolean(env, !is_constant_l(vp, xp));
}

// Get conflicting clause index
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
	return enif_raise_exception(env, ATOM(variable));
    return enif_make_boolean(env, variable_is_bound(vp, var));
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
	return enif_raise_exception(env, ATOM(literal));
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_raise_exception(env, ATOM(literal));
    return enif_make_boolean(env, (xp == yp));
}

static ERL_NIF_TERM varp_is_used(ErlNifEnv* env, int argc,
				 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    lit_t xl;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_variable(env, vp, argv[1], &var))
	return enif_raise_exception(env, ATOM(variable));
    xl = MAKE_LIT(var->ix, 0);
    if (argc == 2) {
	return enif_make_boolean(env, is_marked(vp, xl, VAR_USED));
    }
    else {
	int was_used, use;
	if (!enif_get_boolean(env, argv[2], &use))
	    return enif_make_badarg(env);
	was_used = is_marked(vp, xl, VAR_USED);
	if (use && !was_used) {
	    set_mark(vp, xl, VAR_USED);
	    order_move_top(vp, var);
	}
	else if (!use && was_used) {
	    clr_mark(vp, xl, VAR_USED);
	    order_remove(vp, var);
	}
	return enif_make_boolean(env, was_used);
    }
}

static ERL_NIF_TERM varp_is_atom(ErlNifEnv* env, int argc,
				 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    lit_t xl;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xl))
	return enif_raise_exception(env, ATOM(literal));
    if (argc == 2) {
	return enif_make_boolean(env, lit_is_atom(vp, xl));
    }
    else {
	int was_atom;
	int atom;
	if (!enif_get_boolean(env, argv[2], &atom))
	    return enif_make_badarg(env);
	was_atom = lit_is_atom(vp, xl);
	if (atom)
	    set_mark(vp, L_VAR(xl), VAR_ATOM);
	else
	    clr_mark(vp, L_VAR(xl), VAR_ATOM);
	return enif_make_boolean(env, was_atom);
    }
}

static int bind_lit(varp_t* vp, lit_t xp, ival_t val)
{
    ival_t v;
    if ((v = get_value(vp, xp)) != I_UNDEF) {
	if (v != val)
	    return 0;
	return 1;
    }
    put_l(vp, xp, val, CLAUSE_NONE, vp->level);
    return 1;
}

static int decide_lit(varp_t* vp, lit_t xp, ival_t val)
{
    int level;
    ival_t v;

    if ((v = get_value(vp, xp)) != I_UNDEF) {
	if (v != val)
	    return 0;
	return 1;
    }
    if ((level=vp->level) > 0) {
	COUNT(vp, DECISION_COUNTER);
	vp->bnd[level].decision = xp;
	vp->bnd[level].value = val;
	vp->bnd[level].t = uSET;
    }
    put_l(vp, xp, val, CLAUSE_NONE, level);
    return 1;
}

static ERL_NIF_TERM varp_decide(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xl;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);    
    if (!vif_get_lit(env, vp, argv[1], &xl))
	return enif_raise_exception(env, ATOM(literal));
    if (!decide_lit(vp, xl, decide_phase(vp, xl)))
	return enif_make_boolean(env, false);
    return enif_make_boolean(env, true);
}

static ERL_NIF_TERM varp_bind(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_raise_exception(env, ATOM(literal));
    if (!bind_lit(vp, xp, I_TRUE))
	return enif_make_boolean(env, false);
    return enif_make_boolean(env, true);
}

// check if we have a hole at the end
static int clauseset_plug_hole(varp_t* vp, int si, int ix)
{
    clause_t** cm = vp->clauseset[si];
    int h = 0;
    size_t n = dynvec_size(vp->clauseset, si);

    // must be the last index and be cleared
    if ((ix+1 == (int)n) && (cm[ix] == NULL)) {
	h++;
	while(ix && (cm[ix-1] == NULL)) {
	    h++;
	    ix--;
	}
	dynvec_resize(vp->clauseset, si, ix);
    }
    return h;
}

// check if (dp - l) is a sub-clause of cp (all literals except l are marked)
// constats (level=0) are ignored, fixme mark all level 0 literals!?
static bool_t is_clause_marked(varp_t* vp, clause_t* dp, lit_t l)
{
    int i;

    for (i = 0; i < (int)dp->size; i++) {
	lit_t li = dp->lit[i];
	if (li != l) {
	    // variable_t* var = var_l(vp, li);
	    if (vp->var_lev[INDEX(li)].level > 0) {
		if (!is_marked(vp, li, LIT_MARK1))
		    return false;
	    }
	}
    }
    return true;
}

static int rec_clause_mark(varp_t* vp, clause_t* dp, lit_t u, int depth)
{
    int i;
    int all_marked = true;
    size_t size = dp->size;

    DBG1("%srec_clause_mark: %s ", indent(depth), format_lit(vp, u));
    print_sym_array_nl(vp, dp->lit, dp->size);
    
    for (i = 0; (i < (int)size) /* && all_marked */; i++) {
	lit_t xl = dp->lit[i];
	if (xl != u) {  // skip unit literal
	    cix_t  cix;
	    varlev_t* vlp = &vp->var_lev[INDEX(xl)];
	    // variable_t* var = var_l(vp, xl);
	    lit_t nxl = neg_l(xl);

	    DBG1("%slit[i]: %s\r\n", indent(depth+1), format_lit(vp, xl));

	    if (vlp->level == 0)
		DBG1("%s%s ATOM\r\n", indent(depth+1), format_lit(vp, xl));
	    else if ((cix=vlp->implication_clause) == CLAUSE_NONE)
		DBG1("%s%s DECISION\r\n", indent(depth+1), format_lit(vp, xl));
	    else if (is_marked(vp, xl, LIT_MARK1))
		DBG1("%s%s MARKED\r\n", indent(depth+1), format_lit(vp, xl));
	    else {
		clause_t* dp1 = get_clause(vp, cix);
		if (rec_clause_mark(vp, dp1, nxl, depth+1)) {
		    set_mark(vp, xl, LIT_MARK1);
		    DBG1("%smark: %s\r\n", indent(depth+1), format_lit(vp, xl));
		    COUNT(vp, MARK_COUNTER);
		}
		else {
		    // terminate early?
		    // all_marked = false;
		    return 0;
		}
	    }
	}
    }
    return all_marked;
}

// Minimize a clause wrt implication clauses as subclauses
static ERL_NIF_TERM varp_minimize(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t  cix;
    clause_t* cp;
    int i,n;
    minimize_t method = m_none;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);
    if (argc > 2) {
	if (EQUAL_KEY(env, none, argv[2]))
	    method = m_none;
	else if (EQUAL_KEY(env, local, argv[2]))
	    method = m_local;
	else if (EQUAL_KEY(env, global, argv[2]))
	    method = m_global;
	else if (EQUAL_KEY(env, recursive, argv[2]))
	    method = m_recursive;
	else
	    return enif_make_badarg(env);
    }
    if ((cp = get_clause(vp, cix)) == NULL)
	return enif_make_badarg(env);
    if (GET_SI(cix) != ALPHA)
	return enif_make_badarg(env);

    if ((n = (int)cp->size) == 1)
	return enif_make_int(env, 1);
    if (method == m_none)  // do nothing
	return enif_make_int(env, n);
    
    dynvar_resize(vp->tlit, 0);

    for (i = 0; i < n; i++)
	set_mark(vp, cp->lit[i], LIT_MARK1);
    vp->counter[MARK_COUNTER] += n;

    switch(method) {
    case m_local:
	break;
    case m_global:
	// forward version
	for (i = 1; i < vp->level; i++) {
	    lit_t* bpv = bindings_at(vp, i);
	    int bsz = vp->bnd[i].size;
	    int j;
	    for (j = 0; j < bsz; j++) {
		lit_t xl = bpv[j];
		varlev_t* vlp = &vp->var_lev[INDEX(xl)];
		if ((cix = vlp->implication_clause) != CLAUSE_NONE) {
		    // lit_t xl = lit_vv(vp, var);
		    lit_t nxl = neg_l(xl);
		    if (!is_marked(vp, nxl, LIT_MARK1)) {
			clause_t* dp = get_clause(vp, cix);
			if (is_clause_marked(vp, dp, xl)) {
			    set_mark(vp, nxl, LIT_MARK1);
			    COUNT(vp, MARK_COUNTER);
			}
		    }
		}
	    }
	}
	break;
    case m_recursive:
	for (i = 1; i < n; i++) {
	    lit_t xl = cp->lit[i];
	    // variable_t* var = var_l(vp, xl);
	    if ((cix = vp->var_lev[INDEX(xl)].implication_clause) !=
		CLAUSE_NONE) {
		clause_t* dp = get_clause(vp, cix);
		rec_clause_mark(vp, dp, neg_l(xl), 0);
	    }
	}
	break;
    default:
	break;
    }

    // assume UIP is in position 0
    dynvar_append(vp->tlit, &cp->lit[0]);
    
    // keep all decisions and literals not "marked"
    for (i = 1; i < n; i++) {
	lit_t li = cp->lit[i];
	// variable_t* var = var_l(vp, li);
	if ((cix = vp->var_lev[INDEX(li)].implication_clause) == CLAUSE_NONE) {
	    dynvar_append(vp->tlit, &li);
	}
	else {
	    clause_t* dp = get_clause(vp, cix);
	    if (!is_clause_marked(vp, dp, neg_l(li)))
		dynvar_append(vp->tlit, &li);
	}
    }
    ASSERT(dynvar_size(vp->tlit) > 0);

    // clear marks
    for (i = 0; i < n; i++) {
	clr_mark(vp, cp->lit[i], LIT_MARK1);
    }
    if ((method == m_recursive) || (method == m_global)) {
	for (i = 1; i < vp->level; i++) {
	    lit_t* bpv = bindings_at(vp, i);
	    int bsz = vp->bnd[i].size;
	    int j;
	    for (j = 0; j < bsz; j++) {
		lit_t lit = bpv[j];
		clr_mark(vp, lit, LIT_MARK1);
		clr_mark(vp, neg_l(lit), LIT_MARK1);
	    }
	}
    }

    if (dynvar_size(vp->tlit) < cp->size) {
	size_t size = dynvar_size(vp->tlit);
	uint32_t hvalue;
	cix_t cix;

	hvalue = literal_array_hash(vp, vp->tlit, size);
	if ((cix=clauseset_find(vp,vp->tlit,size,ALPHA,hvalue))!=CLAUSE_NONE) {
	    cix = cp->cix;
	    clause_free(vp, cp);
	    clauseset_plug_hole(vp, ALPHA, GET_IX(cix));
	    return enif_make_undefined(env);  // It is a copy
	}
	memcpy(cp->lit, vp->tlit, size*sizeof(lit_t));
	cp->hvalue = hvalue;
	cp->size = size;
	cp->select = (size > 3) ? 3 : size-1;
    }
    return enif_make_int(env, cp->size);
}

static int is_unit_clause(varp_t* vp, clause_t* cp)
{
    long p;
    int  unbound = 0;

    for (p = 0; p < (long)cp->size; p++) {
	lit_t l = cp->lit[p];
	switch(get_value(vp,l)) {
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

static inline void clause_watch_insert(varp_t* vp, clause_t* cp)
{
    wlink_link(vp, &cp->wl[0], cp->lit[0]);
    wlink_link(vp, &cp->wl[1], cp->lit[1]);
}

// insert sort literal level 'l' into la
// while keeping track on position 'p' and literal index 'v'
static void insert_sort2(int l, int p, int la[3], long pa[3])
{
    if (l >= la[0]) {
	la[2] = la[1]; la[1] = la[0]; la[0] = l;
	pa[2] = pa[1]; pa[1] = pa[0]; pa[0] = p;
    }
    else if (l >= la[1]) {
	la[2] = la[1]; la[1] = l;
	pa[2] = pa[1]; pa[1] = p;
    }
    else if (l >= la[2]) {
	la[2] = l;
	pa[2] = p;
    }
}

static void swap_lit(lit_t* lit, int p, int q)
{
    if (p != q) {
	lit_t tmp = lit[p];
	lit[p] = lit[q];
	lit[q] = tmp;
    }
}

static int clause_watch(varp_t* vp, clause_t* cp)
{
    int la[3];
    long pa[3];
    long p;
    bool_t dead = false;
    int nfalse = 0;
    int lev;

    // fixme: swap in clause literals ?
    la[0] = la[1] = la[2] = -1;
    pa[0] = pa[1] = pa[2] = -1;

    for (p = (int)cp->size-1; p >=0; p--) {
	lit_t l = cp->lit[p];
	switch(get_value(vp,l)) {
	case I_TRUE:
	    dead = true;
	    lev = vp->var_lev[INDEX(l)].level;
	    break;
	case I_FALSE:
	    nfalse++;
	    lev = vp->var_lev[INDEX(l)].level;
	    break;
	case I_UNDEF:
	case I_BOUND:
	default:
	    lev = INT_MAX;
	    break;
	}
	insert_sort2(lev,p,la,pa);
    }

    DBG("size=%u, nfalse=%d,\r\n"
	"la[0]=%d,la[1]=%d,la[2]=%d,\r\n"
	"pa[0]=%ld,pa[1]=%ld,pa[2]=%ld\r\n",
	cp->size, nfalse,
	la[0], la[1], la[2],
	pa[0], pa[1], pa[2]);

    if ((pa[0] < 0) || (pa[1] < 0)) {
	printf("Could not set TWL\r\n");
	return -1;
    }

    swap_lit(cp->lit, 0, pa[0]);
    swap_lit(cp->lit, 1, pa[1]);

    // setup watch
    clause_watch_insert(vp, cp);
    cp->watched = 1;

    if ((la[0] == INT_MAX) && (la[1] != INT_MAX)) {
	if (!dead) {
	    DBG("Set UNIT\r\n");
	    put_l(vp, cp->lit[0], I_TRUE, cp->cix, vp->level);
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

static pos_t xref_find_pix(clause_t* cp, lit_t lit)
{
    int i;
    for (i = 0; i < (int)cp->size; i++) {
	if (cp->lit[i] == lit)
	    return i;
    }
    return -1;
}

static int xref_add(varp_t* vp, clause_t* cp, lit_t lit)
{
    literal_t* lp = l2ll(vp, lit);
    cix_t* xp;

    if (lp->xref == NULL)
	lp->xref = dynarray_empty(vp, sizeof(cix_t));
    if ((xp = dynarray_add(lp->xref)) == NULL)
	return -1;
    *xp = cp->cix;
    return 0;
}

// locate and remove xref link
static inline void xref_del(varp_t* vp, clause_t* cp, lit_t lit)
{
    literal_t* lp = l2ll(vp, lit);
    if (lp->xref != NULL) {
	cix_t* xptr  = dynarray_element(lp->xref,0);
	int xn = (int)dynarray_size(lp->xref);
	int i;

	for (i = 0; i < xn; i++) {
	    if (*xptr == cp->cix) {
		dynarray_delete(lp->xref, i);
		return;
	    }
	    xptr++;
	}
	DBG("xref not found for clause %u\r\n", cp->cix);
    }
}

static int xref_add_clause(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) { // since clauseset may, temporary, have holes!
	long n = (long)cp->size;
	long p;
	for (p = 0; p < n; p++) {
	    if (xref_add(vp, cp, cp->lit[p]) < 0)
		return -1;
	}
    }
    return 0;
}

static void xref_del_clause(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) { // since clauseset may, temporary, have holes!
	long n = (long)cp->size;
	long p;
	for (p = 0; p < n; p++)
	    xref_del(vp, cp, cp->lit[p]);
    }
}

static int clause_link(varp_t* vp, clause_t* cp)
{
    if (vp->opt.xref) {
	if (xref_add_clause(vp, cp) < 0)
	    return -1;
    }
    return clause_watch(vp, cp);
}

static void clause_unlink(varp_t* vp, clause_t* cp)
{
    clause_unwatch(vp, cp);      // remove watched literals
    if (vp->opt.xref)
	xref_del_clause(vp, cp);
}

// link clause and update statistics
static int clause_install(varp_t* vp, clause_t* cp)
{
    int si = GET_SI(cp->cix);
    int r;

    if (si == ALPHA) {
	// do not link clause, do not update statistics,
	// this must be done in move
	r = 1;
    }
    else if ((r = clause_link(vp, cp)) >= 0) {
#ifdef DEBUG_NBCP
	enif_fprintf(stdout, "%sadd: ", indent(vp->level));
	print_sym_clause(vp, "", cp);
#endif
    }
    return r;
}

static int parse_clone_opts(ErlNifEnv* env, ERL_NIF_TERM map,
			    varp_clone_opt_t* opt)
{
    ERL_NIF_TERM key, value;
    ErlNifMapIterator iter;

    if (!enif_map_iterator_create(env, map, &iter, ERL_NIF_MAP_ITERATOR_FIRST))
	return 0;

    while (enif_map_iterator_get_pair(env, &iter, &key, &value)) {
	if (vif_clone_config(env, key, value, opt) < 0)
	    return 0;
	enif_map_iterator_next(env, &iter);
    }
    enif_map_iterator_destroy(env, &iter);
    return 1;
}

// copy (clone) the varp structure (clauses and variables)
// but leave the xref etc for the cloneer to speficy
static ERL_NIF_TERM varp_clone(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp0;
    varp_t* vp;
    ERL_NIF_TERM varc;
    varp_clone_opt_t opt;
    size_t vsize;
    int si, i;

    DBG("clone varc instance\r\n");

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp0))
	return enif_make_badarg(env);

    opt.config    = vp0->opt;
    opt.clauseset = (1 << DELTA);
    opt.level     = 0;
    opt.queue     = false;

    if (!parse_clone_opts(env, argv[1], &opt))
	return enif_make_badarg(env);

    if ((opt.level < 0) || (opt.level > vp0->level))
	opt.level = vp0->level;

    if (!(vp = enif_alloc_resource(varp_res, sizeof(varp_t))))
	goto error;
    memset(vp, 0, sizeof(varp_t));

    if (setup(vp, &opt.config) < 0)
	goto error;

    vsize = dynvar_size(vp0->var_map);
    if (add_variables(vp, vsize) < 0)
	goto error;

    for (i = 1; i < (int)vsize; i++) {
	variable_t* var0 = vp0->var_map[i];
	variable_t* var  = vp->var_map[i];
	ival_t v = get_vv(vp0, var0);
	markbits_t mark0;
	int j;

	mark0 = vp0->lit_mark[MAKE_LIT(i,0)];
	vp->lit_mark[MAKE_LIT(i,0)] = mark0 & (VAR_ATOM|VAR_USED);

	switch(v) {
	case I_FALSE:
	case I_TRUE:
	    if (vp0->var_lev[var0->ix].level <= opt.level)
		set_vv(vp, var, v);
	    break;
	case I_BOUND:
	    bnd_vv(vp, var);
	    j = export_l(var0->bl);
	    var->bl = vindex_l(vp, j);
	    break;
	case I_UNDEF:
	default:
	    break;
	}
    }

    if (vp->symtab) {
	size_t size = dynvar_size(vp0->symtab);
	int slot;
	for (slot = 0; slot < (int)size; slot++) {
	    symbol_t* sp = dlist_first(&vp0->symtab[slot]);
	    while(sp != NULL) {
		symbol_t* copy = symbol_copy(vp, sp);
		size_t n = dynvar_size(copy->lit);
		int i;
		symbol_insert(vp, copy);
		for (i = 0; i < (int)n; i++) {
		    if (sref_add(vp, copy->lit[i], copy, i) < 0) {
			return enif_raise_exception(env, ATOM(memory_limit));
		    }
		}
		sp = dlist_next(sp);
	    }
	}
    }

    if (opt.level >= (int)dynvar_size(vp->bnd))
	resize_levels(vp, dynvar_size(vp0->bnd));

    for (i = 0; i <= opt.level; i++) {  // clone undo structure
	int m = vp0->bnd[i].size;
	lit_t* srcv = bindings(vp0, &vp0->bnd[i]);
	lit_t* dstv = bindings(vp, &vp->bnd[i]);
	int li = export_l(vp0->bnd[i].decision);
	int j;
	vp->bnd[i].decision = vindex_l(vp, li);
	vp->bnd[i].t = vp0->bnd[i].t;
	vp->bnd[i].offs = vp0->bnd[i].offs;
	for (j = 0; j < m; j++) {
	    dstv[j] = srcv[j];
	}
    }

    if (opt.queue) {  // clone queue
	size_t size = dynvar_size(vp0->q);
	int i;

	dynvar_resize(vp->q, size);
	for (i = 0; i < (int)size; i++) {
	    lit_t xl = vp0->q[i];
	    vp->q[i] = xl;
	    set_mark(vp, xl, LIT_MARKQ);
	}
    }

    for (si = 0; si < NUM_CSET; si++) {
	if (opt.clauseset & (1 << si)) {
	    size_t n = dynvec_size(vp0->clauseset,si);
	    for (i = 0; i < (int)n; i++) {
		clause_t* cp = clause_copy(vp, vp0->clauseset[si][i]);
		if (cp != NULL) {
		    if (clause_insert(vp, si, cp, cp->hvalue) == CLAUSE_NONE)
			goto error;
		    // FIXME clone watch points! if opt.queue!
		    clause_install(vp, cp);
		}
	    }
	}
    }

    varc = enif_make_resource(env,vp);
    enif_release_resource(vp);
    return varc;

error:
    if (vp)
	enif_release_resource(vp);
    return enif_make_badarg(env);
}

int valid_xref(literal_t* xp)
{
    cix_t* xptr = dynarray_element(xp->xref, 0);
    size_t xsize = dynarray_size(xp->xref);

    while(xsize > 1) {
	if (!(xptr[0] < xptr[1]))
	    return 0;
	xptr++;
	xsize--;
    }
    return 1;
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
static void subst_ll(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp   = l2ll(vp, yl);
    literal_t* xp   = l2ll(vp, xl);
    literal_t* nxp  = l2ll(vp, neg_l(xl));

    cix_t*    xptr = dynarray_element(xp->xref,0);
    size_t    xlen = dynarray_size(xp->xref);

    cix_t*    nxptr = dynarray_element(nxp->xref,0);
    size_t    nxlen = dynarray_size(nxp->xref);

    cix_t*    yptr = dynarray_element(yp->xref,0);
    size_t    ylen = dynarray_size(yp->xref);

    dynarray_t* x1 = dynarray_create(vp, xlen+ylen, sizeof(cix_t));
    cix_t*    x1ptr = dynarray_element(x1,0);
    cix_t*    x1ptr0 = x1ptr;
	
    ASSERT (yp != xp);
    ASSERT(valid_xref(yp));

    DBG("replace %s with %s\r\n",format_lit(vp, yl),format_lit(vp, xl));
    // must set size on x1 otherwise it will zero when shrinking
    dynarray_resize(x1, xlen+ylen);
		 
    // scan and rewrite all y's into x's
    while(ylen--) {
	cix_t   cix = *yptr;
	clause_t* cp = get_clause(vp, cix);
	pos_t   ypix = xref_find_pix(cp, yl);
	int rewatch = 0;

	ASSERT(yl == cp->lit[ypix]);

	// if ((ypix == cp->wl[0].p) || (ypix == cp->wl[1].p)) {
	if ((ypix == 0) || (ypix == 1)) {
	    clause_unwatch(vp, cp);
	    rewatch = 1;
	}

	while(xlen && (*xptr < cix)) {  // step x
	    *x1ptr++ = *xptr++;  // copy reference
	    xlen--;
	}

	while(nxlen && (*nxptr < cix)) { // step !x
	    nxptr++;
	    nxlen--;
	}

	if ( ((xlen==0) || (*xptr > cix)) &&
	     ((nxlen==0) || (*nxptr > cix)) )  { // Y only
	    DBG("clause %d replace Y pos=%d\r\n", cp->cix, ypix);
	    cp->lit[ypix] = xl;
	    cp->hvalue = literal_hash_del(cp->hvalue, yl);
	    cp->hvalue = literal_hash_add(cp->hvalue, xl);
	    if (rewatch) {
		if (clause_watch(vp, cp) <= 0) {
		    ASSERT(0);
		}
	    }
	    *x1ptr++ = *yptr;
	}
	else if ((xlen > 0) && (*xptr == cix)) { // X, Y
	    DBG("clause %d replace X,Y FALSE, pos=%d\r\n", cp->cix, ypix);
	    cp->lit[ypix] = LIT_FALSE; //
	    cp->hvalue = literal_hash_del(cp->hvalue, yl);
	    if (rewatch) {
		if (is_unit_clause(vp, cp)) {
		    // enif_fprintf(stdout, "unit clause in subst(%d,%d)\r\n",
		    // export_l(xl), export_l(yl));
		    // print_clause(vp, "unit", cp);
		    put_l(vp, xl, I_TRUE, cp->cix, vp->level);
		}
		else {
		    if (clause_watch(vp, cp) <= 0) {
			ASSERT(0);
		    }
		}
	    }
	    *x1ptr++ = *xptr++;
	    xlen--;
	}
	else if ((nxlen > 0) && (*nxptr == cix)) { // !X, Y
	    DBG("clause %d replace !X,Y TRUE, pos=%d\r\n", cp->cix, ypix);
	    cp->lit[ypix] = LIT_TRUE;
	    cp->hvalue = literal_hash_del(cp->hvalue, yl);
	    // FIXME: swap away TRUE? (may not be a problem since dead)
	    if (!cp->dead) {
		cp->dead = 1;
		vp->cdead[GET_SI(cp->cix)]++;
	    }
	}
	yptr++;
    }

    while(xlen--)
	*x1ptr++ = *xptr++;
    
    dynarray_resize(x1, x1ptr - x1ptr0);

    dynarray_destroy(vp, xp->xref);
    xp->xref = x1;

    dynarray_destroy(vp, yp->xref);
    yp->xref = NULL;

    ASSERT(valid_xref(xp));
    ASSERT(valid_xref(nxp));
}

// substitue [X/Y] == [X/Y], [!X/!Y]

static void subst(varp_t* vp, lit_t xl, lit_t yl)
{
    variable_t* y = var_l(vp, yl);

    ASSERT(xl != yl);
    ASSERT(get_value(vp, yl) == I_UNDEF);

    vp->num_subst++;
    vp->num_bound++;
    set_max_bound(vp);

    if (get_num_subscribers(vp) > 0)
	log_permanent(vp, xl, yl);

    subst_ll(vp, xl, yl);
    subst_ll(vp, neg_l(xl), neg_l(yl));

    bnd_vv(vp, y);     // mark Y as bound (to X)
    y->bl = is_neg_l(yl) ? neg_l(xl) : xl;
}

static ERL_NIF_TERM varp_subst(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp, yp;
    varp_t* vp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_raise_exception(env, ATOM(literal));
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_raise_exception(env, ATOM(literal));
    if (!vp->opt.xref) // must enable cross reference!
	return enif_raise_exception(env, ATOM(xref));	
    if (vp->level != 0) // only on level 0!
	return enif_raise_exception(env, ATOM(level));

    if (xp == yp)
	return enif_make_boolean(env, true);
    else if (xp == neg_l(yp))
	return enif_make_boolean(env, false);
    else {
	ival_t x, y;

	y = get_value(vp, yp);
	if (I_CONST(y)) {
	    if (!bind_lit(vp, xp, y))
		return enif_make_boolean(env, false);
	    return enif_make_boolean(env, true);
	}
	x = get_value(vp, xp);
	if (I_CONST(x)) {
	    if (!bind_lit(vp, yp, x))
		return enif_make_boolean(env, false);
	    return enif_make_boolean(env, true);	    
	}
	vp->caller_env = env;
	subst(vp, xp, yp);
	vp->caller_env = NULL;
	return enif_make_boolean(env, true);
    }
}

// return level before the call
static ERL_NIF_TERM varp_push_level(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    level = push_level(vp);
    return enif_make_int(env, level);
}

// return level after the call
static ERL_NIF_TERM varp_pop_level(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[])
{
    varp_t* vp;
    int l;
    int level;
    int target;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if ((level = vp->level) <= 0)
	return enif_make_boolean(env, false);
    target = level-1;
    if (argc >= 2) {
	if (!enif_get_int(env, argv[1], &target))
	    return enif_make_badarg(env);
	if (target > level)
	    return enif_make_badarg(env);
    }
    for (l = level; l > target; l--) {
	pop_level(vp);
	unbind_level(vp, l);
	init_level(vp, l);
    }
    return enif_make_int(env, vp->level);
}

// use 2-lower bits on 0 pointer to signal cases
#define EV_UNIT     0   // unit is in lit[0]
#define EV_CONFLICT 1   // conflict found
#define EV_WATCH    2   // update watch point i
#define EV_WATCH2   3   // update watch point i
#define EV_DEAD     4   // clause is dead
#define EV_TRIGGER  5

// monitor clause
// A ~A - B C D E F
// if A or ~A are set then an undefined literal B is selected
// B ~B - A C D E F   and B is waited for
// when all literals got values a trigger will fire
//

static inline int mon_clause(varp_t* vp, lit_t* lit, int32_t size,
			     pos_t wp0, pos_t wp1)
{
    pos_t p;

    for (p = 2; p < size; p++) {
	lit_t pl = lit[p];
	switch(get_value(vp, pl)) {
	case I_FALSE: break;
	case I_TRUE:  break;
	case I_UNDEF: // swap lit[0] and lit[p]
	    lit[p] = lit[wp0];
	    lit[wp0] = pl;
	    lit[wp1] = neg_l(pl);
	    return EV_WATCH;
	case I_BOUND:
	default:
	    ASSERT(0);
	}
    }
    // all literals got values - trigger
    return EV_TRIGGER;
}

static inline int bcp_2_clause(varp_t* vp, lit_t l1)
{
    ival_t lw;

    if ((lw = get_value(vp, l1)) == I_TRUE)
	return EV_DEAD;
    if (lw == I_FALSE)
	return EV_CONFLICT;
    return EV_UNIT;
}

static inline lit_t bcp_3_clause(varp_t* vp,lit_t* lit,pos_t wp0,lit_t l1)
{
    ival_t lw;
    lit_t  pl;

    if ((lw = get_value(vp, l1)) == I_TRUE)
	return EV_DEAD;
    pl = lit[2];
    switch(get_value(vp, pl)) {
    case I_TRUE:
	return EV_DEAD;
    case I_FALSE:
	if (lw == I_FALSE)
	    return EV_CONFLICT;
	return EV_UNIT;
    case I_UNDEF:
    case I_BOUND:
    default:
	break;
    }
    // swap lit[wp0] and lit[2]
    lit[2] = lit[wp0];
    lit[wp0] = pl;
    return EV_WATCH;
}

static inline int bcp_n_clause(varp_t* vp,lit_t* lit,int32_t size,
			       pos_t wp0,lit_t l1)
{
    pos_t p;
    ival_t lw;

    if ((lw = get_value(vp, l1)) == I_TRUE)
	return EV_DEAD;

    for (p = 2; p < size; p++) {
    // for (p = n-1; p >= 2; p--) {
	lit_t pl = lit[p];
	switch(get_value(vp, pl)) {
	case I_FALSE:
	    break;
	case I_TRUE:
	    return EV_DEAD;
	case I_UNDEF: // swap lit[wl0->p] and lit[p]
	    lit[p] = lit[wp0];
	    lit[wp0] = pl;
	    return EV_WATCH;
	case I_BOUND:
	default:
	    ASSERT(0);
	}
    }
    if (lw == I_FALSE)
	return EV_CONFLICT;
    return EV_UNIT;
}

static int is_turbo_clause(varp_t* vp, clause_t* cp, lit_t x, lit_t* zp)
{
    lit_t* yp = cp->lit;
    size_t n  = cp->size;

    while(n--) {
	lit_t y = *yp++;
	if ((y != x) && (get_value(vp,y) == I_TRUE)) {
	    *zp = y;
	    return 1;
	}
    }
    return 0;
}

static int bcp_turbo(varp_t* vp, lit_t xp)
{
    literal_t* lp = l2ll(vp, xp);
    cix_t* xptr   = dynarray_element(lp->xref, 0);
    size_t  n     = dynarray_size(lp->xref);
    int r = 1;

#if defined(DEBUG_BCP)
    if (!vp->opt.xref) enif_fprintf(stdout, "turbo without xref!\r\n");
#endif
    if (n == 0)
	return 0;

    STK_BEGIN(lit_t, q, n+1) {
	int j = 1;
	while(n--) {
	    clause_t* cp = get_clause(vp, *xptr);
	    if (cp != NULL) {
		//enif_fprintf(stdout,"turbo check %s\r\n", format_lit(vp, xp));
		//print_lit_array("trubo check", cp->lit, cp->size);
		if (!is_turbo_clause(vp,cp,xp,&q[j])) {
		    r = 0;
		    STK_LEAVE(q);
		}
		j++;
	    }
	    xptr++;
	}
	q[0] = xp;
	// print_lit_array("TURBO clause", q, j);
    } STK_END(q);
    return r;
}

static int bcp_clauses(varp_t* vp, lit_t xl, int level, int depth)
{
    wlink_t** wlp;
    wlink_t*  wl;
restart:
    wlp = watch_list(vp, xl);
    DBG_BCP("%sBcp_clauses: %s\r\n", indent(level),format_lit(vp, neg_l(xl)));

    while((wl = *wlp) != NULL) {
	clause_t* cp = clause_pointer(wl);
	int i = wlink_index(wl);
#if defined(DEBUG_BCP)
	print_sym_clause(vp, "  bcp: ", cp);
#endif
	if (!cp->dead && !cp->conflict) {
	    lit_t* lit = cp->lit;
	    lit_t u = lit[1-i];
	    int r;
	    COUNT(vp, cp->select);
	    switch(cp->select) {
	    case 0: {
		ASSERT(i == 0);
		r = mon_clause(vp,lit,cp->size,i,1-i);
		break;
	    }
	    case 1: {
		r = bcp_2_clause(vp,u);
		break;
	    }
	    case 2: {
		r = bcp_3_clause(vp,lit,i,u);
		break;
	    }
	    default: {
		r = bcp_n_clause(vp,lit,cp->size,i,u);
		break;
	    }
	    }

	    switch(r) {
	    case EV_TRIGGER: // monitor clause triggered
		DBG1("monitor clause %d trigger\r\n", cp->cix);
		// collect clause
		break;
	    case EV_CONFLICT:
		if (vp->max_conflicting == 1) {
		    vp->conflicting_clauses[vp->num_conflicting++] = cp->cix;
		    goto conflict;
		}
		else if (vp->num_conflicting < vp->max_conflicting) {
		    vp->conflicting_clauses[vp->num_conflicting++] = cp->cix;
		    cp->conflict = 1;
		}
		else
		    goto conflict;
		break;
	    case EV_DEAD:
		COUNT(vp, CLAUSE_DEAD_COUNTER);
		if (level == 0) {
		    cp->dead = 1;
		    vp->cdead[GET_SI(cp->cix)]++;
		    schedule_unwatch_clause(vp, cp);
		}
		break;
	    case EV_WATCH: {
		wlink_t* wl0 = &cp->wl[i];
		*wlp = wl0->next;
		wlink_link(vp, wl0, lit[i]);
		break;
	    }
	    case EV_WATCH2: {
		wlink_t* wl0 = &cp->wl[i];
		wlink_t* wl1 = &cp->wl[1-i];		
		*wlp = wl0->next;
		wlink_link(vp, wl0, lit[i]);
		// FIXME!!! make better
		wlink_unlink(vp, cp, neg_l(xl));
		wlink_link(vp, wl1, lit[1-i]);
		break;
	    }
	    case EV_UNIT: {
		put_nq_l(vp, u, I_TRUE, cp->cix, level);
		if (level == 0) {
		    cp->dead = 1;
		    vp->cdead[GET_SI(cp->cix)]++;
		    schedule_unwatch_clause(vp, cp);
		}
		if (wl->next == NULL) {
		    if ((level == 0) && vp->opt.xref)
			kill_clauses(vp, neg_l(xl));
		    xl = neg_l(u);
		    goto restart;
		}
		
		if (vp->opt.qtype == q_recursive) {
		    if (depth) {
			if (bcp_clauses(vp, neg_l(u), level, depth-1) < 0)
			    goto conflict;
		    }
		    else {
			DBG1("bcp max depth %d reached enqueue\r\n",
			     MAX_BCP_DEPTH);
			lqueue_insert(vp, neg_l(u));
		    }
		}
		else {
		    lqueue_insert(vp, neg_l(u));
		}
		break;
	    }
	    default:
		break;
	    }
	}
	if (*wlp == wl)
	    wlp = &wl->next;
    }
    
    if ((level == 0) && vp->opt.xref)
	kill_clauses(vp, neg_l(xl));
    return 0;
    
conflict:
    if ((level == 0) && vp->opt.xref)
	kill_clauses(vp, neg_l(xl)); 
    return -1;
}

static int bcp(varp_t* vp)
{
    lit_t xl;
    int r = 0;
    int level = vp->level;
    int level_size0 = vp->bnd[level].size; // size before bcp
    int level_size;
    
    COUNT(vp, BCP_COUNTER);
    while((xl = lqueue_deq(vp)) != LIT_FALSE) {
	DBG_BCP("%sBcp: %s\r\n", indent(level), format_lit(vp, xl));
	if ((r = bcp_clauses(vp, xl, level, MAX_BCP_DEPTH)) < 0) {
	    COUNT(vp, CONFLICT_COUNTER);
	    break;
	}
    }
    level_size = vp->bnd[0].size; // size after bcp    
    set_max_bound(vp);
    if (level == 0) {
	if (get_num_subscribers(vp) > 0) { // report all permanent bindings
	    lit_t* bpv = bindings_at(vp, 0);
	    int i = vp->report_index;
	    while(i < level_size) {
		lit_t xl = bpv[i];
		DBG0("log index=%d %s\r\n", i, format_lit(vp,xl));
		log_permanent(vp, xl, LIT_NONE);
		i++;
	    }
	}
	vp->report_index = level_size; // always move report_index
    }
    vp->counter[PROPAGATION_COUNTER] += (vp->bnd[level].size - level_size0);
    return r;
}

// run unwatch, remove clauses that are dead (level=0)
static void bcp_unwatch(varp_t* vp)
{
    size_t n = dynvar_size(vp->unwatch);
    int i;

    for (i = 0; i < (int)n; i++) {
	clause_t* cp = vp->unwatch[i];
	clause_unwatch(vp, cp);
	cp->unwatch = 0;
    }
    dynvar_resize(vp->unwatch, 0);
    // dynvar_set_capacity(vp->unwatch, 1);
}

// bcp:
//  return false  when conflict is found
//         true   when no conflict is found
//         turbo  when turbo-first rule is used
//         {turbo,[literal()]} when turbo-all rule is used
//
static ERL_NIF_TERM varp_bcp(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM turbo = enif_make_list(env, 0);

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (argc >= 2) {
	if (!enif_is_list(env, argv[1]))
	    return enif_make_badarg(env);
	turbo = argv[1];
    }
    vp->caller_env = env;
    vp->num_conflicting = 0;
    bcp(vp);
    vp->caller_env = NULL;
    if (dynvar_size(vp->unwatch)) bcp_unwatch(vp);
    if (vp->num_conflicting) {
	lqueue_clear(vp);
	DBG("num conflicts = %d\r\n", vp->num_conflicting);
	// clear all conflict flags
	clear_conflict_marks(vp,vp->conflicting_clauses, vp->num_conflicting);
	return enif_make_boolean(env, false);
    }
    if (!enif_is_empty_list(env, turbo)) {
	ERL_NIF_TERM head, tail;
	ERL_NIF_TERM turbo_list = enif_make_list(env, 0);
	size_t nturbo = 0;
	int turbo_all = false;  // check all or first? first is default
	if (argc >= 3) {
	    if (!enif_get_boolean(env, argv[2], &turbo_all))
		return enif_make_badarg(env);
	}

	// FIXME: use vif_get_lit_list ...
	while (enif_get_list_cell(env, turbo, &head, &tail)) {
	    lit_t xp;
	    if (!vif_get_lit(env, vp, head, &xp))
		return enif_raise_exception(env, ATOM(literal));
	    if (bcp_turbo(vp, xp)) {
		if (!turbo_all)
		    return ATOM(turbo);
		turbo_list = enif_make_list_cell(env, head, turbo_list);
		nturbo++;
	    }
	    turbo = tail;
	}
	if (!enif_is_empty_list(env, turbo))
	    return enif_make_badarg(env);
	if (nturbo)
	    return enif_make_tuple2(env, ATOM(turbo), turbo_list);
    }
    return enif_make_boolean(env, true);
}

// undo

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
	if (vp->bnd[level].decision != LIT_FALSE) {
	    lit_t xl = vp->bnd[level].decision;
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "undo_bound=%s@%d\r\n",
			 format_lit(vp, xl), level);
#endif
	    order_set_top(vp, var_l(vp, xl));
	}
	switch(vp->bnd[level].t) {
	case uSET:
	    vp->bnd[level].decision = neg_l(vp->bnd[level].decision);
	    vp->bnd[level].t = uTOGGLE;
	    return enif_make_boolean(env, true);
	case uTOGGLE:
	    DBG("fixme: undo uTOGGLE\r\n");
	    return enif_make_boolean(env, false);
	case uDONE:
	    init_level(vp, level);
	    break;
	case uUNDEF:
	default:
	    DBG("fixme: undo uUNDEF\r\n");
	    return enif_make_boolean(env, false);
	}
	if (level == 1)
	    break;
	pop_level(vp);
    }
    return enif_make_boolean(env, false);
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
    int x;
    int32_t level;
    lit_t xp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    level = vp->level;
    vp->num_conflicting = 0;
    vp->caller_env = env;

    DBG("nbcp: level=%d, t=%s, decision=%s\r\n",
	level, bnd_state_name[vp->bnd[level].t],
	format_lit(vp, vp->bnd[level].decision));

    switch(vp->bnd[level].t) {
    case uUNDEF:
	vp->bnd[level].decision = LIT_FALSE;
	if ((x = next_unbound(vp)) == 0) {
	    vp->caller_env = NULL;
	    return enif_make_boolean(env, true);  // model
	}
	DBG_ORDER("%sNbcp: t=uUNDEF x=%d\r\n", indent(level), x);
	break;
    case uSET:
	DBG_ORDER("%sNbcp: t=uSET\r\n", indent(level));
	goto bcp;
    case uTOGGLE:
	// NOTE! xp is already toggled by undo!
	xp = vp->bnd[level].decision;
	put_l(vp, xp, vp->bnd[level].value, CLAUSE_NONE, level);
	vp->bnd[level].t = uDONE;
	DBG_ORDER("%sNbcp: t=uTOGGLE decision=%s\r\n",
		  indent(level), format_lit(vp, xp));
	goto bcp;

    case uDONE:
	DBG("try to bcp t=uDONE state\r\n");
	vp->caller_env = NULL;
	return enif_make_badarg(env);
    default:
	DBG("unknown bcp state\r\n");
	vp->caller_env = NULL;
	return enif_make_badarg(env);
    }
    if (level == 0)
	goto bcp;
next:
    xp = vindex_l(vp, x);
    vp->bnd[level].decision = xp;
    vp->bnd[level].t = uSET;
    vp->bnd[level].value = decide_phase(vp, xp);    
    put_l(vp, xp, vp->bnd[level].value, CLAUSE_NONE, level);
    DBG_ORDER("%sNbcp: next decision=%s\r\n",
	      indent(level), format_lit(vp, xp));
bcp:
    bcp(vp);
    if (dynvar_size(vp->unwatch)) bcp_unwatch(vp);
    if (vp->num_conflicting == 0) {
	x = next_unbound(vp);
	DBG_ORDER("%sNbcp: step x=%d\r\n", indent(level), x);
	if (x == 0) {
	    vp->caller_env = NULL;
	    return enif_make_boolean(env, true);  // model
	}
	push_level(vp);
	level++;
	goto next;
    }
    DBG_NBCP("%sContradiction\r\n", indent(level));
    // conflict found
    vp->caller_env = NULL;
    lqueue_clear(vp);
    DBG("num conflicts = %d\n", vp->num_conflicting);
    clear_conflict_marks(vp,vp->conflicting_clauses, vp->num_conflicting);
    return enif_make_boolean(env, false);
}

// check all literals in lit that they are constistent
// either undefined ot have the same sign as the bound variable
// return -1 if consistent, otherwise index to first inconsistent literal
static int vconsistent(varp_t* vp, int pos, lit_t* lp, int len)
{
    while(len--) {
	lit_t xi = *lp++;
	ival_t v = get_value(vp, L_VAR(xi));  // variable value
	if (v != I_UNDEF) {
	    if (I_SIGN(v) != L_SIGN(xi))
		return pos;
	}
	pos++;
    }
    return -1;
}

static int bcp1(ErlNifEnv* env, varp_t* vp)
{
    vp->caller_env = env;
    vp->num_conflicting = 0;
    bcp(vp);
    vp->caller_env = NULL;
    if (vp->num_conflicting) {
	lqueue_clear(vp);
	clear_conflict_marks(vp,vp->conflicting_clauses,vp->num_conflicting);
	return 0;
    }
    return 1;
}

//
// varp:vbcp(Vp::varp(), [literal()]) ->
//                         {integer(),literal()} | true | false.
// varp:vbcp(Vp::varp(), [literal()], SingleLevel) ->
//                         {integer(),literal()} | true | false.

static ERL_NIF_TERM varp_vbcp(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int single_level = false;
    int len;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);    
    if (!vif_load_tlit(env, vp, &len, argv[1]))
    	return enif_make_badarg(env);
    if (argc >= 3) {
	if (!enif_get_boolean(env, argv[2], &single_level))
	    return enif_make_badarg(env);
    }
    if (single_level) {
	int i;
	for (i = 0; i < len; i++) {
	    if (!bind_lit(vp, vp->tlit[i], I_TRUE))
		return enif_make_tuple2(env,
					enif_make_int(env,TUPLEINDEX(i)),
					make_lit(env, vp->tlit[i]));
	}
	push_level(vp);
	if (!bcp1(env, vp))
	    return enif_make_boolean(env, false);
	return enif_make_boolean(env, true);
    }
    else {
	int i, j;
	PRINT_LIT_ARRAY("vconsistent?",vp->tlit,len);
	if ((j = vconsistent(vp, 0, vp->tlit, len)) >= 0)
	    return enif_make_tuple2(env,
				    enif_make_int(env,TUPLEINDEX(j)),
				    make_lit(env, vp->tlit[j]));
	for (i = 0; i < len; i++) {
	    if (i > 0) push_level(vp);
	    if (!decide_lit(vp, vp->tlit[i], I_TRUE)) {
		DBG("decide_lit is not consistent!\r\n");
	    }
	    if (!bcp1(env, vp))
		return enif_make_boolean(env, false);
	    PRINT_LIT_ARRAY("vconsistent?",vp->tlit+i,len-i);
	    if ((j = vconsistent(vp, i, &vp->tlit[i], len-i)) >= 0) {
		return enif_make_tuple2(env,
					enif_make_int(env,TUPLEINDEX(j)),
					make_lit(env, vp->tlit[j]));
	    }
	}
	return enif_make_boolean(env, true);
    }
}


// Count total size of memory used by literals used by clauseset
// FIXME: cound all memory used by segments
static size_t clauseset_memory_size(varp_t* vp, int si)
{
    size_t size = dynvec_size(vp->clauseset,si)*sizeof(clause_t);
    int n = (int)dynvec_size(vp->clauseset, si);
    int i;
    for (i = 0; i < n; i++) {
	clause_t* cp = get_clause(vp, MAKE_CIX(si,i));
	size += cp->size*sizeof(lit_t);
    }
    return size;
}

static size_t xref_memory_size(varp_t* vp)
{
    size_t size = 0;
    if (vp->opt.xref) {
	int vn = (int)dynvar_size(vp->var_map);
	int i;
	for (i = 1; i < vn; i++) {
	    size += dynarray_size(vp->var_map[i]->lit[0].xref)*sizeof(cix_t);
	    size += dynarray_size(vp->var_map[i]->lit[1].xref)*sizeof(cix_t);
	}
    }
    return size;
}

static size_t sref_memory_size(varp_t* vp)
{
    size_t size = 0;
    int vn = dynvar_size(vp->var_map);
    int i;
    for (i = 1; i < vn; i++) {
	size += dynarray_size(vp->var_map[i]->lit[0].sref)*sizeof(sref_t);
	size += dynarray_size(vp->var_map[i]->lit[1].sref)*sizeof(sref_t);
    }
    return size;
}

    
// get information
static ERL_NIF_TERM varp_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (EQUAL_KEY(env, bcp_counter, argv[1])) {
	return enif_make_uint64(env, vp->counter[BCP_COUNTER]);
    }
    if (EQUAL_KEY(env, number_of_bcps, argv[1])) { // ALIAS
	return enif_make_uint64(env, vp->counter[BCP_COUNTER]);
    }
    if (EQUAL_KEY(env, conflict_counter, argv[1]) ) {
	return enif_make_uint64(env, vp->counter[CONFLICT_COUNTER]);
    }
    if (EQUAL_KEY(env, number_of_conflicts, argv[1]) ) {  // ALIAS
	return enif_make_uint64(env, vp->counter[CONFLICT_COUNTER]);
    }
    if (EQUAL_KEY(env, number_of_propagations, argv[1]) ) {
	return enif_make_uint64(env, vp->counter[PROPAGATION_COUNTER]);
    }    
    if (EQUAL_KEY(env, number_of_decisions, argv[1]) ) {
	return enif_make_uint64(env, vp->counter[DECISION_COUNTER]);
    }
    if (EQUAL_KEY(env, clause_n_counter, argv[1])) {
	return enif_make_uint64(env, vp->counter[CLAUSE_N_COUNTER]);
    }
    if (EQUAL_KEY(env, clause_m_counter, argv[1])) {
	return enif_make_uint64(env, vp->counter[CLAUSE_MON_COUNTER]);
    }    
    if (EQUAL_KEY(env, clause_2_counter, argv[1])) {
	return enif_make_uint64(env, vp->counter[CLAUSE_2_COUNTER]);
    }
    if (EQUAL_KEY(env, clause_3_counter, argv[1])) {
	return enif_make_uint64(env, vp->counter[CLAUSE_3_COUNTER]);
    }
    if (EQUAL_KEY(env, clause_d_counter, argv[1])) {
	return enif_make_uint64(env, vp->counter[CLAUSE_DEAD_COUNTER]);
    }
    if (EQUAL_KEY(env, mark_counter, argv[1]) ) {
	return enif_make_uint64(env, vp->counter[MARK_COUNTER]);
    }
    if (EQUAL_KEY(env, decision_counter, argv[1]) ) {
	return enif_make_uint64(env, vp->counter[DECISION_COUNTER]);
    }    
    if (EQUAL_KEY(env, max_conflicting, argv[1])) {
	return enif_make_int(env, vp->max_conflicting);
    }
    if (EQUAL_KEY(env, number_of_conflicting_clauses, argv[1])) {
	return enif_make_int(env, vp->num_conflicting);
    }
    if (EQUAL_KEY(env, number_of_variables, argv[1])) {
	return enif_make_int(env, dynvar_size(vp->var_map)-1);
    }
    if (EQUAL_KEY(env, number_of_clauses, argv[1])) {
	return enif_make_int(env, get_number_of_clauses(vp));
    }
    if (EQUAL_KEY(env, number_of_dead_clauses, argv[1])) {
	int n = vp->cdead[DELTA]+vp->cdead[GAMMA]+
	    vp->cdead[BETA]+vp->cdead[ALPHA];
	return enif_make_int(env, n);
    }
    if (EQUAL_KEY(env, number_of_learnt_clauses, argv[1])) {
	return enif_make_int(env, vp->cnum[1]);
    }
    if (EQUAL_KEY(env, number_of_bound_variables, argv[1])) {
	return enif_make_int(env, get_num_bound(vp));
    }
    if (EQUAL_KEY(env, number_of_subst_variables, argv[1])) {
	return enif_make_int(env, vp->num_subst);
    }
    if (EQUAL_KEY(env, number_of_unbound_variables, argv[1])) {
	int n = (dynvar_size(vp->var_map)-1) - get_num_bound(vp);
	return enif_make_int(env, n);
    }

    if (EQUAL_KEY(env, level, argv[1])) {
	return enif_make_uint(env, vp->level);
    }
    if (EQUAL_KEY(env, size, argv[1])) {
	return enif_make_uint(env, vp->opt.vsize);
    }
    if (EQUAL_KEY(env, qtype, argv[1])) {
	switch(vp->opt.qtype) {
	case q_lifo: return ATOM(lifo);
	case q_fifo: return ATOM(fifo);
	case q_recursive: return ATOM(recursive);
	default: return ATOM(undefined);
	}
    }
    if (EQUAL_KEY(env, max_level, argv[1])) {
	int val = get_and_reset_max_level(vp);
	return enif_make_int(env, val);
    }
    if (EQUAL_KEY(env, min_level, argv[1])) {
	int val = get_and_reset_min_level(vp);
	return enif_make_int(env, val);
    }
    if (EQUAL_KEY(env, max_bound, argv[1])) {
	size_t val = get_and_reset_max_bound(vp);
	return enif_make_ulong(env, (unsigned long)val);
    }
    if (EQUAL_KEY(env, literal_size, argv[1])) {
	return enif_make_uint(env, 8*sizeof(lit_t));
    }
    if (EQUAL_KEY(env, literal_integer, argv[1])) {
	return enif_make_boolean(env, true);
    }
    if (EQUAL_KEY(env, value_packing, argv[1])) {
	return enif_make_boolean(env, true);
    }
    if (EQUAL_KEY(env, xref, argv[1])) {
	return enif_make_boolean(env, vp->opt.xref);
    }
    if (EQUAL_KEY(env, vsids, argv[1])) {
	return enif_make_boolean(env, vp->opt.vsids);
    }    
    if (EQUAL_KEY(env, hash, argv[1])) {
	return enif_make_boolean(env, vp->opt.hash);
    }
    if (EQUAL_KEY(env, init_phase, argv[1])) {
	switch(vp->opt.init_phase) {
	case I_TRUE: return enif_make_boolean(env, 1);
	case I_FALSE: return enif_make_boolean(env, 0);
	case I_UNDEF: return enif_make_undefined(env);
	default: return enif_make_badarg(env); // internal?
	}
    }
    if (EQUAL_KEY(env, use_phase, argv[1])) {
	return enif_make_boolean(env, vp->opt.use_phase);
    }
    if (EQUAL_KEY(env, all_used, argv[1])) {
	return enif_make_boolean(env, vp->opt.all_used);
    }
    if (EQUAL_KEY(env, version, argv[1])) {
	return enif_make_string(env, VARP_VSN, ERL_NIF_LATIN1);
    }
    if (EQUAL_KEY(env, seed, argv[1])) {
	return enif_make_uint64(env, vp->opt.seed);
    }
    // MEMORY stats
    if (EQUAL_KEY(env, memory_literal_size, argv[1])) {
	return enif_make_uint(env, sizeof(literal_t));
    }
    // both pos and neg litterals are included in the variable structure!
    if (EQUAL_KEY(env, memory_variable_size, argv[1])) {
	return enif_make_uint(env, sizeof(variable_t));
    }
    // clause structure overhead size
    if (EQUAL_KEY(env, memory_clause_size, argv[1])) {
	return enif_make_uint(env, sizeof(clause_t));
    }    
    if (EQUAL_KEY(env, memory_symbol_size, argv[1])) {
	return enif_make_uint(env, sizeof(symbol_t));
    }    
    // memory size of variables / clauses - fixme add everything!
    if (EQUAL_KEY(env, memory_size, argv[1])) {
	unsigned int size =
	    sizeof(varp_t) + 
	    dynvar_size(vp->var_map)*sizeof(variable_t) +
	    clauseset_memory_size(vp, DELTA) +
	    clauseset_memory_size(vp, GAMMA) +
	    clauseset_memory_size(vp, ALPHA) +
	    clauseset_memory_size(vp, BETA) +
	    dynvar_size(vp->symtab)*sizeof(dlist_t) +
	    sizeof(symbol_t)*vp->snum +
	    xref_memory_size(vp) +
	    sref_memory_size(vp)
	    ;
	size += dynvar_size(vp->lit_mark)*sizeof(markbits_t);
	size += dynvar_size(vp->lit_value);
	size += dynvar_size(vp->var_lev)*sizeof(varlev_t);
	return enif_make_uint(env, size);	
    }
    return enif_make_badarg(env);
}

// set config
static ERL_NIF_TERM varp_config(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM key;
    ERL_NIF_TERM value;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    key = argv[1];
    value = argv[2];

    if (EQUAL_KEY(env, max_conflicting, key)) {
	int ivalue;
	if (!enif_get_int(env, value, &ivalue) || (ivalue < 0))
	    return enif_make_badarg(env);
	if ((ivalue == 0) || (ivalue > MAX_CONFLICTING))
	    vp->max_conflicting = MAX_CONFLICTING;
	else
	    vp->max_conflicting = ivalue;
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, xref, key)) {
	int enable;

	if (!enif_get_boolean(env, value, &enable))
	    return enif_make_badarg(env);

	if (enable && !vp->opt.xref) { // xref all clauses
	    int i, si;
	    vp->opt.xref = true;
	    for (si = 0; si < NUM_CSET; si++) {
		size_t n = dynvec_size(vp->clauseset, si);
		for (i = 0; i < (int)n; i++) {
		    if (xref_add_clause(vp, vp->clauseset[si][i]) < 0) {
			return enif_raise_exception(env, ATOM(memory_limit));
		    }
		}
	    }
	}
	else if (!enable && vp->opt.xref) { // teardown xref
	    int i, si;
	    for (si = 0; si < NUM_CSET; si++) {
		size_t n = dynvec_size(vp->clauseset, si);
		for (i = 0; i < (int)n; i++)
		    xref_del_clause(vp, vp->clauseset[si][i]);
	    }
	    vp->opt.xref = false;
	}
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, vsids, key)) {
	int enable;
	if (!enif_get_boolean(env, value, &enable))
	    return enif_make_badarg(env);
	if (enable && !vp->opt.vsids) {
	    cdlist_renumber(&vp->order_list);
	    vp->opt.vsids = true;
	}
	else if (!enable && vp->opt.vsids) {
	    vp->opt.xref = false;
	}
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, hash, key)) {
	int enable;
	if (!enif_get_boolean(env, value, &enable))
	    return enif_make_badarg(env);
	if (enable && !vp->opt.hash) {      // hash all clauses
	    size_t n = vp->cnum[DELTA]+vp->cnum[GAMMA]+vp->cnum[BETA];
	    size_t size = next_pow2(n);

	    dynvar_resize(vp->hashtab, size);

	    clauseset_hash_insert(vp, BETA);
	    clauseset_hash_insert(vp, GAMMA);
	    clauseset_hash_insert(vp, DELTA);

	    vp->opt.hash = true;
	}
	else if (!enable && vp->opt.hash) { // remove hash
	    dynvar_clear(vp->hashtab);
	    allocator_cleanup(&vp->hlink_allocator);
	    vp->hnum = 0;
	    vp->opt.hash = false;
	}
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, qtype, key)) {
	if (EQUAL_KEY(env, fifo, value))
	    vp->opt.qtype = q_fifo;
	else if (EQUAL_KEY(env, lifo, value))
	    vp->opt.qtype = q_lifo;
	else if (EQUAL_KEY(env, recursive, value))
	    vp->opt.qtype = q_recursive;
	else
	    return enif_make_badarg(env);
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, use_phase, key) && enif_is_true(env, value)) {
	vp->opt.use_phase = true;
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, use_phase, key) && enif_is_false(env, value)) {
	vp->opt.use_phase = false;
	return enif_make_ok(env);	
    }
    if (EQUAL_KEY(env, all_used, key) && enif_is_true(env, value)) {
	vp->opt.all_used = true;
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, all_used, key) && enif_is_false(env, value)) {
	vp->opt.all_used = false;
	return enif_make_ok(env);	
    }
    if (EQUAL_KEY(env, init_phase, key) && enif_is_true(env, value)) {
	vp->opt.init_phase = I_TRUE;
	return enif_make_ok(env);
    }
    if (EQUAL_KEY(env, init_phase, key) && enif_is_false(env, value)) {
	vp->opt.init_phase = I_FALSE;
	return enif_make_ok(env);
    }
    else if (EQUAL_KEY(env, init_phase, key) && enif_is_undefined(env, value)) {
	vp->opt.init_phase = I_UNDEF;
	return enif_make_ok(env);
    }
    else if (EQUAL_KEY(env, seed, key)) {
	uint64_t seed;
	if (!enif_get_uint64(env, value, &seed))
	    return enif_make_badarg(env);
	varp_set_seed(vp, seed);
	return enif_make_ok(env);
    }    
    return enif_make_badarg(env);
}

//
// add clause (and normalize, remove literals)
//
#if 0
static int cmp_abs_lit QSORT_ARGS(const void* ap,const void* bp,void* arg)
{
    (void) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);
    if (a == b) return 0;
    if (INDEX(a) == INDEX(b)) {
	if (L_SIGN(a)) return -1;
	return 1;
    }
    else if (INDEX(a) == 0)  // TRUE > *
	return 1;
    else if (INDEX(b) == 0)
	return -1;
    else
	return INDEX(a) - INDEX(b);
}
#endif

// replace literals with constants when possible
static void eval_clause_array(varp_t* vp, lit_t* lit, size_t size)
{
    int i;
    for (i = 0; i < (int)size; i++) {
	if ((lit[i] == LIT_TRUE) || (lit[i] == LIT_FALSE))
	    ;
	else {
	    if (vp->var_lev[INDEX(lit[i])].level == 0) {
		switch(get_value(vp,lit[i])) {
		case I_TRUE:  lit[i] = LIT_TRUE; break;
		case I_FALSE: lit[i] = LIT_FALSE; break;
		case I_BOUND:
		case I_UNDEF:
		default: break;
		}
	    }
	}
    }
}

// normalize clause array 
static size_t norm_clause_array(varp_t* vp, lit_t* lit, size_t size, bool_t raw)
{
    int i, j;
    unsigned Tc=0, Fc=0;

    PRINT_LIT_ARRAY("   src", lit, size);

    // eval first since we must unmark "real" literals in the end!
    if (!raw)
	eval_clause_array(vp, lit, size);

    // PRINT_LIT_ARRAY("   eval", lit, size);
    
    for (i = 0; i < (int)size; i++) {
	if (is_marked(vp, lit[i], LIT_MARK0)) // A,..,A
	    lit[i] = LIT_FALSE;
	else if (is_marked(vp, neg_l(lit[i]), LIT_MARK0)) // !A,..,A
	    lit[i] = LIT_TRUE;
	else
	    set_mark(vp, lit[i], LIT_MARK0);
    }
    // remove constants and count constants found and unmark
    j = 0;
    for (i = 0; i < (int)size; i++) {
	clr_mark(vp, lit[i], LIT_MARK0);
	if (lit[i] == LIT_TRUE) Tc++;
	else if (lit[i] == LIT_FALSE) Fc++;
	else {
	    if (j < i)
		lit[j++] = lit[i];
	    else
		j++;
	}
    }
    // PRINT_LIT_ARRAY("del-dup", lit, size);
    if (j == 0) {
	if ((Tc==0) && (Fc>0))
	    lit[j++] = LIT_FALSE;
    }
    if (Tc>0) // add the T constant to the gate
	lit[j++] = LIT_TRUE;
    PRINT_LIT_ARRAY("   dest", lit, size);
#if defined(DEBUG_BCP)
    enif_fprintf(stdout, "%sclause: ", indent(vp->level));
    print_sym_array_nl(vp, lit, j);
#endif
    return j;	
}

size_t delta_8_count = 0;
size_t delta_16_count = 0;
size_t delta_32_count = 0;

// offset + lit8[i]  (offset = index<<1)
// lit8 = index7bit + sign
// lit16 = index15bit + sign
//#define LIT8(cp,i) ((cp)->offset + (cp)->lit8[i])
//#define LIT16(cp,i) ((cp)->offset + (cp)->lit16[i])
//#define LIT32(cp,i) (cp)->lit32[i]

static cix_t add_clause_array(varp_t* vp, int si, lit_t* lit,
			      size_t size, bool_t put_unit)
{
    clause_t* cp;
    uint32_t hvalue;
    cix_t cix;

    if ((size = norm_clause_array(vp, lit, size, false)) == 0)
	return CLAUSE_FALSE;

    if (lit[size-1] == LIT_TRUE)
	return CLAUSE_TRUE;

    if (size == 1) {  // unit
	if (lit[0] == LIT_FALSE)
	    return CLAUSE_FALSE;
	if (put_unit) { // else make a real clause of the unit
	    put_l(vp, lit[0], I_TRUE, CLAUSE_NONE, 0);
	    return CLAUSE_TRUE;
	}
    }
    if ((cp = clause_alloc(vp, si, size)) == NULL)
	return CLAUSE_NONE;
    hvalue = literal_array_hash(vp, lit, size);
#if 0
// TEST lit encode
    {
	int abs_max;
	int delta_max;
	int i;
	abs_max = INDEX(lit[0]);
	for (i = 1; i < (int)size; i++) {
	    int ind = INDEX(lit[i]);
	    if (ind > abs_max) abs_max = ind;
	}
	delta_max = 0;
	for (i = 1; i < (int)size; i++) {
	    int delta = abs_max - INDEX(lit[i]);
	    if (delta > delta_max) delta_max = delta;
	}
	if (delta_max < 0x7f) delta_8_count++;
	else if (delta_max < 0x7fff) delta_16_count++;
	else delta_32_count++;
    }
#endif    
    memcpy(cp->lit, lit, sizeof(lit_t)*size);
    cix = clause_insert(vp, si, cp, hvalue);
#if 0    
    if (GET_IX(cix) && (GET_IX(cix) % 100 == 0)) {
	printf("delta 8=%lu, 16=%lu, 32=%lu\r\n",
	       delta_8_count, delta_16_count, delta_32_count);
    }
#endif
    return cix;
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
    int len;
    int si = DELTA;
    cix_t cix;
    ERL_NIF_TERM ret;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_load_tlit(env, vp, &len, argv[1]))
    	return enif_make_badarg(env);
    if (argc == 3) {
	if (!vif_get_si(env, argv[2], &si))
	    return enif_make_badarg(env);
    }
    
    vp->caller_env = env;
    if ((cix = add_clause_array(vp,si,vp->tlit,len,true)) == CLAUSE_NONE)
	ret = enif_raise_exception(env, ATOM(memory_limit));
    else if (cix == CLAUSE_TRUE)
	ret = enif_make_boolean(env, true);
    else if (cix == CLAUSE_FALSE)
	ret = enif_make_boolean(env, false);
    else {
	switch (clause_install(vp, get_clause(vp,cix))) {
	case 0:
	    ret = enif_make_tuple2(env,enif_make_boolean(env, false),
				   make_cix(env,cix));
	    break;
	case 1:
	    ret = enif_make_tuple2(env,enif_make_boolean(env, true),
				   make_cix(env,cix));
	    break;
	default:
	    ret = enif_make_badarg(env);
	    break;
	}
    }
    vp->caller_env = NULL;
    return ret;
}

//
// find_clause(vp, [x1, ..., xn]) -> index | false
//
static ERL_NIF_TERM varp_find_clause(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int len;
    cix_t cix;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_load_tlit(env, vp, &len, argv[1]))
	return enif_make_badarg(env);
    len = norm_clause_array(vp, vp->tlit, len, true);
    if ((cix = clause_find(vp, vp->tlit, len)) == CLAUSE_NONE)
	return enif_make_boolean(env, false);
    return enif_make_int(env, (int)cix);
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

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix)) {
	unsigned int len;
	if (!enif_get_list_length(env, argv[1], &len))
	    return enif_make_badarg(env);
	else {
	    int csize = len;
	    ERL_NIF_TERM r;

	    STK_BEGIN(ERL_NIF_TERM, elem, csize) {
		STK_BEGIN(uint8_t, buffer, 5*csize+1) {
		    unsigned char* binptr;
		    int x;
		    int i;
		    int n = 0;

		    if (!enif_get_list(env, argv[1], &csize, elem)) {
			r = enif_make_badarg(env);
			STK_LEAVE(buffer);
		    }
		    for (i = 0; i < csize; i++) {
			if (!enif_get_int(env, elem[i], &x) || (x == 0)) {
			    r = enif_make_badarg(env);
			    STK_LEAVE(buffer);
			}
			n += compress_int(x, &buffer[n]);
		    }
		    buffer[n++] = 0;
		    binptr = enif_make_new_binary(env, n, &r);
		    memcpy(binptr, buffer, n);
		} STK_END(buffer);
	    } STK_END0(elem);
	    return r;
	}
    }
    else {
	ERL_NIF_TERM bin;

	if ((cp = get_clause(vp, cix)) == NULL) {
	    enif_make_new_binary(env, 0, &bin);
	}
	else {
	    lit_t* lit = cp->lit;
	    size_t csize = cp->size;
	    STK_BEGIN(uint8_t, buffer1, 5*csize+1) {
		unsigned char* binptr;
		int n = 0;
		int i;

		for (i = 0; i < (int)csize; i++) {
		    int x = export_l(lit[i]);
		    n += compress_int(x, &buffer1[n]);
		}
		buffer1[n++] = 0;
		binptr = enif_make_new_binary(env, n, &bin);
		memcpy(binptr, buffer1, n);
	    } STK_END0(buffer1);
	}
	return bin;
    }
}

#define BUMP_RANK  -4  // bump implication clause number of steps
#define BUMP_LOG10 -3  // bump value = log10(<number-of-variables>)
#define BUMP_LOG2  -2  // bump value = log2(<number-of-variables>)
#define BUMP_NEXT  -1  // move variable as next unbound
#define BUMP_NONE   0


static int get_bump(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, int* bumpp)
{
    int bump;
    double bumpf;
    size_t nvars = dynvar_size(vp->var_map)-1;
    
    if (enif_get_int(env, arg, &bump)) {
	if (bump < 0)
	    return 0;	
    }
    else if (enif_get_double(env, arg, &bumpf)) {
	if (bumpf < 0.0)
	    return 0;
	else if ((bumpf >= 0.0) && (bumpf < 1.0))
	    bump = nvars*bumpf;
	else
	    bump = round(bumpf);
    }
    else if (EQUAL_KEY(env, next, arg))
	bump = BUMP_NEXT;
    else if (EQUAL_KEY(env, log2, arg))
	bump = BUMP_LOG2;
    else if (EQUAL_KEY(env, log10, arg))
	bump = BUMP_LOG10;
    else if (EQUAL_KEY(env, rank, arg))
	bump = BUMP_RANK;
    else if (EQUAL_KEY(env, none, arg))
	bump = BUMP_NONE;
    else
	return 0;
    *bumpp = bump;
    return 1;
}

static void variable_bump(varp_t* vp, variable_t* var, int bump)
{
    size_t nvars;
    
    if (!vp->opt.vsids)
	return;
    if (bump == BUMP_NONE)
	return;
    switch(get_vv(vp, var)) {
    case I_UNDEF: break;
    case I_TRUE:
    case I_FALSE:
	if (vp->var_lev[var->ix].level == 0) return;
	break;
    case I_BOUND:
    default: return;
    }
    
    nvars = dynvar_size(vp->var_map)-1;

    if (bump < 0) {
	cix_t cix;
	switch(bump) {
	case BUMP_RANK:
	    bump = 0;
	    cix = vp->var_lev[var->ix].implication_clause;
	    if (cix != CLAUSE_NONE) {
		clause_t* cp = get_clause(vp, cix);
		if (cp != NULL)
		    bump = cp->size;
	    }
	    break;
	case BUMP_LOG10:
	    bump = log10((double) nvars);
	    break;
	case BUMP_LOG2:
	    bump = log2((double) nvars);
	    break;
	case BUMP_NEXT:
	    bump = nvars;
	    break;
	default:
	    return;
	}
    }

#if defined(DEBUG_ORDER)
    enif_fprintf(stdout, "bump variable %s@%d\r\n",
		 format_variable(var), vp->level);
    dump_order("bump-before", vp);
#endif
    if ((bump == BUMP_NONE) || (bump < 0))
	return;    
    else if (bump >= (int)nvars) {
	order_move_before_top(vp, var);
	return;
    }
    else {
	variable_t* anchor = var;

	// FIXME accelerate this
	while (bump-- && !cdlist_is_first(&vp->order_list, anchor)) {
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "bump: swap %s\r\n", format_variable(anchor));
#endif
	    anchor = cdlist_prev(anchor);
	}

	if (var != anchor) {
	    order_remove(vp, var);
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "bump: insert %s before %s%s\r\n",
			 format_variable(var),
			 (cdlist_is_first(&vp->order_list, anchor) ?
			  "FIRST " : ""),
			 format_variable(anchor));
#endif
	    order_insert_before(vp, anchor, var);
	}
    }
#if defined(DEBUG_ORDER)
    dump_order("bump-after", vp);
#endif
    ASSERT(valid_order(vp));
}

static ERL_NIF_TERM varp_conflict(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i,j;
    int level;
    int bump;
    cix_t cix;
    // literal_t* lp;
    int step = 0;
    lit_t u = LIT_FALSE;
    size_t size;
    uint32_t hvalue;
    clause_t* cp;
    lit_t* trail_vec;
    int pos;     // current pos in trail
    lit_t* lit;
    lit_t ul;
    int len;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!get_bump(env,vp,argv[1],&bump)) {
	DBG0("bump\r\n");
	return enif_make_badarg(env);
    }
    
    if (vif_load_ulit(env, vp, &len, argv[2])) {
	lit = vp->ulit;
	cp = NULL;
    }
    else if (vif_get_cix(env, vp, argv[2], &cix)) {
	if ((cp = get_clause(vp, cix)) == NULL) {
	    DBG0("get_clause: cix=%d\r\n", cix);
	    return enif_make_badarg(env);
	}
	lit = cp->lit;
	len = cp->size;
    }
    else {
	DBG0("get_clause: argv[2]\\n");
	return enif_make_badarg(env);
    }
    if (argc > 3) {
	if (!vif_get_lit(env, vp, argv[3], &u)) {
	    DBG0("lit: argv[3]\r\n");
	    return enif_make_badarg(env);
	}
    }

    level = vp->level;
	
    if ((pos = vp->bnd[level].size) == 0) {
	DBG0("0:pos=%d\r\n", pos);
	return enif_make_undefined(env);  // No trail
    }
    DBG0("0:pos=%d\r\n", pos);    
    pos--;
    trail_vec = bindings(vp, &vp->bnd[level]);

    unmark_all(vp);  // must clear before use!

    dynvar_resize(vp->tlit, 0);

    while (step >= 0) {
	// conflict reason
	for (i = 0; i < len; i++) {
	    lit_t q;
	    if ((q = lit[i]) != u) { // skip unit literal!
		lit_t qv = L_VAR(q);
		int qlevel = vp->var_lev[INDEX(q)].level;
		DBG0("q = %d, qlevel=%d\r\n", export_l(q), qlevel);
		if (!is_marked(vp, qv, VAR_MARK0) && (qlevel > 0)) {
		    variable_bump(vp, var_l(vp, qv), bump);
		    add_mark(vp, qv, VAR_MARK0);
		    if (qlevel >= level)
			step++;
		    else {
			dynvar_append(vp->tlit, &q);
		    }
		}
	    }
	}
	DBG0("1:pos=%d\r\n", pos);
	while((pos >= 0) && !is_marked(vp, L_VAR(trail_vec[pos]), VAR_MARK0))
	    pos--;
	DBG0("2:pos'=%d\r\n", pos);
	if (pos < 0) {
	    unmark_all(vp);
	    DBG0("trail=NULL\r\n");
	    return enif_make_badarg(env);
	}
	ul = L_VAR(trail_vec[pos]);
	u = lit_l(vp, ul);
	if (step <= 1) {
	    u = neg_l(u);
	    dynvar_append(vp->tlit, &u);
	    // printf("UIP = %d (%s)\r\n", export_l(u), format_lit(vp, u));
	    goto make_clause;
	}
	else {
	    cix = vp->var_lev[INDEX(ul)].implication_clause;
	    if ((cix == CLAUSE_NONE) || ((cp = get_clause(vp, cix)) == NULL)) {
		unmark_all(vp);
		return enif_make_badarg(env);
	    }
	    cp->stamp = vp->counter[BCP_COUNTER]; // timestamp clause
	    lit = cp->lit;
	    len = cp->size;
	    clr_mark(vp, ul, VAR_MARK0);
	    pos--;
	    step--;
	}
    }

make_clause:
    unmark_all(vp);
    // printf("tlit.size = %ld\r\n", dynvar_size(vp->tlit));
    size = norm_clause_array(vp, vp->tlit, dynvar_size(vp->tlit), false);
    // printf("size = %ld\r\n", size);

    if (vp->tlit[size-1] == LIT_TRUE)
	return enif_make_boolean(env, true);

    if (size == 1) {  // unit
	if (vp->tlit[0] == LIT_FALSE)
	    return enif_make_boolean(env, false);
    }
    hvalue = literal_array_hash(vp, vp->tlit, size);
    // check if this clause already exist in alpha
    if ((cix=clauseset_find(vp,vp->tlit,size,ALPHA,hvalue)) != CLAUSE_NONE) 
	return enif_make_undefined(env);  // It is a copy
    if ((cp = clause_alloc(vp, ALPHA, size)) == NULL) {
	DBG0("clause alloc alpha size=%ld\r\n", size);
	return enif_make_badarg(env);
    }

    // copy clause but swap in lit[0]=UIP
    j = 0;
    cp->lit[j++] = u;
    for (i = 0; i < (int)size; i++) {
	lit_t v;
	if ((v = vp->tlit[i]) != u)
	    cp->lit[j++] = v;
    }
    if ((cix = clause_insert(vp, ALPHA, cp, hvalue)) == CLAUSE_NONE) {
	DBG0("insert alpha size=%ld\r\n", size);
	return enif_make_badarg(env);
    }
    return make_cix(env, cix);
}


static void clause_remove(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	clause_unlink(vp, cp);
	clause_free(vp, cp);
    }
}

// Move clause from one clause set to another,
// right now only ALPHA => GAMMA is possible!
static ERL_NIF_TERM varp_move_clause(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t cix, cix0;
    clause_t* cp;
    int si, si0;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix0))
	return enif_make_badarg(env);
    if (!vif_get_si(env, argv[2], &si))
	return enif_make_badarg(env);
    if ((cp = get_clause(vp, cix0)) == NULL)
	return enif_make_badarg(env);
    si0 = GET_SI(cix0);
    if ((si != GAMMA) || (si0 != ALPHA))
	return enif_make_badarg(env);

    if (cp->size == 1) {
	lit_t xp = cp->lit[0];
	
	clause_free(vp, cp);
	clauseset_plug_hole(vp, si0, GET_IX(cix0));

	if (!bind_lit(vp, xp, I_TRUE))
	    enif_make_boolean(env, false);
	return enif_make_boolean(env, true);
    }

    cix = clause_insert(vp, si, cp, cp->hvalue);
    set_clause(vp, cix0, NULL);  // kill original position
    vp->cnum[si0]--;             // must decrement
    clauseset_plug_hole(vp, si0, GET_IX(cix0));

    ASSERT(cp == get_clause(vp, cix));

    // setup TWL etc
    switch (clause_install(vp, cp)) {
    case 0:
	return enif_make_tuple2(env,enif_make_boolean(env, false),make_cix(env,cix));
    case 1:
	return enif_make_tuple2(env,enif_make_boolean(env, true),
				make_cix(env,cix));
    default:
	return enif_make_badarg(env);
    }
}

// delete a clause by index or literal list/tuple
static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t cix = CLAUSE_NONE;
    clause_t* cp;
    int si;
    int ix;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix)) {
	int len;
	if (!vif_load_tlit(env, vp, &len, argv[1]))
	    return enif_make_badarg(env);
	len = norm_clause_array(vp, vp->tlit, len, true);
	if ((cix = clause_find(vp, vp->tlit, len)) == CLAUSE_NONE)
	    return enif_make_badarg(env);
    }

    si = GET_SI(cix);
    ix = GET_IX(cix);

    if ((cp = get_clause(vp,cix)) == NULL)
	return enif_make_badarg(env);

#ifdef VALIDATE_TWL
    if (cp->stamp == vp->counter[BCP_COUNTER]) {
	enif_fprintf(stdout, "deleting a new clause %d:%d\r\n",
		     si, ix);
    }
#endif

    clause_remove(vp, cp);

    ASSERT(get_clause(vp, cix) == NULL);

    clauseset_plug_hole(vp, si, ix);

    return enif_make_ok(env);
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
	return enif_raise_exception(env, ATOM(level));
    if ((cp = get_clause(vp,cix)) == NULL)
	return enif_make_ok(env);

    size = cp->size;
    lit  = cp->lit;

    DBG("cleanup: clause %u, size=%lu\r\n", cix, size);

    clause_unlink(vp, cp);
    if (cp->dead) goto remove;
    size = norm_clause_array(vp, lit, size, false);
    if (lit[size-1] == LIT_TRUE)
	goto remove;
    if ((size == 1) && (lit[0] == LIT_FALSE))
	goto error;
    cp->size = size;

    clause_link(vp, cp);
    return enif_make_ok(env);

remove:
    DBG("  %lu-removed\r\n", size);
    clause_free(vp, cp);
    return enif_make_ok(env);

error:
    return enif_make_badarg(env);
}

static int cmp_xref QSORT_ARGS(const void* a, const void* b,void* arg)
{
    UNUSED(arg);
    if (*((cix_t*) a) < *((cix_t*) b))
	return -1;
    else if (*((cix_t*) a) > *((cix_t*) b))
	return 1;
    return 0;
}

static inline void remap_cix(cix_t* cip, const char* tag,
			     int si, int* remap, int n)
{
    UNUSED(n);
    UNUSED(tag);
    cix_t cix = *cip;
    if ((cix != CLAUSE_NONE) && (GET_SI(cix) == si)) {
	int i = GET_IX(cix);
	ASSERT(i < n);
	DBG0("remap %s si=%d, %d => %d\r\n", tag, si, i, remap[i]);
	*cip = MAKE_CIX(si, remap[i]);
    }
}

// use remap (reverse map) to update cix in cross reference after
// sorting clauses.
static void xref_remap(literal_t* lp, int si, int* remap, int n)
{
    cix_t* xptr0 = dynarray_element(lp->xref, 0);
    cix_t* xptr = xptr0;
    size_t len0  = dynarray_size(lp->xref);
    size_t len = len0;

    while(len--) {
	remap_cix(xptr, "xref", si, remap, n);
	xptr++;
    }
    // must sort for subst to work!
    QSORT(xptr0, len0, sizeof(cix_t), cmp_xref, NULL);
}

static void hashtab_remap(varp_t* vp,int i,int si,int* remap,int n)
{
    slist_iter_t iter;

    slist_iter_init(&iter, &vp->hashtab[i]);
    while(!slist_iter_eol(&iter)) {
	hlink_t* hp = slist_iter_current(&iter);
	remap_cix(&hp->cix, "hash", si, remap, n);
	slist_iter_next(&iter);
    }
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

void print_clauseset(varp_t* vp, int si, size_t n)
{
    int i;

    for (i = 0; i < (int)n; i++) {
	clause_t* cp;
	if ((cp = vp->clauseset[si][i]) == NULL) {
	    cix_t cix = cp->cix;
	    enif_fprintf(stdout, "%8d %d:%d (stamp=%ld) = NULL\n",
			 i, GET_SI(cix), GET_IX(cix), cp->stamp);
	}
	else {
	    enif_fprintf(stdout, "%8d", i);
	    print_clause(vp, "", cp);
	}
    }
}

//
// Sort and "compact" clause put all "holes" (NULL clauses)
// at the end and update cnum to match cleanup
//
static ERL_NIF_TERM varp_clauseset_sort(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    int si;
    int n;
    clause_t** cm;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_si(env, argv[1], &si))
	return enif_make_badarg(env);
    if (vp->level != 0)
	return enif_raise_exception(env, ATOM(level));

    if ((n=(int)dynvec_size(vp->clauseset, si)) == 0)
	return enif_make_ok(env);

    cm = vp->clauseset[si];

    QSORT(cm, n, sizeof(clause_t*), cmp_stamp, vp);

//    enif_fprintf(stdout, "SORTED clauses si=%d\n", si);
//    print_clauseset(vp, si, n);

    STK_BEGIN(int, rmap, n) {
	int h = 0;
	int m;

	h = clauseset_plug_hole(vp, si, n-1);
	m = n - h;

	for (i = 0; i < m; i++) {
	    int j = GET_IX(cm[i]->cix);   // the old clause index
	    rmap[j] = i;                  // point to new index
	    cm[i]->cix = MAKE_CIX(si,i);  // set the new index
	}

	// remap implication_clauses
	// only remap level0!!! and they should be old anyways?!
#if 0
	{
	    size_t vn = dynvar_size(vp->var_map);
	    for (i = 1; i < (int)vn; i++) {
		remap_cix(&(vp->var_map[i]->implication_clause), "imp",
			  si, rmap, n);
	    }
	}
#endif
	// now map all xrefs and edges
	if (vp->opt.xref) {
	    size_t vn = dynvar_size(vp->var_map);
	    for (i = 1; i < (int)vn; i++) {
		xref_remap(&vp->var_map[i]->lit[0], si, rmap, n);
		xref_remap(&vp->var_map[i]->lit[1], si, rmap, n);
	    }
	}
	if (vp->opt.hash && (si != ALPHA)) {
	    size_t hn = dynvar_size(vp->hashtab);
	    for (i = 0; i < (int)hn; i++)
		hashtab_remap(vp, i, si, rmap, n);
	}

//	enif_fprintf(stdout, "REMAPPED clauses si=%d\n", si);
//	print_clauseset(vp, si, n);
    } STK_END0(rmap);

    return enif_make_ok(env);
}

static ERL_NIF_TERM varp_clauseset_size(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int si;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_si(env, argv[1], &si))
	return enif_make_badarg(env);
    return enif_make_uint(env, dynvec_size(vp->clauseset,si));
}

static ERL_NIF_TERM varp_clauseset_offset(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[])
{
    varp_t* vp;
    int si;
    unsigned offs;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_si(env, argv[1], &si))
	return enif_make_badarg(env);
    if (argc == 3) {
	if (!enif_get_uint(env, argv[2], &offs))
	    return enif_make_badarg(env);
	vp->coffs[si] = offs;
	return enif_make_ok(env);
    }
    return enif_make_uint(env, vp->coffs[si]);
}

static ERL_NIF_TERM varp_clauseset_first(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int si;
    int n;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_si(env, argv[1], &si))
	return enif_make_badarg(env);
    if ((n = (int)dynvec_size(vp->clauseset, si)) > 0) {
	int i = vp->coffs[si];
	clause_t** cm = vp->clauseset[si];

	while(i < n) {
	    if (cm[i] != NULL) {
		return make_cix(env, MAKE_CIX(si,i));
	    }
	    i++;
	}
    }
    return enif_make_boolean(env, false);
}

// clauseset_next ignore offset!!!
// must use clauseset_first first if offset is needed
static ERL_NIF_TERM varp_clauseset_next(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    unsigned int cix;
    int si;
    int n;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_uint(env, argv[1], &cix))
	return enif_make_badarg(env);
    si = GET_SI(cix);
    if ((n = (int)dynvec_size(vp->clauseset, si)) > 0) {
	clause_t** cm = vp->clauseset[si];
	int i = GET_IX(cix)+1;

	while(i < n) {
	    if (cm[i] != NULL) {
		return make_cix(env, MAKE_CIX(si,i));
	    }
	    i++;
	}
    }
    return enif_make_boolean(env, false);
}

//
// get_clause(Vp::varp()
//            ClauseIndex::integer(),
//            SkipLiteral::literl(),
//            Raw::boolean(),
//            AsTuple:boolean())->
//  [literal()] | true | false.
//
// returns
//     false      when contradictory
//     true       when clause is dead (contains true)
//     [L1...Ln]  a clause, without the Skip literal, if set.
//
static ERL_NIF_TERM varp_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM r;
    int raw = false;
    int skip = false;
    int skipped = false;
    int as_tuple = false;
    ERL_NIF_TERM skip_lit = ATOM(undefined);
    cix_t  cix;
    lit_t* lit;
    size_t csize;
    clause_t* cp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);

    if (argc >= 3) {
	lit_t xl;
	if (vif_get_lit(env, vp, argv[2], &xl)) {
	    skip = true;
	    skip_lit = external_l(env,xl);
	}
	else if (!enif_is_undefined(env, argv[2]))
	    return enif_make_badarg(env);

	if (argc >= 4) {
	    if (!enif_get_boolean(env, argv[3], &raw))
		return enif_make_badarg(env);
	    if (argc >= 5) {
		if (!enif_get_boolean(env, argv[4], &as_tuple))
		    return enif_make_badarg(env);
	    }
	}
    }

    if ((cp = get_clause(vp, cix)) == NULL)
	return enif_make_badarg(env);

    lit = cp->lit;
    csize = cp->size;
    r = enif_make_boolean(env, true);

    STK_BEGIN(ERL_NIF_TERM, element, csize) {
	int i, size = 0;
	for (i = 0; i < (int)csize; i++) {
	    ERL_NIF_TERM elem = external_l(env, lit[i]);
	    if (raw) { // all elemenents (but not skip)
		if (skip && (elem == skip_lit))
		    skipped = true;  // found skip_lit and skipped it
		else
		    element[size++] = elem;
	    }
	    else {  // filter constant values
		if (vp->var_lev[INDEX(lit[i])].level > 0) {
		    if (skip && (elem == skip_lit))
			skipped = true;  // found skip_lit and skipped it
		    else
			element[size++] = elem;
		}
		else {
		    switch(get_value(vp,lit[i])) {
		    case I_TRUE:
			STK_LEAVE(element);
		    case I_FALSE:  // skip FALSE constants
			break;
		    case I_UNDEF:
		    case I_BOUND:
		    default:
			if (skip && (elem == skip_lit))
			    skipped = true;
			else
			    element[size++] = elem;
			break;
		    }
		}
	    }
	}
	if (raw || (size > 0)) {
	    if (as_tuple)
		r = enif_make_tuple_from_array(env, element, size);
	    else
		r = enif_make_list_from_array(env, element, size);
	}
	else { // size=0 && raw == false
	    if (skipped) {
		if (as_tuple)
		    r = enif_make_tuple(env, 0);
		else
		    r = enif_make_list(env, 0);
	    }
	    else
		r = enif_make_boolean(env, false);  // contradictory
	}
    } STK_END(element);
    return r;
}

// sort descending variable level
static int cmp_lev QSORT_ARGS(const void* ap,const void* bp,void* arg)
{
    varp_t* vp = (varp_t*) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);
    if (a == b) return 0;
    return vp->var_lev[INDEX(b)].level - vp->var_lev[INDEX(a)].level;
}

// return {ClauseLength,Depth1,Depth2,Level2,Level3,ClauseIndex}
// Depth1 = Level1 - Level2
// Depth2 = Level2 - Level3
static ERL_NIF_TERM make_jump_info(ErlNifEnv* env, varp_t* vp, clause_t* cp)
{
    int j1,j2,j3;

    if (cp->size == 1)
	return enif_make_badarg(env);
    dynvar_resize(vp->tlit, cp->size);
    memcpy(vp->tlit, cp->lit, cp->size*sizeof(lit_t));
    // since we only need the 3 top element we could do
    // 3 bubble sorts with special case on len = 2,3
    QSORT(vp->tlit, cp->size, sizeof(lit_t), cmp_lev, vp);

    j1 = vp->var_lev[INDEX(vp->tlit[0])].level;
    j2 = vp->var_lev[INDEX(vp->tlit[1])].level;
    j3 = (cp->size == 2) ? 0 : vp->var_lev[INDEX(vp->tlit[2])].level;
    return enif_make_tuple6(env,
			    enif_make_long(env, cp->size),
			    enif_make_int(env, j1-j2),
			    enif_make_int(env, j2-j3),
			    enif_make_int(env, j2),
			    enif_make_int(env, j3),
			    make_cix(env, cp->cix));
}

// get status/length
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

    if (argv[2] == ATOM(length))
	return enif_make_long(env, cp->size);
    if (argv[2] == ATOM(jump))
	return make_jump_info(env, vp, cp);
    if (argv[2] == ATOM(status)) {
	if (cp->dead)
	    return ATOM(dead);
	else if (cp->conflict)
	    return ATOM(conflict);
	else
	    return enif_make_ok(env);
    }
    if (argv[2] == ATOM(watch)) {
	if (cp->watched)
	    return enif_make_tuple2(env,
				    enif_make_int(env, export_l(cp->lit[0])),
				    enif_make_int(env, export_l(cp->lit[1])));
	return enif_make_boolean(env, 0);
    }
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
    cp->stamp = vp->counter[BCP_COUNTER];
    return enif_make_ok(env);
}

static ERL_NIF_TERM varp_bump(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    int bump;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);    
    if (!vif_get_variable(env, vp, argv[1], &var))
	return enif_raise_exception(env, ATOM(variable));
    if (!get_bump(env, vp, argv[2], &bump))
	return enif_make_badarg(env);    
    variable_bump(vp, var, bump);
    return enif_make_ok(env);
}

static int vif_get_sub_flag(ErlNifEnv* env, ERL_NIF_TERM term, uint32_t* flag)
{
    UNUSED(env);
    if (EQUAL_KEY(env, variable, term))
	*flag = SUB_FLAG_VAR;
    else if (EQUAL_KEY(env, atom, term))
	*flag = SUB_FLAG_ATOM;
    else if (EQUAL_KEY(env, number_of_variables, term))
	*flag = SUB_FLAG_NUM_VARS;
    else if (EQUAL_KEY(env, number_of_bound_variables,term))
	*flag = SUB_FLAG_NUM_BOUND;
    else if (EQUAL_KEY(env,number_of_subst_variables,term))
	*flag = SUB_FLAG_NUM_SUBST;
    else if (EQUAL_KEY(env,number_of_clauses,term))
	*flag = SUB_FLAG_NUM_CLAUSES;
    else if (EQUAL_KEY(env,number_of_dead_clauses,term))
	*flag = SUB_FLAG_NUM_DEAD;
    else if (EQUAL_KEY(env,max_level,term))
	*flag = SUB_FLAG_MAX_LEVEL;
    else if (EQUAL_KEY(env,max_bound,term))
	*flag = SUB_FLAG_MAX_BOUND;
    else if (EQUAL_KEY(env, min_level, term))
	*flag = SUB_FLAG_MIN_LEVEL;
    else if (EQUAL_KEY(env, number_of_conflicts, term))
	*flag = SUB_FLAG_NUM_CONFL;
    else if (EQUAL_KEY(env, number_of_propagations, term))
	*flag = SUB_FLAG_NUM_PROP;
    else if (EQUAL_KEY(env, number_of_decisions, term))
	*flag = SUB_FLAG_NUM_DECI;
    else if (EQUAL_KEY(env, number_of_bcps, term))
	*flag = SUB_FLAG_NUM_BCP;    
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

    if ((sp = obj_alloc(&vp->sub_allocator)) == NULL)
	return enif_make_badarg(env);
    r = enif_monitor_process(env, vp, enif_self(env,&sp->pid), &sp->mon);
    if (r != 0) {
	// r < 0 no down callback, r > 0 process not alive
	obj_free(&vp->sub_allocator, sp);
	return enif_make_badarg(env);
    }
    sp->flags = flags;
    dlist_insert_first(&vp->subs, sp);
    return enif_make_ok(env);
}

static ERL_NIF_TERM varp_get_clauses(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    ERL_NIF_TERM list;
    lit_t xl;
    literal_t* lp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_l(env, vp, argv[1], &xl))
	return enif_make_badarg(env);

    lp = l2ll(vp, xl);
    list = enif_make_list(env, 0);

    if (argv[2] == ATOM(watch)) {
	wlink_t* wl = lp->wlist;
	while(wl != NULL) {
	    clause_t* cp = clause_pointer(wl);
	    ERL_NIF_TERM elem = make_cix(env, cp->cix);
	    list = enif_make_list_cell(env, elem, list);
	    wl = wl->next;
	}
    }
    else if (argv[2] == ATOM(literal)) {
	cix_t* xptr = dynarray_element(lp->xref, 0);
	size_t  xlen = dynarray_size(lp->xref);
	while(xlen--) {
	    if (get_clause(vp, *xptr) != NULL) {
		ERL_NIF_TERM elem = make_cix(env, *xptr);
		list = enif_make_list_cell(env, elem, list);
	    }
	    xptr++;
	}
    }
    else if (argv[2] == ATOM(variable)) {
	variable_t* var = var_l(vp, xl);
	int i;

	for (i = 0; i < 2; i++) {
	    cix_t* xptr = dynarray_element(var->lit[i].xref, 0);
	    cix_t  xlen = dynarray_size(var->lit[i].xref);
	    while(xlen--) {
		if (get_clause(vp, *xptr) != NULL) {
		    ERL_NIF_TERM elem = make_cix(env, *xptr);
		    list = enif_make_list_cell(env, elem, list);
		}
		xptr++;
	    }
	}
    }
    else
	return enif_make_badarg(env);
    return list;
}

// Get first literal in queue
static ERL_NIF_TERM varp_queue_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (dynvar_size(vp->q) > 0)
	return make_lit(env, vp->q[0]);
    else
	return enif_make_boolean(env, false);
}

// Get next literal in queue (debug)
static ERL_NIF_TERM varp_queue_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    size_t size;
    lit_t xl;
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xl))
	return enif_make_badarg(env);
    if ((size = dynvar_size(vp->q)) > 1) {
	size--;
	for (i = 0; i < (int)size; i++) {
	    if (vp->q[i] == xl)
		return make_lit(env, vp->q[i+1]);
	}
    }
    return enif_make_boolean(env, false);
}

// Clear the literal queue
static ERL_NIF_TERM varp_queue_clear(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    lqueue_clear(vp);
    return enif_make_boolean(env, true);
}

// get_descision(Vp, Level)
// return decision "literal" on Level

static ERL_NIF_TERM varp_get_decision(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0) || (level > vp->level))
	return enif_make_badarg(env);
    if (vp->bnd[level].decision == LIT_FALSE)
	return enif_make_boolean(env, false);
    else
	return enif_make_int(env, export_l(vp->bnd[level].decision));
}

// get_undo_state(Vp, Level)
// return undo state on Level

static ERL_NIF_TERM varp_get_undo_state(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0) || (level > vp->level))
	return enif_make_badarg(env);
    return enif_make_string(env, bnd_state_name[vp->bnd[level].t],
			    ERL_NIF_LATIN1);
}

//
// get_bindings(Vp, [Level,[Trail[, Tuple]]]) -> [binding()]
//
static ERL_NIF_TERM varp_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    int as_trail    = false;
    int as_tuple    = true;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    level = vp->level;
    if (argc >= 2) {
	if (!enif_get_int(env, argv[1], &level) || (level<0))
	    return enif_make_badarg(env);
	if (argc >= 3) {
	    if (!enif_get_boolean(env, argv[2], &as_trail))
		return enif_make_badarg(env);
	    if (argc >= 4) {
		if (!enif_get_boolean(env, argv[3], &as_tuple))
		    return enif_make_badarg(env);
	    }
	}
    }
    if (level <= vp->level) {
	int size   = vp->bnd[level].size;
	lit_t* bpv = bindings_at(vp, level);
	ERL_NIF_TERM r;
	STK_BEGIN(ERL_NIF_TERM,element,size) {
	    int i = as_trail ? 0 : size-1;
	    int s  = as_trail ? 1 : -1;
	    int j;
	    for (j = size-1; j >= 0; j--) {
		element[i] = make_lit(env,bpv[j]);
		i += s;
	    }
	    if (as_tuple)
		r = enif_make_tuple_from_array(env, element, size);
	    else
		r = enif_make_list_from_array(env, element, size);
	} STK_END0(element);
	return r;
    }
    if (as_tuple)
	return enif_make_tuple(env, 0);
    else
	return enif_make_list(env, 0);
}

//
// get_nbindings(Vp, Count, [Trail[, Tuple]]) ->
//    [binding()]
//
static ERL_NIF_TERM varp_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int count;
    int level;
    int as_trail    = false;
    int as_tuple    = true;    
    ERL_NIF_TERM r;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &count) || (count < 0))
	return enif_make_badarg(env);
    if (argc >= 3) {
	if (!enif_get_boolean(env, argv[2], &as_trail))
	    return enif_make_badarg(env);
	if (argc >= 4) {
	    if (!enif_get_boolean(env, argv[3], &as_tuple))
		return enif_make_badarg(env);
	}
    }
    
    STK_BEGIN(ERL_NIF_TERM, elements, count) {
	int j = 0;
	if (as_trail) {  // first binding first
	    int remain = count;
	    level = 0;
	    while((level <= vp->level) && (remain > 0)) {
		lit_t* bpv = bindings_at(vp,level);
		int n = vp->bnd[level].size;
		int i = 0;
		while(remain-- && (i < n)) {
		    elements[j++] = make_lit(env,bpv[i++]);
		}
		level++;
	    }
	}
	else { // Last bindings first
	    int remain = count;
	    level = vp->level;
	    while((level >= 0) && (remain > 0)) {
		lit_t* bpv = bindings_at(vp, level);
		int n = vp->bnd[level].size;
		int i = n;
		while(remain-- && (i >= 0)) {
		    elements[j++] = make_lit(env,bpv[--i]);
		}
		level--;
	    }
	}
	if (as_tuple)
	    r = enif_make_tuple_from_array(env, elements, j);
	else
	    r = enif_make_list_from_array(env, elements, j);	
    } STK_END0(elements);
    return r;
}

// get_number_of_bindings(Vp, Level) -> unsigned()
// return number of bindings on Level

static ERL_NIF_TERM varp_get_number_of_bindings(ErlNifEnv* env, int argc,
						const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level < 0) ||
	(level >= (int)dynvar_size(vp->bnd)))
	return enif_make_badarg(env);
    return enif_make_uint(env, vp->bnd[level].size);
}

static ERL_NIF_TERM varp_unmark(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    unmark_all(vp);
    return enif_make_ok(env);
}

// Mark, with mark0 list of literals, tuple of literals or bindings
// on a level optionally concat, do not clear marks before assigning new
static ERL_NIF_TERM varp_mark(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int arity;
    int level;
    int unmark = true;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (argc >= 3) {
	if (!enif_get_boolean(env, argv[2], &unmark))
	    return enif_make_badarg(env);
    }

    if (unmark)
	unmark_all(vp);

    if (enif_get_int(env, argv[1], &level)) {
	if ((level < 1) || (level >= (int)dynvar_size(vp->bnd)))
	    return enif_make_badarg(env);
	else {
	    size_t size = vp->bnd[level].size;
	    lit_t* bpv = bindings_at(vp, level);
	    int i;
	    for (i = 0; i < (int)size; i++) {
		lit_t xl = bpv[i];
		mark0_lit(vp, xl);
	    }
	}
    }
    else if (!vif_load_tlit(env, vp, &arity, argv[1]))
	return enif_make_badarg(env);
    else {
	int i;
	for (i = 0; i < arity; i++)
	    mark0_lit(vp, vp->tlit[i]);
    }
    return enif_make_ok(env);
}


// remove elements not marked with both mark0 and mark1 and
// remove mark1 in case an element as both mark0 and mark1
static void intersect_marked(varp_t* vp)
{
    size_t nmarked = dynvar_size(vp->mark_stack);
    int i = 0;

    while(i < (int)nmarked) {
	lit_t vl = vp->mark_stack[i];
	if (is_marked(vp, vl, VAR_MARK0|VAR_MARK1)) {
	    // both mark 0 and 1 - retain only mark 0
	    clr_mark(vp, vl, VAR_MARK1);
	    i++;
	}
	else {
	    // remove element i
	    clr_mark(vp, vl, VAR_MARKL|VAR_MARK0|VAR_MARK1|VAR_MARKN);
	    // shrink stack by swapping in last element
	    vp->mark_stack[i] = vp->mark_stack[nmarked-1];
	    nmarked--;
	}
    }
    dynvar_resize(vp->mark_stack, nmarked);
}

// Mark all literals that are marked as mark0 with mark1 (markn is checked)
// Then marked variables with both mark0 and mark1 are kept and
// marked as mark0 together with markn flags, other marks are removed
//
static ERL_NIF_TERM varp_intersect_marks(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int arity;
    int level;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (enif_get_int(env, argv[1], &level)) {
	if ((level < 1) || (level >= (int)dynvar_size(vp->bnd)))
	    return enif_make_badarg(env);
	else {
	    size_t size = vp->bnd[level].size;
	    lit_t* bpv = bindings_at(vp, level);
	    int i;
	    for (i = 0; i < (int)size; i++) {
		lit_t xl = bpv[i];
		add_mark1_lit(vp, xl);
	    }	    
	}
    }
    else {
	int i;
	if (!vif_load_tlit(env, vp, &arity, argv[1]))
	    return enif_make_badarg(env);
	for (i = 0; i < arity; i++) {
	    add_mark1_lit(vp, vp->tlit[i]);
	}
    }
    intersect_marked(vp);
    return enif_make_ok(env);
}

// return a list/tuple of literals that are marked with mark0 (|markn)
static ERL_NIF_TERM varp_get_marked(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int tuple = false;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[1], &tuple))
	return enif_make_badarg(env);
    {
	size_t size = dynvar_size(vp->mark_stack);
	ERL_NIF_TERM r;
	STK_BEGIN(ERL_NIF_TERM, elements, size) {
	    int i;
	    int j = 0;
	    for (i = 0; i < (int)size; i++) {
		lit_t vl = vp->mark_stack[i];
		if (is_marked(vp, vl, VAR_MARK0)) {
		    if (is_marked(vp, vl, VAR_MARKN))
			vl = L_NEG(vl);
		    elements[j++] = make_lit(env, vl);
		}
	    }
	    if (tuple)
		r = enif_make_tuple_from_array(env,elements,j);
	    else
		r = enif_make_list_from_array(env,elements,j);
	} STK_END0(elements);
	return r;
    }
}

static int mark_intersect_var(ErlNifEnv* env, varp_t* vp,
			      ERL_NIF_TERM var,
			      const ERL_NIF_TERM* elem0,
			      ERL_NIF_TERM* element,
			      size_t size0)
{
    int i;
    int j = 0;

    for (i = 0; i < (int)size0; i++) {
	ERL_NIF_TERM x = elem0[i];
	lit_t xl;
	lit_t vl;
	if (!vif_get_lit(env, vp, x, &xl))
	    return -1;
	vl = L_VAR(xl);
	if (is_marked(vp, vl, VAR_MARK0)) {
	    int neg = is_marked(vp, vl, VAR_MARKN);
	    if (neg == is_neg_l(xl))
		element[j++] = x;
	    else {
		ERL_NIF_TERM nx = make_lit(env, neg_l(xl));
		element[j++] = enif_make_tuple2(env, var, nx);
	    }
	}
    }
    return j;
}

static ERL_NIF_TERM varp_intersect_var(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    const ERL_NIF_TERM* elem0;
    int arity;
    int level;
    unsigned len;
    ERL_NIF_TERM var;
    lit_t x;
    int as_tuple = false;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    var = argv[1];
    if (!vif_get_lit(env, vp, argv[1], &x))
	enif_raise_exception(env, ATOM(literal));
    if (!enif_get_boolean(env, argv[3], &as_tuple))
	return enif_make_badarg(env);

    if (enif_get_int(env, argv[2], &level)) {
	if ((level < 1) || (level >= (int)dynvar_size(vp->bnd)))
	    return enif_make_badarg(env);
	else {
	    size_t n = vp->bnd[level].size;
	    lit_t* bpv = bindings_at(vp, level);
	    int size = 0;
	    ERL_NIF_TERM r;

	    STK_BEGIN(ERL_NIF_TERM, element, n) {
		int j = n;
		int i;
		for (i = n-1; i >= 0; i--) {
		    lit_t xl = bpv[i];
		    lit_t vl = L_VAR(xl);
		    if (is_marked(vp, vl, VAR_MARK0)) {
			int neg = is_marked(vp, vl, VAR_MARKN);
			if (neg == is_neg_l(xl)) {
			    element[--j] = make_lit(env, xl);
			    size++;
			}
			else {
			    ERL_NIF_TERM nx = make_lit(env, neg_l(xl));
			    element[--j] = enif_make_tuple2(env, var, nx);
			    size++;
			}
		    }
		}
		if (as_tuple)
		    r = enif_make_tuple_from_array(env,&element[j],size);
		else
		    r = enif_make_list_from_array(env,&element[j],size);
	    } STK_END0(element);
	    return r;	    
	}
    }
    else if (enif_get_tuple(env, argv[2], &arity, &elem0)) { // as tuple
	int size;
	ERL_NIF_TERM r;
	STK_BEGIN(ERL_NIF_TERM, element, arity) {
	    if ((size=mark_intersect_var(env,vp,var,elem0,element,arity)) < 0) {
		r = enif_make_badarg(env);
		STK_LEAVE(element);
	    }
	    if (as_tuple)
		r = enif_make_tuple_from_array(env,element,size);
	    else
		r = enif_make_list_from_array(env, element, size);
	} STK_END(element);
	return r;
    }
    else if (enif_get_list_length(env, argv[2], &len)) { // as list
	ERL_NIF_TERM r;
	STK_BEGIN(ERL_NIF_TERM, elem, len) {
	    STK_BEGIN(ERL_NIF_TERM, element1, len) {
		ERL_NIF_TERM list;
		ERL_NIF_TERM head, tail;
		int i = 0;
		int size;

		list = argv[2];
		while(enif_get_list_cell(env, list, &head, &tail)) {
		    elem[i++] = head;
		    list = tail;
		}
		ASSERT(i == (int)len);
		if ((size=mark_intersect_var(env,vp,var,elem,element1,len))<0)
		    r = enif_make_badarg(env);
		else {
		    if (as_tuple)
			r = enif_make_tuple_from_array(env, element1, size);
		    else
			r = enif_make_list_from_array(env, element1, size);
		}
	    } STK_END0(element1);
	} STK_END0(elem);
	return r;
    }
    else
	return enif_make_badarg(env);
}

// return a 32 bit random number 
static ERL_NIF_TERM varp_rand(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);    
    return enif_make_uint64(env, arc4_random(&vp->as));
}


// lookup varp only
static ERL_NIF_TERM varp_noop(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    return enif_make_ok(env);
}

// create all tracing NIFs
#ifdef NIF_TRACE

static void trace_print_arg_list(ErlNifEnv* env,int argc,const ERL_NIF_TERM argv[])
{
    enif_fprintf(stdout, "(");
    if (argc > 0) {
	int i;
	if (enif_is_ref(env, argv[0]))
	    enif_fprintf(stdout, "$VP");
	else
	    enif_print(stdout, argv[0]);
	for (i = 1; i < argc; i++) {
	    enif_fprintf(stdout, ",");
	    enif_print(stdout, argv[i]);
	}
    }
    enif_fprintf(stdout, ")");
}

#define NIF(name, arity, func) \
static ERL_NIF_TERM trace##_##func##_##arity(ErlNifEnv* env, int argc,const ERL_NIF_TERM argv[]) \
{ \
    ERL_NIF_TERM result;					\
    enif_fprintf(stdout, "ENTER %s", (name));			\
    trace_print_arg_list(env, argc, argv);			\
    enif_fprintf(stdout, "\r\n");				\
    result = func(env, argc, argv);				\
    enif_fprintf(stdout, "  RESULT=%T\r\n", (result));		\
    enif_fprintf(stdout, "LEAVE %s\r\n", (name));		\
    return result;						\
}

NIF_LIST
#undef NIF

#endif


static void load_atoms(ErlNifEnv* env)
{
    LOAD_ATOM(alpha);
    LOAD_ATOM(beta);
    LOAD_ATOM(atom);
    LOAD_ATOM(bcp_counter);
    LOAD_ATOM(clause_2_counter);
    LOAD_ATOM(clause_3_counter);
    LOAD_ATOM(clause_d_counter);
    LOAD_ATOM(clause_n_counter);
    LOAD_ATOM(clause_m_counter);
    LOAD_ATOM(conflict_counter);
    LOAD_ATOM(propagation_counter);
    LOAD_ATOM(decision_counter);
    LOAD_ATOM(mark_counter);    
    LOAD_ATOM(conflict);
    LOAD_ATOM(dead);
    LOAD_ATOM(default);
    LOAD_ATOM(delta);
    LOAD_ATOM(done);
    LOAD_ATOM(error);
    LOAD_ATOM(false);
    LOAD_ATOM(fifo);
    LOAD_ATOM(flags);
    LOAD_ATOM(gamma);
    LOAD_ATOM(hash);
    LOAD_ATOM(implication);
    LOAD_ATOM(implication_clause);
    LOAD_ATOM(inqueue);
    LOAD_ATOM(is_atom);
    LOAD_ATOM(is_used);
    LOAD_ATOM(jump);
    LOAD_ATOM(length);
    LOAD_ATOM(level);
    LOAD_ATOM(lifo);
    LOAD_ATOM(literal);
    LOAD_ATOM(literal_integer);
    LOAD_ATOM(literal_size);
    LOAD_ATOM(local);
    LOAD_ATOM(global);
    LOAD_ATOM(mark);
    LOAD_ATOM(max_bound);
    LOAD_ATOM(max_conflicting);
    LOAD_ATOM(max_level);
    LOAD_ATOM(min_level);
    LOAD_ATOM(number_of_bound_variables);
    LOAD_ATOM(number_of_clauses);
    LOAD_ATOM(number_of_conflicting_clauses);
    LOAD_ATOM(number_of_dead_clauses);
    LOAD_ATOM(number_of_learnt_clauses);
    LOAD_ATOM(number_of_subst_variables);
    LOAD_ATOM(number_of_unbound_variables);
    LOAD_ATOM(number_of_variables);
    LOAD_ATOM(number_of_conflicts);
    LOAD_ATOM(number_of_propagations);
    LOAD_ATOM(number_of_decisions);
    LOAD_ATOM(number_of_bcps);
    LOAD_ATOM(off);
    LOAD_ATOM(phase);
    LOAD_ATOM(init_phase);
    LOAD_ATOM(qtype);
    LOAD_ATOM(queue);
    LOAD_ATOM(recursive);
    LOAD_ATOM(reset);
    LOAD_ATOM(set);
    LOAD_ATOM(size);
    LOAD_ATOM(status);
    LOAD_ATOM(symbol);
    LOAD_ATOM(system_limit);
    LOAD_ATOM(memory_limit);    
    LOAD_ATOM(toggle);
    LOAD_ATOM(true);
    LOAD_ATOM(turbo);
    LOAD_ATOM(undefined);
    LOAD_ATOM(unit);
    LOAD_ATOM(use);
    LOAD_ATOM(use_phase);
    LOAD_ATOM(all_used);
    LOAD_ATOM(value_packing);
    LOAD_ATOM(variable);
    LOAD_ATOM(varp);
    LOAD_ATOM(watch);
    LOAD_ATOM(xref);
    LOAD_ATOM(vsids);
    LOAD_ATOM(none);
    LOAD_ATOM(log2);
    LOAD_ATOM(log10);
    // LOAD_ATOM(rank);
    LOAD_ATOM(next);
    LOAD_ATOM(version);
    LOAD_ATOM(seed);
    LOAD_ATOM_STRING(exclamation_mark, "!");
    LOAD_ATOM(identity);
    LOAD_ATOM_STRING(p_identity, "+identity");
    LOAD_ATOM_STRING(n_identity, "-identity");
    LOAD_ATOM_STRING(e_identity, "=identity");
    LOAD_ATOM(random);
    LOAD_ATOM_STRING(p_random, "+random");
    LOAD_ATOM_STRING(n_random, "-random");
    LOAD_ATOM_STRING(e_random, "=random");
    LOAD_ATOM(degree);
    LOAD_ATOM_STRING(p_degree, "+degree");
    LOAD_ATOM_STRING(n_degree, "-degree");
    LOAD_ATOM_STRING(e_degree, "=degree");
    LOAD_ATOM(rank);
    LOAD_ATOM_STRING(p_rank, "+rank");
    LOAD_ATOM_STRING(n_rank, "-rank");
    LOAD_ATOM_STRING(e_rank, "=rank");

    LOAD_ATOM(memory_literal_size);
    LOAD_ATOM(memory_clause_size);
    LOAD_ATOM(memory_variable_size);
    LOAD_ATOM(memory_symbol_size);
    LOAD_ATOM(memory_size);    
}

static void varp_down(ErlNifEnv* env, void* obj,
		      ErlNifPid* pid, ErlNifMonitor* mon)
{
    UNUSED(env);
    UNUSED(pid);
    varp_t* vp = (varp_t*) obj;
    subscription_t* sp = dlist_first(&vp->subs);

    DBG("varp_down called\r\n");

    while(sp != NULL) {
	if (enif_compare_monitors(mon, &sp->mon) == 0) {
#ifdef DEBUG
	    char buf[80];
	    enif_snprintf(buf, sizeof(buf), "process %T died",
			  enif_make_pid(env, &sp->pid));
	    enif_fprintf(stdout, "%s\r\n", buf);
#endif
	    dlist_remove(&vp->subs, sp);
	    obj_free(&vp->sub_allocator, sp);
	    return;
	}
	sp = dlist_next(sp);
    }
}

static void varp_dtor(ErlNifEnv* env, void* obj)
{
    UNUSED(env);
    varp_t* vp = (varp_t*) obj;

    DBG("dtor\r\n");
    cleanup(vp);
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

    DBG("varp_load called\r\n");

    xnif_init(env);

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

    DBG("varp_upgrade called\r\n");

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
    DBG("varp_unload called\r\n");
}

ERL_NIF_INIT(varp_nif, varp_funcs,
	     varp_load, NULL,
	     varp_upgrade, varp_unload)
