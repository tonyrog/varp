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
#include <stddef.h>
#include <errno.h>
#include <memory.h>
#include <limits.h>
#include <sys/time.h>
#include <math.h>
#include <float.h>
#include "erl_nif.h"

#include "cdlist.h"
#include "slist.h"
#include "dlist.h"

#include "xnif_funcs.h"

#define EPSILON (4*FLT_EPSILON) // 1.19e-07

//
// configurations
// NIF_TRACE
// TWL_BACKWARD      
// ASSERTIONS         various sanity test in runtime (during test)
// DEBUG              various output during debug
// DEBUG_MEM          special wrapped allocators to find leaks etc
// FENCE_MEM          set data patterns around allocated memory
// DEBUG_BCP          print clauses during bcp
// DEBUG_NBCP         print level information during nbcp
// DEBUG_ORDER        print order handling info
// VALIDATE_TWL       check TWL data structures after clause changes
// LIT_INTEGER        literals are represented as integers, size=8,16,32
// LIT_VALUE          store literal values instead of variable value
// PACKED_VALUE       two bit values in separate vector size=1,4 per byte
//
// #define NIF_TRACE
#define TWL_BACKWARD
#define LIT_INTEGER 32
#define LIT_VALUE
#define PACKED_VALUE 1
// #define ASSERTIONS
// #define DEBUG
// #define DEBUG_BCP
// #define DEBUG_NBCP
// #define DEBUG_ORDER
// #define DEBUG_EDGE
// #define DEBUG_MEM
// #define FENCE_MEM
// #define VALIDATE_TWL
// #define VALIDATE_ORDER
// #define VALIDATE_MODEL

// #define COUNT(vp, cnt)
#define COUNT(vp, cnt) vp->counter[(cnt)]++


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

typedef enum {
    lifo = 0,
    fifo = 1,
    recursive = 2
} qtype_t;

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
#define MAKE_LIT(v,neg) (((v)<<1)+(neg))

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

#define DBG1(args...) enif_fprintf(stdout, args)
#define DBG0(args...)

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

#if defined(DEBUG_NBCP)
#define DBG_NBCP(args...) enif_fprintf(stdout, args)
#else
#define DBG_NBCP(args...)
#endif

#if defined(DEBUG_ORDER)
#define DBG_ORDER(args...) enif_fprintf(stdout, args)
#else
#define DBG_ORDER(args...)
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
    NIF( "value",               2,  varp_value )	\
    NIF( "bind",                2,  varp_bind )		\
    NIF( "bind",                3,  varp_bind )		\
    NIF( "decide",              2,  varp_decide )	\
    NIF( "decide",              3,  varp_decide )       \
    NIF( "subst",               3,  varp_subst )	      \
    NIF( "implication_clause",  2,  varp_implication_clause ) \
    NIF( "implication_level",   2,  varp_implication_level )  \
    NIF( "implication_pos",     2,  varp_implication_pos )    \
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
    NIF( "bcp",                 2,  varp_bcp )	\
    NIF( "bcp",                 3,  varp_bcp )	\
    NIF( "nbcp",                1,  varp_nbcp ) \
    NIF( "add_clause",          2,  varp_add_clause ) \
    NIF( "add_clause",          3,  varp_add_clause ) \
    NIF( "get_clause",          2,  varp_get_clause ) \
    NIF( "get_clause",          3,  varp_get_clause ) \
    NIF( "get_clause",          4,  varp_get_clause ) \
    NIF( "find_clause",         2,  varp_find_clause ) \
    NIF( "compress_clause",     2,  varp_compress_clause )  \
    NIF( "clause_info",         3,  varp_clause_info )  \
    NIF( "variable_info",       3,  varp_variable_info )  \
    NIF( "literal_info",        3,  varp_literal_info ) \
    NIF( "del_clause",          2,  varp_del_clause )  \
    NIF( "clean_clause",        2,  varp_clean_clause )  \
    NIF( "clean_edges",         2,  varp_clean_edges )  \
    NIF( "get_clauses",         3,  varp_get_clauses ) \
    NIF( "get_decision",        2,  varp_get_decision ) \
    NIF( "get_undo_state",      2,  varp_get_undo_state ) \
    NIF( "get_bindings",        5,  varp_get_bindings ) \
    NIF( "get_nbindings",       4,  varp_get_nbindings ) \
    NIF( "get_number_of_bindings", 2,  varp_get_number_of_bindings ) \
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
    NIF( "use_clause",          2,  varp_use_clause ) \
    NIF( "bump",                3,  varp_bump )     \
    NIF( "subscribe",           2,  varp_subscribe ) \
    NIF( "clauseset_size",      2,  varp_clauseset_size ) \
    NIF( "clauseset_offset",    2,  varp_clauseset_offset ) \
    NIF( "clauseset_offset",    3,  varp_clauseset_offset ) \
    NIF( "clauseset_sort",      2,  varp_clauseset_sort )   \
    NIF( "clauseset_first",     2,  varp_clauseset_first )  \
    NIF( "clauseset_next",      2,  varp_clauseset_next )   \
    NIF( "set_user_count",      3,  varp_set_user_count ) \
    NIF( "conflict",            4,  varp_conflict ) \
    NIF( "minimize",            2,  varp_minimize ) \
    NIF( "move_clause",         3,  varp_move_clause ) \
    NIF( "mark_literals",       2,  varp_mark_literals ) \
    NIF( "mark_intersect",      2,  varp_mark_intersect ) \
    NIF( "mark_intersect_var",  4,  varp_mark_intersect_var ) \
    NIF( "get_marked",          2,  varp_get_marked)

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
    slink_t  link;              // next heap block link
    uint8_t* current;           // must be aligned
    uint8_t* end;
    uint8_t base[0];
} heap_t;

#ifdef DEBUG_MEM
struct _object_t;

typedef struct _object_link_t
{
    dlink_t link;
    struct _object_t* obj;
} object_link_t;

#define OBJECT_LINK \
    cdlink_t link; \
    object_link_t* olink
#else

#define OBJECT_LINK \
    cdlink_t link
#endif

// objects may be slist/dlist or cdlist
typedef struct _object_t
{
    OBJECT_LINK;
    uint8_t data[];
} object_t;

typedef struct _allocator_t
{
    size_t size;         // object size
    slist_t heap_list;   // heaps of data
    slist_t free_list;   // list of free objects
#ifdef DEBUG_MEM
    dlist_t obj_list;    // list of object links
#endif
} allocator_t;

#define DYN_SYMTAB_INIT  8
#define DYN_HASHTAB_INIT 8
#define DYN_UNDO_INIT    8 // 1024 at least 1 level 0 exit from start!

// Grow factor
#define DYN_GROW0 2.0000
#define DYN_GROW1 1.6180
#define DYN_GROW2 1.2500

// switch limit
#define DYN_GROW0_LIMIT 1024
#define DYN_GROW1_LIMIT (1024*1024)

#define DYN_ADDR(dp,i) ((void*)((intptr_t)((dp)->base) + ((i)*(dp)->width)))

typedef struct _dyntype_t
{
    const char* name;
    size_t width;
} dyntype_t;

typedef struct _dynarray_t // :object_t
{
    OBJECT_LINK;
    const char* name;  // debugging name of array
    size_t capacity;   // max number of elements
    size_t size;       // assigned size <= capacity
    size_t width;      // element size
    void*  base;       // array base address
} dynarray_t;

// Simple variable fiels

#define dynvar(type, name)			\
    dynarray_t name ## _dyn_;			\
    type name

#define dynvar_size(name) name ## _dyn_.size
#define dynvar_capacity(name) name ## _dyn_.capacity
#define dynvar_init(name, size)			\
    ((dynarray_init(&name ## _dyn_, #name, (size), sizeof(name[0])) < 0) ? -1 : \
     (name = name ## _dyn_.base, 0))
#define dynvar_resize(name, size)				\
    ((dynarray_resize(&name ## _dyn_, (size)) < 0) ? -1 :	\
     (name = name ## _dyn_.base, 0))
#define dynvar_set_capacity(name, size)				\
    ((dynarray_set_capacity(&name ## _dyn_, (size)) < 0) ? -1 :	\
     (name = name ## _dyn_.base, 0))
#define dynvar_add(name)			\
    (dynarray_add(&name ## _dyn_), name = name ## _dyn_.base,		\
     (__typeof__(name[0])*) DYN_ADDR(&name ## _dyn_, name ## _dyn_.size -1))
#define dynvar_clear(name)			\
    (dynarray_clear(&name ## _dyn_), name = NULL)

// Array variable fiels
    
#define dynvec(type,name,n)			\
    dynarray_t name ## _dyn_[n];		\
    type name[n]

#define dynvec_size(name,i) name ## _dyn_[(i)].size
#define dynvec_capacity(name,i) name ## _dyn_[(i)].capacity
#define dynvec_init(name,i,vtag,size)					\
    ((dynarray_init(&name ## _dyn_[(i)], #name vtag,(size),sizeof(name[(i)][0])) < 0) ? -1 : \
     (name[(i)] = name ## _dyn_[(i)].base, 0))
#define dynvec_resize(name,i,size)				\
    ((dynarray_resize(&name ## _dyn_[(i)], (size)) < 0) ? -1 :	\
     (name[(i)] = name ## _dyn_[(i)].base, 0))
#define dynvec_set_capacity(name,i,size)			\
    ((dynarray_set_capacity(&name ## _dyn_[(i)], (size)) < 0) ? -1 :	\
     (name[(i)] = name ## _dyn_[(i)].base, 0))
#define dynvec_add(name,i)				\
    (__typeof__(name[(i)][0])*) dynarray_add(&name ## _dyn_[(i)])
#define dynvec_clear(name,i)				\
    (dynarray_clear(&name ## _dyn_[(i)]), name[(i)] = NULL)

    
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

#define LIT_FLAG_Q  0x01   // literal in Q

typedef struct _literal_t // :slink_t
{
    slink_t  qlink;            // literal_t is a slink (element in slist)
    bool_t   neg;              // is_negated
    uint8_t  flags;            // LIT_FLAG_Q ...
    uint32_t user;             // user count for sorting
    ulit_t    l;               // integer literal code
#if defined(LIT_VALUE) && !defined(PACKED_VALUE)
    ival_t    ivalue;
#endif
    struct _variable_t* var;   // "parent"
    struct _wlink_t* wlist;    // list of watch positions
    struct _edge_t* elist;     // list of 2-clause triggers
    dynarray_t* xref;          // cross references when enabled
} literal_t;

typedef uint32_t cix_t;             // clause index type <<set:2,index:30>>
typedef int32_t  pos_t;             // literal position type (-1 = invalid)
#define CLAUSE_NONE  ((cix_t) -1)
#define CLAUSE_TRUE  ((cix_t) -2)   // never stored, just returned
#define CLAUSE_FALSE ((cix_t) -3)   // never stored, just returned
#define MAKE_CIX(si,ix)  (((si)<<30)|(ix))
#define GET_SI(cix)      ((int)(((cix)>>30) & 3))
#define GET_IX(cix)      ((cix)&0x3FFFFFFF)

typedef struct _xref_t
{
    cix_t cix;
    pos_t p;
} xref_t;

typedef struct _edge_t // :object_t
{
    OBJECT_LINK;
    cix_t    cix;            // real 2-clause    
    lit_t l;
} edge_t;

#define MARK0        0x01  // first mark
#define MARK1        0x02  // second mark
#define MARKS        0x03  // all marks
#define MARKN        0x04  // negative
#define MARKL        0x80  // on-list

#define LIT_POS 0
#define LIT_NEG 1

typedef struct _variable_t     // :object_t
{
    OBJECT_LINK;               // used as cdlink (ordered link)
    struct _variable_t* bound_next;
    struct _variable_t* mark_next; // mark next
    bool_t  is_atom;          // variable marked as input/atom
    uint8_t mark;             // mark0/mark1/markn...
    uint8_t flags;
    literal_t* bound;          // if bound/subst this is the bound literal
#if !defined(LIT_VALUE) && !defined(PACKED_VALUE)
    ival_t    ivalue;
#endif
    ival_t    phase;           // last set value (or by sort) def=opt.init_pase
    int ix;                    // variable index
    cix_t implication_clause;  // implication clause index
    pos_t literal_pos;         // position in implication clause
    int  level;                // implication clause level
    char* strname;             // string formated name or NULL
    struct _symbol_t* names;   // list of aliases
    literal_t lit[2];          // literal containers LIT_POS=0 LIT_NEG=1
} variable_t;

typedef struct _symbol_t // :object_t
{
    OBJECT_LINK;              
    struct _symbol_t* anext;  // alias link
    uint32_t hvalue;          // symbol hash
    bool_t is_term;           // either name is a term or name is binary string
    uint8_t* data;            // raw data
    size_t   size;            // raw len
    variable_t*  var;
} symbol_t;

typedef struct _wlink_t
{
    struct _wlink_t* next;
    // FIXME: store literal here in case of 2-clause! 
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
    uint8_t    select;       // case select: 0=unit-clause, 1=2-clause,
                             // 2=3-clause, 3=n_clause
    struct _clause_t* uwatch;// clauses to unwatch
    uint64_t stamp;          // last used time (bcp_counter clock)
    uint32_t hvalue;         // clause hash value
    lit_t lit[];             // literal array
} clause_t;

// hash structure
typedef struct _hlink_t // :object_t
{
    OBJECT_LINK;
    uint32_t hvalue;
    cix_t cix;
} hlink_t;

typedef enum {
    uUNDEF   = 0,
    uSET     = 1,
    uTOGGLE  = 2,
    uDONE    = 3
} undo_state_t;

typedef struct _undo_t
{
    lit_t decision;      // decision literal from bind (last among bs)
    undo_state_t t;
    size_t      size;    // length of list
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
#define SUB_FLAG_NUM_CLAUSES 0x0040    // report number of clauses
#define SUB_FLAG_NUM_DEAD    0x0080    // report number of dead clauses
#define SUB_FLAG_MAX_LEVEL   0x0100    // report max level sinc last
#define SUB_FLAG_MAX_BOUND   0x0200    // report max bound variables since last
#define SUB_FLAG_NUM_SUBST   0x0400    // report number of susbstitutions
#define SUB_FLAG_MIN_LEVEL   0x0100    // report min level (at conflict)

typedef struct _subscription_t {   // :object_t
    OBJECT_LINK;
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
    bool_t   edge;       // keep edge list for 2-clauses
    bool_t   use_phase;  // use saved phase
    ival_t   init_phase; // initial phase selection
    size_t   vsize;
    size_t   csize;
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

    uint32_t cdead;           // number of dead clauses (level=0)
    uint32_t edead;           // number of dead edges (level=0)    
    uint32_t nedge;           // number of edges in use
    
    int num_conflicting;      // number of conflicting clauses saved
    int max_conflicting;      // max number of conflicting <= MAX_CONFLICTING
    cix_t conflicting_clauses[MAX_CONFLICTING];

    dynvar(variable_t**, var_map);
#if defined(LIT_VALUE)
#if defined(PACKED_VALUE)
    dynvar(uint8_t*, lit_value);   // ivals for every lit_t value
    uint16_t*    lit_overlay; // write overlay access for single write access
#endif
#else
#if defined(PACKED_VALUE)
    dynvar(uint8_t*, var_value);   // values are stored 8 bit/2 bit packed
#endif
#endif
    size_t       nmarked;       // number of elements in marked
    variable_t*  marked_head;   // mlist marked variables
    variable_t** marked_tailp;  // pointer to tail pointer
    size_t       snum;          // number of symbols in symbol hash table
    dynvar(symbol_t**,symtab);  // symbol hash table
    size_t       hnum;          // number of clauses in clause hashtab
    dynvar(hlink_t**,hashtab);  // clause hash table
    dynvec(clause_t**,clauseset,NUM_CSET); // array of clausesets, entries may be null
    cdlist_t     order_list;    // doubly linked order list
    variable_t* order_next;     // next variable to search from
    
    clause_t*    unwatch;      // clauses to unwatch (check after bcp)
    dynvar(undo_t*,undo);       // array of undo block, one for each level
    size_t       num_bound;     // #bound variables
    size_t       num_subst;     // #substitions < #bound
    size_t       max_bound;     // max bound variables since last check
    int level;                  // current undo level
    int max_level;              // statistics max level since last check
    int min_level;              // statistics min level since last check

    slist_t q;                  // literal queue for propagation

    uint64_t  counter[NUM_COUNTERS];
    uint64_t  bcp_counter;    // performance counter/step counter/clock
    uint64_t  conflict_counter; // number of conflicts
    
    variable_t constant;

    arc4_stream_t as;              // random stream

    subscription_t* subs;          // list of subscriptions
    
    ErlNifEnv*      msg_env;       // message environment
    ErlNifEnv*      caller_env;    // message environment

    dynvar(lit_t*, tlit);          // temporary clause

    allocator_t dyn_allocator;     // heap storage for dyn_t
    allocator_t var_allocator;     // heap storage for variable_t
    allocator_t sym_allocator;     // heap storage for symbols_t
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

DECL_ATOM(alpha);
DECL_ATOM(atom);
DECL_ATOM(bcp_counter);
DECL_ATOM(beta);
DECL_ATOM(clause_2_counter);
DECL_ATOM(clause_3_counter);
DECL_ATOM(clause_d_counter);
DECL_ATOM(clause_n_counter);
DECL_ATOM(conflict);
DECL_ATOM(conflict_counter);
DECL_ATOM(dead);
DECL_ATOM(default);
DECL_ATOM(degree);
DECL_ATOM(delta);
DECL_ATOM(done);
DECL_ATOM(edge);
DECL_ATOM(edge_2_counter);
DECL_ATOM(edge_d_counter);
DECL_ATOM(error);
DECL_ATOM(exclamation_mark);
DECL_ATOM(f);
DECL_ATOM(false);
DECL_ATOM(fifo);
DECL_ATOM(flags);
DECL_ATOM(gamma);
DECL_ATOM(hash);
DECL_ATOM(implication);
DECL_ATOM(implication_clause);
DECL_ATOM(implication_pos);
DECL_ATOM(inqueue);
DECL_ATOM(is_atom);
DECL_ATOM(jump);
DECL_ATOM(length);
DECL_ATOM(level);
DECL_ATOM(lifo);
DECL_ATOM(literal);
DECL_ATOM(literal_integer);
DECL_ATOM(literal_size);
DECL_ATOM(max_bound);
DECL_ATOM(max_conflicting);
DECL_ATOM(max_level);
DECL_ATOM(min_level);
DECL_ATOM(number_of_bound_variables);
DECL_ATOM(number_of_clauses);
DECL_ATOM(number_of_conflicting_clauses);
DECL_ATOM(number_of_dead_clauses);
DECL_ATOM(number_of_dead_edges);
DECL_ATOM(number_of_edges);
DECL_ATOM(number_of_learnt_clauses);
DECL_ATOM(number_of_subst_variables);
DECL_ATOM(number_of_unbound_variables);
DECL_ATOM(number_of_variables);
DECL_ATOM(off);
DECL_ATOM(ok);
DECL_ATOM(phase);
DECL_ATOM(qtype);
DECL_ATOM(queue);
DECL_ATOM(recursive);
DECL_ATOM(reset);
DECL_ATOM(set);
DECL_ATOM(size);
DECL_ATOM(status);
DECL_ATOM(symbol);
DECL_ATOM(system_limit);
DECL_ATOM(t);
DECL_ATOM(toggle);
DECL_ATOM(true);
DECL_ATOM(turbo);
DECL_ATOM(undefined);
DECL_ATOM(unit);
DECL_ATOM(use);
DECL_ATOM(use_phase);
DECL_ATOM(user);
DECL_ATOM(value_packing);
DECL_ATOM(variable);
DECL_ATOM(varp);
DECL_ATOM(watch);
DECL_ATOM(watch0);
DECL_ATOM(watch1);
DECL_ATOM(xref);

#ifdef DEBUG_MEM
#define VARP_ALLOC(n)       debug_alloc((n))
#define VARP_REALLOC(ptr,n) debug_realloc((ptr),(n))
#define VARP_FREE(ptr)      debug_free((ptr))
#else
#define VARP_ALLOC(n)       enif_alloc((n))
#define VARP_REALLOC(ptr,n) enif_realloc((ptr),(n))
#define VARP_FREE(ptr)      enif_free((ptr))
#endif


#ifdef DEBUG_MEM

// NOT good for SMP!!! only light tetsing (atomics?)
ErlNifMutex* mem_lock;  // lock while updateing mem_allocated
static size_t mem_allocated = 0;
static dlist_t memlist;

#ifdef FENCE_MEM
#define MEM_FENCE1_SIZE  16
#define MEM_PATTERN1     0xA5
#define MEM_FENCE2_SIZE  16
#define MEM_PATTERN2     0xCC
#define MEM_FENCE3_SIZE  16
#define MEM_PATTERN3     0x7E
#endif

typedef struct memblock_t {
    dlink_t link;
#ifdef FENCE_MEM    
    uint8_t fence1[MEM_FENCE1_SIZE];
#endif
    size_t  allocated;
#ifdef FENCE_MEM        
    uint8_t fence2[MEM_FENCE2_SIZE];
#endif
    double  align;   // force double aligment
    uint8_t data[0];
    // uint8_t pattern[MEM_FENCE3_SIZE]
} memblock_t;

void debug_mem_init()
{
    mem_lock = enif_mutex_create("mem_lock");
    mem_allocated = 0;
    dlist_init(&memlist);
    enif_fprintf(stdout, "allocated memory at load = %ld\r\n",
		 mem_allocated);
}

void debug_mem_inc(size_t change)
{
    enif_mutex_lock(mem_lock);
    mem_allocated += change;
    enif_mutex_unlock(mem_lock);
}

void debug_mem_dec(size_t change)
{
    enif_mutex_lock(mem_lock);
    mem_allocated -= change;
    enif_mutex_unlock(mem_lock);
}

static void init_memblock(memblock_t* block, size_t n)
{
    block->allocated = n;
#ifdef FENCE_MEM
    {
	int i;
	for (i = 0; i < MEM_FENCE1_SIZE; i++)
	    block->fence1[i] = MEM_PATTERN1;
	for (i = 0; i < MEM_FENCE2_SIZE; i++)
	    block->fence2[i] = MEM_PATTERN2;
	for (i = 0; i < MEM_FENCE3_SIZE; i++)
	    block->data[n+i] = MEM_PATTERN3;
    }
#endif
}

static void validate_memblock(memblock_t* block, size_t n)
{
#ifdef FENCE_MEM
    int i;
    uint8_t f;
    for (i = 0; i < MEM_FENCE1_SIZE; i++) {
	if ((f = block->fence1[i]) != MEM_PATTERN1) {
	    fprintf(stderr,
		    "validatation failed: fence1 pos=%d [0x%02x]\r\n",
		    i, f);
	    exit(1);
	}
    }
    for (i = 0; i < MEM_FENCE2_SIZE; i++) {
	if ((f = block->fence2[i]) != MEM_PATTERN2) {
	    fprintf(stderr,
		    "validatation failed fence2 pos=%d [0x%02x]\r\n",
		    i, f);
	    exit(1);
	}
    }
    for (i = 0; i < MEM_FENCE3_SIZE; i++) {
	if ((f = block->data[n+i]) != MEM_PATTERN3) {
	    fprintf(stderr,
		    "validatation failed fence3 pos=%d [0x%02x]\r\n",
		    i, f);
	    exit(1);
	}
    }
#endif
}

void validate_memlist()
{
#ifdef FENCE_MEM    
    memblock_t* mptr;

    mptr = dlist_first(&memlist);
    while(!dlist_is_eol(mptr)) {
	validate_memblock(mptr, mptr->allocated);
	mptr = dlist_next(mptr);
    }
#endif
}

#define VALIDATE_MEMLIST() validate_memlist()

void* debug_alloc(size_t n)
{
    memblock_t* mptr;
    size_t size;

#ifdef FENCE_MEM
    size = sizeof(memblock_t)+n+MEM_FENCE3_SIZE;
#else
    size = sizeof(memblock_t)+n;
#endif
    if ((mptr = enif_alloc(size)) != NULL) {
	init_memblock(mptr, n);
	dlist_insert_first(&memlist, mptr);
	debug_mem_inc(n);
	fprintf(stderr, "debug_alloc: %p size=%ld\r\n", mptr, n);
	return &mptr->data[0];
    }
    return NULL;
}

void* debug_realloc(void* ptr, size_t n)
{
    if (ptr == NULL)
	return debug_alloc(n);
    else {
	memblock_t* pptr = (memblock_t*)(((uint8_t*)ptr) - offsetof(memblock_t, data));
	memblock_t* mptr;
	size_t m = pptr->allocated;
#ifdef FENCE_MEM
	size_t size = sizeof(memblock_t)+n+MEM_FENCE3_SIZE;
#else
	size_t size = sizeof(memblock_t)+n;
#endif
	validate_memlist();
	dlist_remove(&memlist, pptr);
	if ((mptr = enif_realloc(pptr, size)) != NULL) {
	    init_memblock(mptr, n);
	    dlist_insert_first(&memlist, mptr);
	    if (n == m)
		;
	    else if (n > m)
		debug_mem_inc(n - m);
	    else
		debug_mem_dec(m - n);
	    return &mptr->data[0];
	}
	fprintf(stderr, "debug_realloc: %p => %p size=%ld\r\n",
		pptr, ptr, n);
	debug_mem_dec(m);
	return NULL;
    }
}

void debug_free(void* ptr)
{
    if (ptr != NULL) {
	memblock_t* pptr = (memblock_t*)(((uint8_t*)ptr) - offsetof(memblock_t, data));
	size_t m = pptr->allocated;
	validate_memlist();
	dlist_remove(&memlist, pptr);
	debug_mem_dec(m);
	fprintf(stderr, "debug_free: %p\r\n", pptr);
	enif_free(pptr);
    }
}

#else

#define VALIDATE_MEMLIST()

#endif

static heap_t* new_heap_block()
{
    heap_t* hp;
    if ((hp = VARP_ALLOC(HEAP_BLOCK_SIZE + HEAP_ALIGN - 1)) == NULL)
	return NULL;
    hp->current = hp->base + PAD(hp->base,HEAP_ALIGN);
    hp->end     = hp->current + MAX_HEAP_ALLOC_SIZE;
    return hp;
}

static void* heap_alloc(slist_t* list, size_t size)
{
    heap_t* hp;
    void* ptr;

    if (size > MAX_HEAP_ALLOC_SIZE)
	return NULL;
    if (slist_is_empty(list))
	hp = slist_insert_first(list, new_heap_block());
    else {
	hp = slist_first(list);
	if (hp->current + size >= hp->end)
	    hp = slist_insert_first(list, new_heap_block());
    }
    ptr = hp->current;
    hp->current += size;
    return ptr;
}

static void heap_cleanup(slist_t* list)
{
    heap_t* hp = slist_first(list);
    while(!slist_is_eol(hp)) {
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
#ifdef DEBUG_MEM
    dlist_init(&ap->obj_list);
#endif
    return 0;
}

static void allocator_cleanup(allocator_t* ap)
{
#ifdef DEBUG_MEM
    object_link_t* olink = dlist_first(&ap->obj_list);
    while(!dlist_is_eol(olink)) {
	object_link_t* olink_next = dlist_next(olink);
	VARP_FREE(olink->obj);
	VARP_FREE(olink);
	olink = olink_next;
    }
    dlist_init(&ap->obj_list);
#endif
    heap_cleanup(&ap->heap_list);
    slist_init(&ap->heap_list);
    slist_init(&ap->free_list);
}

static void* obj_alloc(allocator_t* ap)
{
    object_t* obj;
#ifdef DEBUG_MEM
    object_link_t* olink;
    if ((obj = VARP_ALLOC(ap->size)) == NULL)
	return NULL;
    olink = VARP_ALLOC(sizeof(object_link_t));
    olink->obj = obj;
    obj->olink = olink;
    dlist_insert_last(&ap->obj_list, olink);
#else
    if (slist_is_empty(&ap->free_list))
	return heap_alloc(&ap->heap_list, ap->size);
    obj = slist_take_first(&ap->free_list);
#endif
    return obj;
}

static void obj_free(allocator_t* ap, void* ptr)
{
#ifdef DEBUG_MEM
    if (ptr != NULL) {
	object_t* obj = (object_t*) ptr;
	object_link_t* olink = obj->olink;
	dlist_remove(&ap->obj_list, olink);
	VARP_FREE(olink);
	VARP_FREE(obj);
    }
#else
    slist_insert_last(&ap->free_list, ptr);
#endif
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

static size_t dynarray_next_size(size_t cur, size_t capacity)
{
    while((cur < DYN_GROW0_LIMIT) && (cur < capacity))
	cur *= DYN_GROW0;
    while((cur < DYN_GROW1_LIMIT) && (cur < capacity))
	cur *= DYN_GROW1;
    while((cur < capacity))
	cur *= DYN_GROW2;
    return cur;
}

static size_t dynarray_first_size(size_t capacity)
{
    return dynarray_next_size(1, capacity);
}

#if 0
static void dyntype_init(dyntype_t* dt, const char* name, size_t width)
{
    dt->name = name;
    dt->width = width;
}
#endif
      
static int dynarray_init(dynarray_t* dp, const char* name,
			 size_t initial_capacity,
			 size_t width)
{
    void* base;
    size_t capacity;
    
    if (initial_capacity == 0) {
	capacity = 0;
	base = NULL;
    }
    else {
	capacity = dynarray_first_size(initial_capacity);
	if ((base = VARP_ALLOC(capacity*width)) == NULL)
	    return -1;
    }
#ifdef DEBUG_MEM    
    enif_fprintf(stdout, "dynarray_init[%s]: base=%p,capacity=%d,width=%d\r\n",
		 name, base, capacity, width);
#endif
    dp->name     = name;
    dp->capacity = capacity;
    dp->size     = 0;
    dp->width    = width;
    dp->base     = base;
    return 0;
}

static void dynarray_clear(dynarray_t* dp)
{
#ifdef DEBUG_MEM        
    enif_fprintf(stdout,
		 "dynarray_clear[%s]: base=%p,size=%d,capacity=%d,width=%d\r\n",
		 dp->name, dp->base, dp->size, dp->capacity, dp->width);
#endif
    VARP_FREE(dp->base);
    dp->base = NULL;
    dp->size = 0;
    dp->capacity = 0;
}

static void dynarray_destroy(varp_t* vp, dynarray_t* dp)
{
    if (dp) {
	dynarray_clear(dp);
	obj_free(&vp->dyn_allocator, dp);
    }
}

static inline size_t dynarray_capacity(dynarray_t* dp)
{
    return (dp == NULL) ? 0 : dp->capacity;
}

static inline size_t dynarray_size(dynarray_t* dp)
{
    return (dp == NULL) ? 0 : dp->size;
}

static int dynarray_set_capacity(dynarray_t* dp, size_t capacity)
{
    void* base;

#ifdef DEBUG_MEM
    enif_fprintf(stdout, "dynarray_set_capacity[%s] base=%p from=%d to %d\r\n",
		 dp->name, dp->base, dp->capacity, capacity);
#endif
    if ((base = VARP_REALLOC(dp->base, capacity*dp->width)) == NULL)
	return -1;
    dp->base = base;
#ifdef DEBUG_MEM
    enif_fprintf(stdout, "dynarray_set_capacity[%s]: base=%p [%s] %d => %d\r\n",
		 dp->name, dp->base, dp->name, dp->capacity, capacity);
#endif
    dp->capacity = capacity;
    dp->size = MIN(dp->size, capacity);
    return 0;
}

static inline int dynarray_resize(dynarray_t* dp, size_t size)
{
#ifdef DEBUG_MEM
    enif_fprintf(stderr, "dynarray_resize[%s] %d (from %d) (capacity=%d)\r\n",
		 dp->name, size, dp->size, dp->capacity);
#endif
    if (size > dp->capacity) {
	size_t capacity = dynarray_next_size(MAX(1,dp->capacity), size);
	if (dynarray_set_capacity(dp, capacity) < 0)
	    return -1;
    }
    dp->size = size;
    return 0;
}

static dynarray_t* dynarray_create(varp_t* vp, const char* name,
				   size_t capacity, size_t width)
{
    dynarray_t* dp;
    
    if ((dp = obj_alloc(&vp->dyn_allocator)) == NULL)
	return NULL;
    if (dp != NULL) {
	if (dynarray_init(dp, name, capacity, width) < 0) {
	    obj_free(&vp->dyn_allocator, dp);
	    return NULL;
	}
    }
    return dp;
}

static inline dynarray_t* dynarray_empty(varp_t* vp, const char* name,
					 size_t width)
{
    return dynarray_create(vp, name, 0, width);
}

static inline void* dynarray_element(dynarray_t* dp, int i)
{
    if (dp == NULL) return NULL;
    if (i == 0) return dp->base;
    if ((i < 0) || (i >= (int)dp->size)) return NULL;
    return DYN_ADDR(dp, i);
}


// copy data into dynarray resize if needed
static inline int dynarray_setelement(dynarray_t* dp,int i,void* data)
{
    if (dp == NULL || (i < 0)) return -1;
    if (i >= (int)dp->size) {
	if (dynarray_resize(dp, i+1) < 0)
	    return -1;
    }
    memcpy(DYN_ADDR(dp, i), data, dp->width);
    return 0;
}

static inline void* dynarray_add(dynarray_t* dp)
{
    size_t n;
    if (dp == NULL) return NULL;
    n = dp->size;
    if (dynarray_resize(dp, n+1) < 0)
	return NULL;
    return DYN_ADDR(dp, n);
}

static inline void* dynarray_delete(dynarray_t* dp, int i)
{
    void* src;    
    void* dst;
    size_t len;
    
    if ((i<0) || (dp == NULL) || (i >= (int)dp->size))
	return NULL;
    dst = DYN_ADDR(dp, i);
    src = dst + dp->width;
    if ((len = (dp->size - i -1)) > 0)
	memmove(dst, src, len*dp->width);
    dp->size--;
    return dst;
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

// primitive negate a literal
static inline literal_t* neg_ll(literal_t* lp)
{
    return &lp->var->lit[!lp->neg];
}

static inline literal_t* vindex_ll(varp_t* vp, int i)
{
    ASSERT(i != 0);
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
    return lp->neg ? -lp->var->ix : lp->var->ix;
}

static inline ERL_NIF_TERM external_ll(ErlNifEnv* env,literal_t* lp)
{
    if (lp->var->ix == 0)
	return lp->neg ? ATOM(f): ATOM(t);
    else {
	int x = export_ll(lp);
	return enif_make_int(env, x);
    }
}

static inline bool_t is_neg_l(lit_t l)
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

#ifndef LIT_VALUE
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

#endif

// primitiv get variable value
static inline ival_t get_vv(varp_t* vp, variable_t* var)
{
#ifdef PACKED_VALUE
    return get_packed_ival(vp, var->ix);
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
    vp->lit_overlay[var->ix] = (v << 8) | v;
#else
    set_packed_ival(vp, var->ix, v);
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
    // enif_fprintf(stderr, "clr_vv %d\r\n", var->ix);        
    write_vv(vp, var, I_UNDEF);
}

static inline void bnd_vv(varp_t* vp, variable_t* var)
{
    // enif_fprintf(stderr, "bnd_vv %d\r\n", var->ix);    
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
    vp->lit_overlay[var->ix] = w;
#else
    set_packed_ival(vp, var->ix, ivalue);
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
	return lp->neg ^ v;
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
    if (lp->neg)
	set_vv(vp,lp->var,NEGATE(ivalue));
    else
	set_vv(vp,lp->var,ivalue);
}
#endif

// given a literal pointer, return the susbstituted literal value
static inline literal_t* lookup_literal(literal_t* lp)
{
    literal_t* bp;
    while ((bp = lp->var->bound) != NULL) { // resolve literal
	if (lp->neg)  // negate literal
	    lp = neg_ll(bp);
	else
	    lp = bp;
    }
    return lp;
}

static inline int phase_export(variable_t* var)
{
    return (var->phase == I_FALSE) ? -var->ix : var->ix;
}

static inline ival_t decide_phase(varp_t* vp, lit_t xp)
{
    literal_t* lp = l2ll(vp, xp);
    if (vp->opt.use_phase)
	return lp->var->phase;
    return vp->opt.init_phase;
}

static inline bool_t variable_is_bound(varp_t* vp, variable_t* var)
{
    return get_vv(vp, var) != I_UNDEF;
}

static inline bool_t literal_is_bound(varp_t* vp, literal_t* lp)
{
    return get_vv(vp, lp->var) != I_UNDEF;
}

// return true if variable is constant or bound to other variable
// vix is a variable index or the negation of the same
static inline int vis_bound(varp_t* vp, int i)
{
    return variable_is_bound(vp, vp->var_map[ABS(i)]);
}

static inline int export_vv(varp_t* vp, variable_t* var)
{
    switch(get_vv(vp, var)) {
    case I_TRUE:  return var->ix;
    case I_FALSE: return -var->ix;
    case I_BOUND: ASSERT(0); return 0;
    case I_UNDEF:
    default: return 0;
    }
}

static inline literal_t* literal_vv(varp_t* vp, variable_t* var)
{
    ival_t ival = get_vv(vp, var);
    int i = var->ix;
    ASSERT((ival & 0x2) == 0x2);  // must not be bound/undef
    if (ival == I_FALSE)
	i = -i;
    return vindex_ll(vp, i);
}

static inline void mark(varp_t* vp, variable_t* var, uint8_t marks)
{
    if (!(var->mark & MARKL)) { // not on mark list
	*(vp->marked_tailp) = var;  // put last
	var->mark_next = NULL;
	vp->marked_tailp = &(var->mark_next);
	vp->nmarked++;
	marks |= MARKL;  // on list
    }
    var->mark |= marks;
}

static inline void unmark(variable_t* var, uint8_t marks)
{
    var->mark &= ~marks;
}

// any/all just an other name for clarity
static inline bool_t is_marked(variable_t* var, uint8_t mark)
{
    return (var->mark & mark) == mark;
}

// check that any flags in flag are set
static inline int any_marked(variable_t* var, uint8_t marks)
{
    return ((var->mark & marks) != 0);
}

// check that all flags in flag are set
static inline int all_marked(variable_t* var, uint8_t marks)
{
    return ((var->mark & marks) == marks);
}

// clear before use!  clear all marks and clear mark list
static void unmark_all(varp_t* vp)
{
    variable_t* var = vp->marked_head;
    while(var) {
	var->mark = 0;
	var = var->mark_next;
    }
    vp->nmarked = 0;
    vp->marked_head = NULL;
    vp->marked_tailp = &(vp->marked_head);
}


static inline void unmark_clause(clause_t* cp, uint8_t mask)
{
    if (cp != NULL)
	cp->flags &= mask;
}

static void unmark_cix_clauses(varp_t* vp,cix_t* cixv, size_t len,uint8_t mask)
{
    while(len--) {
	clause_t* cp = get_clause(vp, *cixv++);
	unmark_clause(cp, mask);
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
	ASSERT(l != L_TRUE(vp));
	if (l == L_FALSE(vp))  // count as zero
	    continue;
	hvalue = literal_hash_add(hvalue, l);
    }
    return hvalue;
}

// FIXME make thread safe
char* format_variable(variable_t* var)
{
    static char vn1[32];
    static char vn2[32];
    static char* varname = vn2;

    varname = (varname == vn1) ? vn2 : vn1;
    
    if (var->strname != NULL)
	snprintf(varname, sizeof(vn1), "%s", var->strname);	
    else
	snprintf(varname, sizeof(vn1), "%d", var->ix);
    return varname;
}

// FIXME make thread safe
char* format_literal(varp_t* vp, literal_t* lp)
{
    static char ln1[32];
    static char ln2[32];
    static char* litname = ln2;
    char* n;
    UNUSED(vp);
    
    if (lp == NULL)
	return "NULL";
    
    // alternate to allow to printf arguments!!
    litname = (litname == ln1) ? ln2 : ln1; 
    n = lp->neg ? "!" : "";
    if (lp->var->strname != NULL)
	snprintf(litname, sizeof(ln1), "%s%s", n, lp->var->strname);
    else
	snprintf(litname, sizeof(ln1), "%s$%d", n, lp->var->ix);
    return litname;
}

char* format_lit(varp_t* vp, lit_t l)
{
    if (l == L_TRUE(vp)) return "t";
    else if (l == L_FALSE(vp)) return "f";
    else return format_literal(vp, l2ll(vp, l));
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

void print_ll(literal_t* lp)
{
    int vix;
    if ((vix=lp->var->ix) == 0) {
	if (lp->neg)
	    enif_fprintf(stdout, "f");
	else
	    enif_fprintf(stdout, "t");
    }
    else {
	if (lp->neg)
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
    enif_fprintf(stdout, "%s %d:%d (t=%ld) (w=%ld:%ld) [%d/%s",
		 label, GET_SI(cp->cix), GET_IX(cp->cix),
		 cp->stamp, cp->wl[0].p, cp->wl[1].p,
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
    enif_fprintf(stdout, "%s id=%d:%d,[%ld:%ld] ",
		 label, GET_SI(cp->cix), GET_IX(cp->cix),
		 cp->wl[0].p, cp->wl[1].p);
    print_sym_array(vp, cp->lit, cp->size);
    if ((cp->flags & CLAUSE_FLAG_DEAD)!=0)
	enif_fprintf(stdout, " dead=%d");
    enif_fprintf(stdout, "\r\n");
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
	struct timeval tv;
	uint8_t rnd[128 - sizeof(struct timeval) - sizeof(pid_t)];
    } rdat;

    gettimeofday(&rdat.tv, NULL);
#ifndef __WIN32__
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

static inline void wlink_clear(wlink_t* wlp)
{
    wlp->p = -1;
    wlp->next = NULL;   // mark dead for debug
}

static inline void wlink_link(wlink_t* wlp, literal_t* lp)
{
    wlp->next = lp->wlist;  // link literal
    lp->wlist = wlp;
}

static inline void wlink_set(wlink_t* wlp, long p, literal_t* lp)
{
    wlp->p = p;   // new watch point
    wlink_link(wlp, lp);
}

// FIXME: make constant
static void wlink_unlink(varp_t* vp, clause_t* cp, literal_t* lp)
{
    UNUSED(vp);
    wlink_t** wlp = &lp->wlist;
    wlink_t* wl;

    // DBG("UNWATCH cix=%lu lit=%d wl=%p\r\n", cp->cix, export_ll(lp), *wlp);

    while((wl = *wlp) && (clause_pointer(wl) != cp))
	wlp = &(wl->next);
    if (wl != NULL) {
	*wlp = wl->next;  // unlink
	wl->next = NULL;  // do we need to clear this?
	wl->p = -1;       // mark as not used
    }
}

static inline void unwatch_l(varp_t* vp, clause_t* cp, lit_t l)
{
    wlink_unlink(vp, cp, l2ll(vp, l));
}

// remove the 2-WL watch points
static void clause_unwatch(varp_t* vp, clause_t* cp)
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

static inline void lqueue_insert_ll(varp_t* vp, literal_t* lp)
{
    DBG("%sEnq %s\r\n", indent(vp->level), format_literal(vp,lp));

    // make sure literals are not queued twice!
    if (lp->flags & LIT_FLAG_Q) {
	enif_fprintf(stdout, "already in queue\r\n");
	return;
    }
    ASSERT(!slist_is_member(&vp->q, lp));  // special extra check
    if (vp->opt.qtype == lifo) // put element first
	slist_insert_first(&vp->q, lp);
    else
	slist_insert_last(&vp->q, lp);
    lp->flags |= LIT_FLAG_Q;
}

// always get from head of list(queue)
static inline literal_t* lqueue_deq(varp_t* vp)
{
    literal_t* lp;
    if (slist_is_empty(&vp->q))
	return NULL;
    lp = slist_take_first(&vp->q);
    DBG("DEQ %s\r\n", format_literal(vp,lp));
    lp->flags &= ~LIT_FLAG_Q;
    return lp;
}

static void lqueue_clear(varp_t* vp)
{
    literal_t* lp = slist_first(&vp->q);
    while(!slist_is_eol(lp)) {
	lp->flags &= ~LIT_FLAG_Q;
	lp = slist_next(lp);
    }
    slist_init(&vp->q);
}

static inline void push_variable(varp_t* vp, variable_t* var, int level)
{
    ASSERT(get_vv(vp, var) == I_UNDEF);
    var->bound_next = vp->undo[level].bs;
    vp->undo[level].bs = var;
    vp->undo[level].size++;
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
    ERL_NIF_TERM sub_info_keys[8] = {
	ATOM(number_of_variables),
	ATOM(number_of_bound_variables),
	ATOM(number_of_clauses),
	ATOM(number_of_dead_clauses),
	ATOM(max_level),
	ATOM(max_bound),
	ATOM(number_of_subst_variables),
	ATOM(min_level),
    };
    ERL_NIF_TERM values[8] = {
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
    if (flags & SUB_FLAG_NUM_SUBST)
	values[6] = enif_make_int(env, vp->num_subst);
    if (flags & SUB_FLAG_MIN_LEVEL) {
	if (vp->min_level == MAX_INT32)
	    values[7] = enif_make_int(env, 0);
	else
	    values[7] = enif_make_int(env, vp->min_level);
	vp->min_level = MAX_INT32;  // and reset
    }
    return enif_make_map_from_arrays(env, sub_info_keys, values, 8, info);

    
}

static void log_permanent_(varp_t* vp, literal_t* x, literal_t* y)
{
    ErlNifEnv* env = vp->msg_env;
    subscription_t* sp = vp->subs;
    
    while(sp != NULL) {
	if ((sp->flags & SUB_FLAG_VAR) ||
	    ((sp->flags & SUB_FLAG_ATOM) &&
	     (x->var->is_atom))) {
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
	    else { // y->var->is_atom
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
	sp = (subscription_t*)sp->link.next;
    }
}

static inline void log_permanent(varp_t* vp, literal_t* x,
				 literal_t* y, int level)
{
    if (level != 0) return;
    if (vp->subs == NULL) return;
    log_permanent_(vp, x, y);
}

// get next unbound literal
static int next_unbound(varp_t* vp)
{
    variable_t* var;

    if ((var = vp->order_next) != NULL) {
	while(!cdlist_is_eol(var) && variable_is_bound(vp, var))
	    var = cdlist_next(var);
	if (!cdlist_is_eol(var)) {
	    vp->order_next = var;
	    return var->ix; // phase_export(var);
	}
	vp->order_next = NULL;
    }
    return 0;
}

static int next_unbound_after(varp_t* vp, variable_t* var)
{
    if (!cdlist_is_last(&vp->order_list, var)) {
	var = cdlist_next(var);
	while(!cdlist_is_eol(var) && variable_is_bound(vp, var))
	    var = cdlist_next(var);
	if (!cdlist_is_eol(var))
	    return var->ix; // phase_export(var);
    }
    return 0;
}

// level=0 work
// after evaluation of a literal in the L literal queue
// schedule all clauses in cross referenced from !L to
// be killed.

static void kill_clauses(varp_t* vp, literal_t* xp)
{
    xref_t* xptr = dynarray_element(xp->xref, 0);
    size_t  len  = dynarray_size(xp->xref);

    DBG_BCP("%sKill %s\r\n", indent(vp->level), format_literal(vp, xp));

    while(len--) {
	clause_t* cp = get_clause(vp, xptr->cix);
	if (cp && !(cp->flags & CLAUSE_FLAG_DEAD)) { // not alread dead
	    vp->cdead++;
	    cp->flags |= CLAUSE_FLAG_DEAD;
	    if ((cp->size == 2) && vp->opt.edge) {
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
	xptr++;
    }
}

// insert implication edge a -> b, this will trigger
// when a=1 and yield b=1
static void edge_insert(varp_t* vp, lit_t a, lit_t b, cix_t cix)
{
    edge_t* ep;
    literal_t* ap = l2ll(vp, a);
    
    ep = obj_alloc(&vp->edge_allocator);
    ep->l = b;
    ep->cix = cix;
    ep->link.next = (cdlink_t*)ap->elist;
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
	    *ppp = (edge_t*) pp->link.next;
	    obj_free(&vp->edge_allocator, pp);
	    vp->nedge--;
	    return;
	}
	ppp = (edge_t**) &(pp->link.next);
    }
}

static void put_nq_ll(varp_t* vp, literal_t* lp, ival_t ivalue,
		      pos_t li, cix_t cix, int level)
{
    variable_t* var = lp->var;

    DBG_BCP("%sPut %s=%s @%d\r\n", indent(level), format_literal(vp,lp),
	    format_ival(ivalue), level);
    ASSERT(level >= 0);
    ASSERT(var->bound == NULL);    
    ASSERT(!IS_CONSTANT(get_vv(vp, var)));

    push_variable(vp, var, level);

    set_vv(vp, var, lp->neg ? NEGATE(ivalue) : ivalue);
    var->implication_clause = cix;
    var->literal_pos = li;
    var->level = level;
    if (cix != CLAUSE_NONE) // not a decision 
	var->phase = ivalue;  // save for use with phase restore
    log_permanent(vp, lp, NULL, level);
}

//  X=1         enq -X
// -X=1 == X=0  enq  X
//  X=0         enq  X
// -X=0 == X=1  enq -X
// value=1 then negate literal!

static void put_ll(varp_t* vp, literal_t* lp, ival_t ivalue,
		   pos_t li, cix_t cix, int level)
{
    put_nq_ll(vp, lp, ivalue, li, cix, level);
    if (ivalue == I_TRUE)
	lqueue_insert_ll(vp, neg_ll(lp));
    else if (ivalue == I_FALSE)
	lqueue_insert_ll(vp, lp);
}

static inline void put_l(varp_t* vp,lit_t l,ival_t ivalue,
			 pos_t li, cix_t cix, int level)
{
    put_ll(vp,l2ll(vp, l),ivalue,li,cix,level);
}

static void init_level(varp_t* vp, int level)
{
    ASSERT(level < (int)dynvar_size(vp->undo));
    vp->undo[level].decision = L_FALSE(vp);
    vp->undo[level].t  = uUNDEF;
    vp->undo[level].size  = 0;
    vp->undo[level].bs = NULL;
}

static int undo_set_size(varp_t* vp, size_t size)
{
    size_t n = dynvar_size(vp->undo);
    int i;
    if (dynvar_resize(vp->undo, size) < 0)
	return -1;
    // clear added levels
    for (i = (int)n; i < (int)size; i++)
	init_level(vp, i);
    return 0;
}

// set current bindings level
static int set_level(varp_t* vp, int level)
{
    if (level >= (int)dynvar_size(vp->undo))
	undo_set_size(vp, level+1);
    vp->level = level;
    if (level > vp->max_level)
	vp->max_level = level;
    DBG("%sSet_level: @%d, t=%d, decision=%s\r\n",
	indent(level), level, vp->undo[level].t,
	format_lit(vp, vp->undo[level].decision)); 
#ifdef ASSERTIONS
    {
	// check that levels above level are clean
	int n = (int)dynvar_size(vp->undo);
	int i;
	for (i = level+1; i < n; i++) {
	    ASSERT(vp->undo[i].bs == NULL);
	    ASSERT(vp->undo[i].size == 0);
	    ASSERT(vp->undo[i].t == uUNDEF);
	}
    }
#endif
    return 0;
}

static void unbind_level(varp_t* vp, int level)
{
    variable_t* bp = vp->undo[level].bs;

    DBG_ORDER("%sUnbind_level @%d\r\n", indent(level), level);

    while(bp != NULL) {
	ASSERT(bp->bound == NULL);
	DBG_BCP("%sUnbind %s\r\n",indent(level),format_variable(bp));
	clr_vv(vp, bp);
	bp->implication_clause = CLAUSE_NONE;
	bp->literal_pos = -1;
	bp->level = -1;
	if ((vp->order_next == NULL) || cdlist_is_before(bp, vp->order_next))
	    vp->order_next = bp;
	bp = bp->bound_next;
    }
    vp->num_bound -= vp->undo[level].size;
    vp->undo[level].size = 0;
    vp->undo[level].bs = NULL;
}

static void undo_level(varp_t* vp, int level)
{
    DBG_ORDER("%sUndo_level @%d\r\n", indent(level), level);    
    unbind_level(vp, level);
    init_level(vp, level);
}

// move bindings from src level to dst level
// the bindings are moved last into dst level
static void move_level(varp_t* vp, int src, int dst)
{
    variable_t* var = vp->undo[src].bs;

    if (var) {
	log_permanent(vp, var_literal(vp,var), NULL, dst);
	// find last binding
	while(var->bound_next) {
	    var->level = dst;
	    var = var->bound_next;
	    log_permanent(vp, var_literal(vp,var), NULL, dst);
	}
	var->bound_next = vp->undo[dst].bs;
	var->level = dst;
	vp->undo[dst].bs = vp->undo[src].bs;
	vp->undo[dst].size += vp->undo[src].size;
	init_level(vp, src);
    }
}

// clear but do not undo a level (keep the bindings)
static void keep_level(varp_t* vp, int level)
{
    vp->undo[level].bs = NULL;
    vp->undo[level].size = 0;
}

static void ll_init(literal_t* lp, variable_t* var, bool_t neg)
{
    lp->neg      = neg;
    lp->flags    = 0;
    lp->l        = MAKE_LIT(var->ix,neg);
    lp->var      = var;
    lp->wlist    = NULL;
    lp->elist    = NULL;
    lp->xref     = NULL;
}

static void var_init(varp_t* vp, variable_t* var, int ix)
{
    var->ix         = ix;
    var->phase      = vp->opt.init_phase;
    var->is_atom    = false;
    var->mark       = 0;
    var->flags      = 0;    
    var->bound_next = NULL;
    var->bound      = NULL;
    var->implication_clause = CLAUSE_NONE;
    var->literal_pos = -1;
    var->level = -1;
    var->strname = NULL;
    var->names = NULL;
    clr_vv(vp, var);
    ll_init(&var->lit[LIT_POS], var, false);
    ll_init(&var->lit[LIT_NEG], var, true);
}

// return 1 if literal array a is equal to literal array b, return 0 otherwise
static int clause_is_equal(lit_t* a, lit_t* b, int size)
{
    int i = 0;
    while((i<size) && (a[i] == b[i]))
	i++;
    return (i == size);
}

// allocate / resize clause hash table
static int hashtab_grow(varp_t* vp)
{
    size_t size0 = dynvar_size(vp->hashtab);
    size_t size  = next_pow2(size0);
    int i;

    if (dynvar_resize(vp->hashtab, size) < 0)
	return -1;
    // clear new links
    memset(vp->hashtab+size0, 0, (size-size0)*sizeof(hlink_t*));
    // move elements that rehash to the upper part
    for (i = 0; i < (int)size0; i++) {
	hlink_t** hpp = &vp->hashtab[i];
	hlink_t* hp;
	while((hp = *hpp) != NULL) {
	    int j = hp->hvalue & (size-1);  // hash with new size
	    if (i == j) { // element stay
		hpp = (hlink_t**) &(hp->link.next);
	    }
	    else { // element move to new location j=(i+2^r) (top half)
		*hpp = (hlink_t*) hp->link.next;
		hp->link.next = (cdlink_t*) vp->hashtab[j];
		vp->hashtab[j] = hp;		
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
    hp->link.next = (cdlink_t*)vp->hashtab[i];
    vp->hashtab[i] = hp;
    vp->hnum++;
    return 0;
}

static int hash_unlink(varp_t* vp, clause_t* cp)
{
    int i = cp->hvalue & (dynvar_size(vp->hashtab)-1);
    hlink_t** hpp = &vp->hashtab[i];
    while(*hpp) {
	hlink_t* hp = *hpp;
	if (hp->cix == cp->cix) {
	    *hpp = (hlink_t*) hp->link.next;
	    obj_free(&vp->hlink_allocator, hp);
	    return 0;
	}
	hpp = (hlink_t**) &(hp->link.next);
    }
    DBG("clause %d not found in hash table\r\n", cp->cix);
    return -1;
}

static hlink_t* hlink_lookup(varp_t* vp,lit_t* lit,size_t size,uint32_t hvalue)
{
    size_t hsize = dynvar_size(vp->hashtab);
    if (hsize > 0) {
	int i = hvalue & (hsize-1);
	hlink_t* hp = vp->hashtab[i];
	while(hp) {
	    if (hp->hvalue == hvalue) {
		clause_t* cp = get_clause(vp, hp->cix);
		ASSERT(cp != NULL);
		if ((cp->size == size) && clause_is_equal(lit,cp->lit,size))
		    return hp;
	    }
	    hp = (hlink_t*) hp->link.next;
	}
    }
    return NULL;
}

// FIXME clauses should really be heap allocated?
// except we need to garbage collect in that case when
// deleting clauses...or
// at least alpha is no problem (just delete and restart)
// gamma need to be purged and copied somehow, copy active clauses?

static clause_t* clause_alloc(varp_t* vp, int size)
{
    UNUSED(vp);
    clause_t* cp;
    size_t nbytes;
    
    if (size < 1)
	return NULL;
    nbytes = sizeof(clause_t) + sizeof(lit_t)*size;
#if defined(__WIN32__)
    if ((cp = _aligned_malloc(nbytes, CLAUSE_ALIGNMENT)) == NULL) {
      return NULL;
    }
#else
    if (posix_memalign((void**)&cp, CLAUSE_ALIGNMENT, nbytes) != 0) {
	// fixme: maybe handler return value as errno...
	return NULL;
    }
#endif
    wlink_clear(&cp->wl[0]);
    wlink_clear(&cp->wl[1]);
    cp->size = size;
    cp->flags = 0;
    cp->select = (size > 3) ? 3 : size-1;
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
#if defined(__WIN32__)
	_aligned_free(cp);
#else
	free(cp);
#endif
    }
}

static clause_t* clause_copy(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	clause_t* copy;
	if ((copy = clause_alloc(vp, cp->size)) == NULL)
	    return NULL;
	memcpy(copy->lit, cp->lit, cp->size*sizeof(lit_t));
	return copy;
    }
    return NULL;
}

#if 0
// return 1 if a is subclause of b, return 0 otherwise
// assume both clauses are sorted in falling order
// (C D E)   (A B C D E F)
static int clause_is_subclause(lit_t* a, lit_t* b, int size_a, int size_b)
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
#endif

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
	    clause_is_equal(lit, cp->lit, size)) {
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
    
    DBG("clauseset_hash_insert: si=%dm n=%d\r\n", si, n);
    
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
    cp->stamp  = vp->bcp_counter;
    cp->hvalue = hvalue;

    if (dynvec_resize(vp->clauseset, si, ix+1) < 0)
	return CLAUSE_NONE;

    vp->cnum[si]++;
    set_clause(vp, cix, cp);
    if ((si != ALPHA) && vp->opt.hash) // alphas are not hashed
	clause_hash_insert(vp, cp);
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
    else if (arg == ATOM(delta))
	*si = DELTA;
    else if (arg == ATOM(gamma))
	*si = GAMMA;
    else if (arg == ATOM(alpha))
	*si = ALPHA;
    else if (arg == ATOM(beta))
	*si = BETA;
    else
	return 0;
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
	else if (ABS(x) < (int)dynvar_size(vp->var_map))
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
	else if (ABS(x) < (int)dynvar_size(vp->var_map))
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
    si = GET_SI(cix);
    if ((ix = GET_IX(cix)) >= (int)dynvec_size(vp->clauseset,si))
	return 0;
    *cixp = cix;
    return 1;
}

// read a clause - list of literals
int vif_get_lit_list(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM list,
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
	int n = *lenp;
	ERL_NIF_TERM elem[n];
	int i;
	if (!enif_get_list(env, list, lenp, elem))
	    return 0;
	n = *lenp;
	for (i = 0; i < n; i++) {
	    if (!vif_get_lit(env, vp, elem[i], &clause[i]))
		return 0;
	}
	return 1;
    }
}

// read a clause - list of literals
int vif_get_literal_list(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM list,
			 int* lenp, literal_t** clause)
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
	int n = *lenp;
	ERL_NIF_TERM elem[n];
	int i;
	if (!enif_get_list(env, list, lenp, elem))
	    return 0;
	n = *lenp;
	for (i = 0; i < n; i++) {
	    if (!vif_get_literal(env, vp, elem[i], &clause[i]))
		return 0;
	}
	return 1;
    }
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, literal_t* lp)
{
    return enif_make_int(env, export_ll(lp));
}

static void symbol_clear(symbol_t* sp)
{
    while(sp) {
	if (!sp->is_term) {
	    fprintf(stderr, "clear symbol '%s'\r\n", sp->data);
	}
	VARP_FREE(sp->data);
	sp = (symbol_t*) sp->link.next;
    }
}

static void cleanup(varp_t* vp)
{
    int si;
    int i;
    
    if (vp->symtab) {
	size_t size = dynvar_size(vp->symtab);
	for (i = 0; i < (int)size; i++)
	    symbol_clear(vp->symtab[i]);
	dynvar_clear(vp->symtab);
    }

    for (i = 1; i < (int)dynvar_size(vp->var_map); i++) {
	dynarray_destroy(vp, vp->var_map[i]->lit[0].xref);
	dynarray_destroy(vp, vp->var_map[i]->lit[1].xref);
    }

    dynvar_clear(vp->var_map);
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
    dynvar_clear(vp->lit_value);
    vp->lit_overlay = NULL;
#else
    dynvar_clear(vp->var_value);
#endif
#endif
    // turn off, avoid free all hash links clause_free
    dynvar_clear(vp->hashtab);
    vp->hnum = 0;
    vp->opt.hash = false; // avoid unlink in clause_free
    
    for (si = 0; si < NUM_CSET; si++) {
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
    }

    dynvar_clear(vp->undo);
    dynvar_clear(vp->tlit);

    allocator_cleanup(&vp->dyn_allocator);    
    allocator_cleanup(&vp->var_allocator);
    allocator_cleanup(&vp->sym_allocator);
    allocator_cleanup(&vp->sub_allocator);
    allocator_cleanup(&vp->edge_allocator);
    allocator_cleanup(&vp->hlink_allocator);
}


static void default_config(varp_config_t* conf)
{
    conf->qtype = recursive;
    conf->xref  = false;    
    conf->hash  = false;
    conf->edge  = false;
    conf->init_phase = I_TRUE;
    conf->use_phase  = false;
    conf->vsize  = DEFAULT_MAP_SIZE;
    conf->csize  = DEFAULT_MAP_SIZE;
}

static int vif_config(ErlNifEnv* env,
		      const ERL_NIF_TERM key,
		      const ERL_NIF_TERM value,
		      varp_config_t* opt)
{
    if (key == ATOM(size)) {
	if (value == ATOM(default))
	    opt->vsize = DEFAULT_MAP_SIZE;
	else if (!vif_get_size_t(env, value, &opt->vsize))
	    return 0;
	else if ((opt->vsize < 2) || (opt->vsize > MAX_MAP_SIZE))
	    return 0;
    }
    else if ((key == ATOM(qtype)) && (value == ATOM(fifo))) {
	opt->qtype = fifo;
    }
    else if ((key == ATOM(qtype)) && (value == ATOM(lifo))) {
	opt->qtype = lifo;
    }
    else if ((key == ATOM(qtype)) && (value == ATOM(recursive))) {
	opt->qtype = recursive;
    }	
    else if (key == ATOM(xref) && enif_is_true(env, value)) {
	opt->xref = true;
    }
    else if (key == ATOM(xref) && enif_is_false(env, value)) {
	opt->xref = false;
    }
    else if (key == ATOM(hash) && enif_is_true(env, value)) {
	opt->hash = true;
    }
    else if (key == ATOM(hash) && enif_is_false(env, value)) {
	opt->hash = false;
    }
    else if (key == ATOM(use_phase) && enif_is_true(env, value)) {
	opt->use_phase = true;
    }
    else if (key == ATOM(use_phase) && enif_is_false(env, value)) {
	opt->use_phase = false;
    }
    else if (key == ATOM(phase) && enif_is_true(env, value)) {
	opt->init_phase = I_TRUE;
    }
    else if (key == ATOM(phase) && enif_is_false(env, value)) {
	opt->init_phase = I_FALSE;
    }
    else if (key == ATOM(edge) && enif_is_true(env, value)) {
	opt->edge = true;
    }
    else if (key == ATOM(edge) && enif_is_false(env, value)) {
	opt->edge = false;
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
	if (key == ATOM(level)) {
	    int level;
	    if (!enif_get_int(env, value, &level)) return 0;
	    if (level < -1) return 0;
	    opt->level = level;
	    return 0;
	}
	else if (key == ATOM(set)) {
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
	else if (key == ATOM(queue)) {
	    bool_t queue;
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

static int symtab_grow(varp_t* vp)
{
    size_t size0 = dynvar_size(vp->symtab);
    size_t size  = next_pow2(size0);
    int i;

    fprintf(stderr, "symtab_grow\r\n");

    if (dynvar_resize(vp->symtab, size) < 0)
	return -1;
    
    // clear new links
    memset(vp->symtab+size0, 0, (size-size0)*sizeof(symbol_t*));
    // move elements that rehash the lower part and move elements
    // that rehash to the upper part
    for (i = 0; i < (int)size0; i++) {
	symbol_t** spp = &vp->symtab[i];
	symbol_t* sp;
	while((sp = *spp) != NULL) {
	    int j = sp->hvalue & (size-1);  // hash with new size
	    if (i == j) { // element stay
		spp = (symbol_t**) &(sp->link.next);
	    }
	    else { // element move to new location j=(i+2^r) (top half)
		*spp = (symbol_t*) sp->link.next;
		sp->link.next = (cdlink_t*) vp->symtab[j];
		vp->symtab[j] = sp;
	    }
	}
    }
    return 0;
}


static symbol_t* symbol_lookup(varp_t* vp, ErlNifBinary* bp,
			       uint32_t hvalue, bool_t is_term)
{
    size_t hsize = dynvar_size(vp->symtab);
    if (hsize > 0) {
	int hix  = hvalue & (hsize - 1);
	symbol_t* sp = vp->symtab[hix];
	while(sp != NULL) {
	    if ((sp->hvalue == hvalue) &&
		(sp->size == bp->size) &&
		(sp->is_term == is_term) &&
		(memcmp(sp->data, bp->data, bp->size) == 0))
		return sp;
	    sp = (symbol_t*) sp->link.next;
	}
    }
    return NULL;
}

// create a new symbol
static symbol_t* symbol_create(varp_t* vp, variable_t* var, ErlNifBinary* bp,
			       uint32_t hvalue, bool_t is_term)
{
    symbol_t* sp;
    
    if ((sp = obj_alloc(&vp->sym_allocator)) == NULL)
	return NULL;
    sp->is_term = is_term;
    sp->hvalue = hvalue;
    sp->var  = var;    
    // copy term or binary (add +1 for nil termination)
    sp->data = VARP_ALLOC(bp->size+1);
    memcpy(sp->data, bp->data, bp->size);
    sp->data[bp->size] = '\0';
    sp->size = bp->size;
    if (!is_term && (var->strname == NULL))
	var->strname = (char*) sp->data;
    if (var->strname) {
	fprintf(stderr, "create symbol '%s'\r\n", var->strname);
    }
    return sp;
}

static int symbol_insert(varp_t* vp,variable_t* var, symbol_t* sp)
{
    int i;

    if (vp->snum+1 >= dynvar_size(vp->symtab)) // rehash
	symtab_grow(vp);

    i = sp->hvalue & (dynvar_size(vp->symtab)-1);
    sp->anext = var->names;  // link alias list
    var->names = sp;
    // link hash bucket list
    sp->link.next = (cdlink_t*) vp->symtab[i];
    vp->symtab[i] = sp;
    vp->snum++;
    if (var->strname != NULL) {
	fprintf(stderr, "insert symbol '%s' slot = %d\r\n", var->strname, i);
    }
    return 0;
}

static symbol_t* symbol_copy(varp_t* vp, variable_t* var, symbol_t* sp0)
{
    symbol_t* sp;
    
    if ((sp = obj_alloc(&vp->sym_allocator)) == NULL)
	return NULL;
    sp->is_term = sp0->is_term;
    sp->hvalue = sp0->hvalue;
    sp->var  = var;
    // copy term or binary
    sp->data = VARP_ALLOC(sp0->size+1);
    memcpy(sp->data, sp0->data, sp0->size);
    sp->data[sp0->size] = '\0';
    sp->size = sp0->size;
    if (!sp->is_term && (var->strname == NULL))
	var->strname = (char*) sp->data;
    return sp;
}

// setup data-structure used by vp
static int setup(varp_t* vp, varp_config_t* config)
{
    size_t vsize, csize;
    int i;

    vp->opt = *config;

    vsize = MAX(1, vp->opt.vsize);
    csize = vp->opt.csize;

    vp->nmarked = 0;
    vp->marked_head = NULL;
    vp->marked_tailp = &(vp->marked_head);    

    if (dynvar_init(vp->var_map, vsize) < 0)
	goto error;

    DBG("var_map init\r\n");
    VALIDATE_MEMLIST();    
    
    dynvar_resize(vp->var_map, 1); // set size = 1 (include first constant)

    DBG("var_map resize\r\n");
    VALIDATE_MEMLIST();    
    
    cdlist_init(&vp->order_list);
    vp->order_next = NULL;
    
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
    if (dynvar_init(vp->lit_value, 2*PACKED_BYTES(vsize)) < 0)
	goto error;
    DBG("lit_value\r\n");
    VALIDATE_MEMLIST();        
    vp->lit_overlay = (uint16_t*) vp->lit_value;
#else
    if (dynvar_init(vp->var_value, PACKED_BYTES(vsize)) < 0)
	goto error;
    DBG("var_value\r\n");
    VALIDATE_MEMLIST();            
#endif
#endif
    
    if (dynvar_init(vp->symtab, DYN_SYMTAB_INIT) < 0)
	goto error;
    vp->snum  = 0;

    if (dynvar_init(vp->hashtab, DYN_HASHTAB_INIT) < 0)
	goto error;
    vp->hnum  = 0;

    dynvec_init(vp->clauseset,0,"[DELTA]", csize);
    dynvec_init(vp->clauseset,1,"[GAMMA]",0);
    dynvec_init(vp->clauseset,2,"[BETA]", 0);
    dynvec_init(vp->clauseset,3,"[ALPHA]", 0);

    for (i = 0; i < NUM_CSET; i++) {
	vp->cnum[i]  = 0;
	vp->coffs[i] = 0;
    }

    if (dynvar_init(vp->tlit, 0) < 0)
	goto error;

    vp->cdead = 0;
    vp->edead = 0;

    vp->unwatch = NULL;

    if (allocator_init(&vp->dyn_allocator, sizeof(dynarray_t)) < 0)
	goto error;
    if (allocator_init(&vp->var_allocator, sizeof(variable_t)) < 0)
	goto error;
    if (allocator_init(&vp->sym_allocator, sizeof(symbol_t)) < 0)
	goto error;
    if (allocator_init(&vp->sub_allocator, sizeof(subscription_t)) < 0)
	goto error;
    if (allocator_init(&vp->edge_allocator, sizeof(edge_t)) < 0)
	goto error;
    if (allocator_init(&vp->hlink_allocator, sizeof(hlink_t)) < 0)
	goto error;        

    slist_init(&vp->q);
    
    dynvar_init(vp->undo, 0);
    undo_set_size(vp, DYN_UNDO_INIT);

    vp->num_bound = 0;
    vp->num_subst = 0;
    vp->level = 0;
    
    // transient statistics
    vp->max_level = 0;
    vp->min_level = MAX_INT32;
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

    var_init(vp, &vp->constant, 0);
    vp->var_map[0] = &vp->constant;
    set_vv(vp, &vp->constant, I_TRUE);
    
    arc4_init(&vp->as);

    vp->subs = NULL;
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

    DBG("new varc instance\r\n");

    default_config(&opt.config);

    if (!parse_new_opts(env, argv[0], &opt))
	return enif_make_badarg(env);

    DBG("parse_new_opts\r\n");
    VALIDATE_MEMLIST();

    if (!(vp = enif_alloc_resource(varp_res, sizeof(varp_t))))
	goto error;
    memset(vp, 0, sizeof(varp_t));

    DBG("alloc_resource\r\n");
    VALIDATE_MEMLIST();

    
    if (setup(vp, &opt.config) < 0)
	goto error;

    DBG("setup\r\n");
    VALIDATE_MEMLIST();    
    
    varc = enif_make_resource(env,vp);
    enif_release_resource(vp);
    return varc;
error:
    if (vp)
	enif_release_resource(vp);
    return enif_make_badarg(env);
}

// add n variables return index to the first added
static int add_variables(varp_t* vp, size_t n)
{
    size_t k = dynvar_size(vp->var_map);
    size_t m = k + n;
    size_t cap = dynvar_capacity(vp->var_map);
    int j;
    
    if (dynvar_resize(vp->var_map, m) < 0)
	return -1;
    // only update rest of variable/values when capacity grows
    if (dynvar_capacity(vp->var_map) > cap) {
	cap = dynvar_capacity(vp->var_map);
#ifdef PACKED_VALUE
#ifdef LIT_VALUE
	if (dynvar_set_capacity(vp->lit_value, 2*PACKED_BYTES(cap)) < 0)
	    return -1;
	vp->lit_overlay = (uint16_t*) vp->lit_value;
#else
	if (dynvar_set_capacity(vp->var_value, PACKED_BYTES(cap)) < 0)
	    return -1;
#endif
#endif
    }
    for (j = (int)k; j < (int)m; j++) {
	variable_t* var;
	if ((var = obj_alloc(&vp->var_allocator)) == NULL)
	    return -1;
	cdlist_insert_last(&vp->order_list, var);
	var_init(vp, var, j);
	vp->var_map[j] = var;
	if (vp->order_next == NULL)
	    vp->order_next = var;
    }
    return (int)k;
}
    
// varc:add_variable(Vp:varc()[,Atom:boolean()]) -> integer()
static ERL_NIF_TERM varp_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    bool_t is_atom = 0;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (argc == 2) {
	if (!enif_get_boolean(env, argv[1], &is_atom))
	    return enif_make_badarg(env);
    }
    if (dynvar_size(vp->var_map) >= VLIMIT)
	enif_raise_exception(env, ATOM(system_limit));
    
    if ((i = add_variables(vp, 1)) < 0)
	return enif_make_badarg(env);
    
    vp->var_map[i]->is_atom = is_atom;

    return enif_make_int(env, i);
}

// varc:add_symbol(Vp:varc(),integer(),term()) -> ok | error
static ERL_NIF_TERM varp_add_symbol(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    ErlNifBinary bin;
    uint32_t hvalue;
    bool_t is_term = false;
    symbol_t* sp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (!vif_get_v(env, vp, argv[1], &var))
	return enif_make_badarg(env);

    if (!enif_inspect_iolist_as_binary(env, argv[2], &bin)) {
	if (!enif_term_to_binary(env, argv[2], &bin))
	    return enif_make_badarg(env);
	is_term = true;
    }

    hvalue = djb_hash(bin.data, bin.size);

    if ((sp = symbol_lookup(vp, &bin, hvalue, is_term)) != NULL) {
	if (is_term) enif_release_binary(&bin);
	return ATOM(error);
    }

    if ((sp = symbol_create(vp, var, &bin, hvalue, is_term)) == NULL)
	return enif_make_badarg(env);

    if (symbol_insert(vp, var, sp) < 0)
	return enif_make_badarg(env);

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

    sp = symbol_lookup(vp, &bin, hash, is_term);
    if (is_term) enif_release_binary(&bin);
    if (sp != NULL)
	return enif_make_int(env, sp->var->ix);
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
    if (argv[2] == ATOM(level))
	return enif_make_int(env, var->level);
    if (argv[2] == ATOM(phase))
	return enif_make_int(env, (var->phase == I_TRUE) ? 1 : -1);
    if (argv[2] == ATOM(is_atom))
	return enif_make_boolean(env, var->is_atom);
    if (argv[2] == ATOM(degree)) {
	if (!vp->opt.xref)
	    return enif_make_badarg(env);
	return enif_make_uint(env,
			      dynarray_size(var->lit[0].xref) +
			      dynarray_size(var->lit[1].xref));
    }
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
	if (!vp->opt.xref)
	    return enif_make_badarg(env);
	return enif_make_uint(env, dynarray_size(lp->xref));
    }
    if (argv[2] == ATOM(user))
	return enif_make_uint(env, lp->user);
    if (argv[2] == ATOM(edge)) {
	ERL_NIF_TERM list = enif_make_list(env, 0);
	edge_t* ep = lp->elist;
	
	while(ep) {
	    ERL_NIF_TERM elem = enif_make_int(env, export_l(ep->l));
	    list = enif_make_list_cell(env, elem, list);
	    ep = (edge_t*) ep->link.next;
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
		if (lp->neg)
		    term = enif_make_tuple2(env, ATOM(exclamation_mark), term);
	    }
	    else {
		size_t size = sp->size + lp->neg;
		uint8_t* data = enif_make_new_binary(env, size, &term);
		if (lp->neg)
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

void dump_order(char* label, varp_t* vp)
{
    int vn = (int)dynvar_size(vp->var_map);
    variable_t* var;

    enif_fprintf(stdout, "dump_order %s: |order-list|=%d,#num=%d,#bound=%d,#subst=%d,#unbound=%d\r\n",
		 label, cdlist_length(&vp->order_list),
		 vn-1, vp->num_bound, vp->num_subst,
		 (vn-1) - vp->num_bound);
    var = cdlist_first(&vp->order_list);
    while(var && !cdlist_is_eol(var)) {
	char* nmark = (var == vp->order_next) ? "*" : "";
	enif_fprintf(stdout, "[o=%e]%s%s=%s ",
		     var->link.order,
		     nmark,
		     format_literal(vp, vindex_ll(vp, phase_export(var))),
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

    prev = NULL;
    var = cdlist_first(&vp->order_list);
    while(!cdlist_is_eol(var)) {
	if ((prev != NULL) && !cdlist_is_after(var, prev)) {
	    enif_fprintf(stdout, "variable %s @%d is not ordered correct!\r\n",
			 format_variable(var), var->level);
	    dump_order("valid", vp);
	    return false;
	}
	if (!first_unbound && !variable_is_bound(vp, var)) {
	    first_unbound = true;	    
	    if ((vp->order_next != NULL) &&
		(var != vp->order_next) &&
		!cdlist_is_after(var, vp->order_next)) {
		enif_fprintf(stdout, "order_next is set incorrect!\r\n");
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
    while(!cdlist_is_eol(var)) {
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
			 format_literal(vp, vindex_ll(vp, i)), vp->level);
#endif
	    return enif_make_int(env, i);
	}
#ifdef VALIDATE_MODEL
	ASSERT(valid_model(vp));
#endif
    }
    else if (argc == 2) {
	variable_t* var;
	if (!vif_get_variable(env, vp, argv[1], &var))
	    return enif_make_badarg(env);
	if ((i = next_unbound_after(vp, var)) != 0) {
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "next_unbound=%s\r\n",
			 format_literal(vp, vindex_ll(vp, i)));
#endif
	    return enif_make_int(env, i);
	}
    }
    return ATOM(false);
}

#define ORDER_UNDEFINED  0x00   // "zero" order
#define ORDER_IDENTITY   0x01   // "input" order
#define ORDER_RANDOM     0x02   // "random" order
#define ORDER_DEGREE     0x03   // order according to occurence
#define ORDER_RANK       0x04   // 1/n1+...1/nk where ni is size of clause i
// #define ORDER_ACTIVITY   0x05   // order according to conflict activity
#define ORDER_USER       0x06   // order according to user count

#define ORDER_ASCEND     0x00   // ascending order
#define ORDER_DESCEND    0x80   // descending order
#define ORDER_INTERLEAVE 0x40   // interleve order

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
	    int j;
	    if (cp != NULL) {
		int n = cp->size;
		if (n > 0) {
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
	    int j;
	    if (cp != NULL) {
		int n = cp->size;
		if (n > 0) {
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

static void order_user(varp_t* vp, float* pkey, float* nkey, int vn)
{
    int i;
    pkey[0] = nkey[0] = 0.0;    
    for (i = 1; i < vn; i++) {
	variable_t* var = vp->var_map[i];
	pkey[i] = var->lit[LIT_POS].user;
	nkey[i] = var->lit[LIT_NEG].user;		
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

// move order_next if needed 
static inline void order_move_next(varp_t* vp, variable_t* var)
{
    if (!variable_is_bound(vp, var)) {
	if ((vp->order_next == NULL) ||
	    cdlist_is_before(var, vp->order_next))
	    vp->order_next = var;
    }
}

// remove var from order list, update order_next if needed
static void order_remove(varp_t* vp, variable_t* var)
{
    cdlist_t* list = &vp->order_list;    
    size_t n = cdlist_length(list);

    ASSERT(n > 0);
    
    if (n == 1) { // remove last element
	cdlist_remove(list, var);
	vp->order_next = NULL;
    }
    else if (n > 1) {
	if (var == vp->order_next) {
	    if (cdlist_is_last(list, var))
		vp->order_next = cdlist_prev(var);
	    else
		vp->order_next = cdlist_next(var);
	}
	cdlist_remove(list, var);
    }
}

static void order_insert_first(varp_t* vp, variable_t* var)
{
    cdlist_insert_first(&vp->order_list, var);
    order_move_next(vp, var);
}

static void order_insert_last(varp_t* vp, variable_t* var)
{
    cdlist_insert_last(&vp->order_list, var);
}

static void order_insert_before(varp_t* vp,variable_t* anchor,variable_t* var)
{
    cdlist_insert_before(&vp->order_list, anchor, var);
    order_move_next(vp, var);
}

static ERL_NIF_TERM varp_order_sort(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int arg = 0;
    int i, m, n;
    int order[2];
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    if (!enif_get_int(env, argv[1], &order[0]))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &order[1]))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[3], &arg))
	return enif_make_badarg(env);
    if (vp->level != 0)
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

    n = (int)dynvar_size(vp->var_map);
    
    {
	float nkey[2][n];
	float pkey[2][n];
	int sort_map[n];
	int sort_key[2];    // sort order -1,-2,1,2 (0=not used)
	
	for (i = 1; i < 3; i++) {
	    int k = i;
	    switch(order[i-1] & 0x0f) {
	    case ORDER_IDENTITY:
		order_identity(vp, pkey[k-1], nkey[k-1], n);
		break;
	    case ORDER_UNDEFINED:
		order_undefined(vp, pkey[k-1], nkey[k-1], n);
		k = 0;
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
	    case ORDER_USER:
		order_user(vp, pkey[k-1], nkey[k-1], n);
		break;
	    default:
		return enif_make_badarg(env);
	    }
	    if (order[i-1] & ORDER_DESCEND)
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
	vp->order_next = NULL;   // make sure we do not point on moved variables
    
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
	    k1 = abs(sort_key[0])-1;
	    k2 = abs(sort_key[1])-1;
	    for (i = 0; i < m; i++) {
		int j = sort_map[i];
		variable_t* var = vp->var_map[j];
		float r = pkey[k1][j] - nkey[k1][j];
		if (fabs(r) < EPSILON)
		    r = (pkey[k2][j] - nkey[k2][j]);
		var->phase = (r >= 0.0) ? I_TRUE : I_FALSE;
		cdlist_insert_last(&vp->order_list, var);
	    }
	    vp->order_next = vp->var_map[sort_map[0]];
#if defined(DEBUG_ORDER)
	    dump_order("order_sort", vp);
#endif
	}
    }
    ASSERT(valid_order(vp));
    return ATOM(ok);
}

static ERL_NIF_TERM varp_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int len;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);
    if (vif_get_literal_list(env, vp, argv[1], &len, NULL)) {
	literal_t* literals[len];
	int i;
	if (!vif_get_literal_list(env, vp, argv[1], &len, literals))
	    return enif_make_badarg(env);
	// insert all (reversed) first, will produce the correct order!
	for (i = len-1; i >= 0; i--) {
	    if (!cdlist_is_first(&vp->order_list, literals[i]->var)) {
		cdlist_remove(&vp->order_list, literals[i]->var);
		// FIXME insert before order_next!?
		order_insert_first(vp, literals[i]->var);
	    }
	}
	ASSERT(valid_order(vp));
	return ATOM(ok);	
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
	return enif_make_badarg(env);

    if (vif_get_literal_list(env, vp, argv[1], &len, NULL)) {
	literal_t* literals[len];
	int i;
	if (!vif_get_literal_list(env, vp, argv[1], &len, literals))
	    return enif_make_badarg(env);
	for (i = 0; i < (int)len; i++) {
	    if (!cdlist_is_last(&vp->order_list, literals[i]->var)) {
		order_remove(vp, literals[i]->var);
		order_insert_last(vp, literals[i]->var);
	    }
	}
	ASSERT(valid_order(vp));
	return ATOM(ok);	
    }
    return enif_make_badarg(env);
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
    return enif_make_boolean(env, !is_constant_l(vp, xp));
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
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);
    return enif_make_boolean(env, (xp == yp));
}

static int set_lit(ErlNifEnv* env, varp_t* vp, lit_t xp, ival_t val, int level)
{
    ival_t v;

    if ((v = get_l(vp, xp)) != I_UNDEF) {
	if (v != val)
	    return 0;
	return 1;
    }
    vp->caller_env = env;
    vp->undo[level].decision = xp;
    vp->undo[level].t = uSET;
    put_l(vp, xp, val, -1, CLAUSE_NONE, level);
    vp->caller_env = NULL;
    return 1;
}

static ERL_NIF_TERM varp_decide(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    varp_t* vp;
    int level = -1;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    // fixme assert xp is positive decide_phase does the work
    if (argc == 3) {
	if (!enif_get_int(env, argv[2], &level) || (level < 0) ||
	    (level >= (int)dynvar_size(vp->undo)))
	    return enif_make_badarg(env);
    }
    if (level < 0) level = vp->level;
    if (!set_lit(env, vp, xp, decide_phase(vp, xp), level))
	return enif_make_boolean(env, false);
    return enif_make_boolean(env, true);
}

static ERL_NIF_TERM varp_bind(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp;
    varp_t* vp;
    int level = -1;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    if (argc == 3) {
	if (!enif_get_int(env, argv[2], &level) || (level < 0) ||
	    (level >= (int)dynvar_size(vp->undo)))
	    return enif_make_badarg(env);
    }
    if (level < 0) level = vp->level;
    if (!set_lit(env, vp, xp, I_TRUE, level))
	return enif_make_boolean(env, false);
    return enif_make_boolean(env, true);	
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
    if ((x == 0) || (ABS(x) >= (int)dynvar_size(vp->var_map))) {
	DBG("literal %d out of range\r\n", x);
	return enif_make_badarg(env);
    }
    if (!enif_get_uint(env, argv[2], &count))
	return enif_make_badarg(env);
    xp = vindex_ll(vp, x);
    xp->user = count;
    return ATOM(ok);
}


// check if dp - l is a sub-clause of cp
static bool_t is_subclause(clause_t* dp, lit_t l, clause_t* cp)
{
    int i, j;
    
    if (dp->size >= cp->size)
	return false;
    i = j = 0;
    while((i < (int)dp->size) && (j < (int)cp->size)) {
	if (dp->lit[i] == l)
	    i++;
	else if (dp->lit[i] == cp->lit[j]) {
	    i++;
	    j++;
	}
	else {
	    if (abs(export_l(dp->lit[i])) < abs(export_l(cp->lit[j])))
		return false;
	    j++;
	}
    }
    if (i == (int)dp->size) // all match
	return true;
    return false;
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


// Minimize a clause wrt implication clauses as subclauses
static ERL_NIF_TERM varp_minimize(ErlNifEnv* env, int argc,
				  const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t  cix;
    clause_t* cp;
    int i,n;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);
    if ((cp = get_clause(vp, cix)) == NULL)
	return enif_make_badarg(env);
    if (GET_SI(cix) != ALPHA)
	return enif_make_badarg(env);

    if (cp->size == 1)
	return enif_make_int(env, 1);

    dynvar_resize(vp->tlit, 0);
	
    n = (int) cp->size;
    for (i = 0; i < n; i++) {
	lit_t li = cp->lit[i];
	variable_t* var = var_l(vp, li);
	if ((cix = var->implication_clause) == CLAUSE_NONE)
	    *dynvar_add(vp->tlit) = li;
	else {
	    clause_t* dp = get_clause(vp, cix);
	    bool_t is_sub = is_subclause(dp, neg_l(li), cp);
	    if (!is_sub)
		*dynvar_add(vp->tlit) = li;
	}
    }
    
    ASSERT(dynvar_size(vp->tlit) > 0);

    if (dynvar_size(vp->tlit) < cp->size) {
	size_t size = dynvar_size(vp->tlit);
	uint32_t hvalue;
	cix_t cix;
	
	hvalue = literal_array_hash(vp, vp->tlit, size);
	if ((cix=clauseset_find(vp,vp->tlit,size,ALPHA,hvalue))!=CLAUSE_NONE) {
	    cix = cp->cix;
	    clause_free(vp, cp);
	    clauseset_plug_hole(vp, ALPHA, GET_IX(cix));
	    return ATOM(undefined); // It is a copy
	}
	memcpy(cp->lit, vp->tlit, size*sizeof(lit_t));
	cp->hvalue = hvalue;
	cp->size = size;
	cp->select = (size > 3) ? 3 : size-1;
    }
    return enif_make_int(env, cp->size);
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

static inline void clause_watch_insert(varp_t* vp, clause_t* cp,
				       long p1, long p2)
{
    wlink_set(&cp->wl[0], p1, l2ll(vp, cp->lit[p1]));
    wlink_set(&cp->wl[1], p2, l2ll(vp, cp->lit[p2]));
}


static int clause_watch(varp_t* vp, clause_t* cp)
{
    int va[3], la[3];
    long pa[3];
    long p;
    bool_t dead = false;
    int nfalse = 0;
    int lev;
    
    la[0] = la[1] = la[2] = -1;
    pa[0] = pa[1] = pa[2] = -1;

    for (p = (int)cp->size-1; p >=0; p--) {
	lit_t l = cp->lit[p];
	switch(get_l(vp,l)) {
	case I_TRUE:
	    dead = true;
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

    if ((pa[0] < 0) || (pa[1] < 0)) {
	printf("Could not set TWL\r\n");
	return -1;
    }
*/

    // setup watch
    clause_watch_insert(vp, cp, pa[0], pa[1]);

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

static void xref_add(varp_t* vp, clause_t* cp, pos_t p)
{
    literal_t* lp = l2ll(vp, cp->lit[p]);
    xref_t* xp;
    
    if (lp->xref == NULL)
	lp->xref = dynarray_empty(vp, "xref", sizeof(xref_t));
    xp = dynarray_add(lp->xref);
    xp->cix  = cp->cix;
    xp->p    = p;
}

// locate and remove xref link
static inline void xref_del(varp_t* vp, clause_t* cp, pos_t p)
{
    literal_t* lp = l2ll(vp, cp->lit[p]);
    if (lp->xref != NULL) {
	xref_t* xptr  = dynarray_element(lp->xref,0);
	int xn = (int)dynarray_size(lp->xref);
	int i;

	for (i = 0; i < xn; i++) {
	    if ((xptr->cix == cp->cix) && (xptr->p == p)) {
		dynarray_delete(lp->xref, i);
		return;
	    }
	    xptr++;
	}
	DBG("xref not found for clause %lu pos = %ld\r\n", cp->cix, p);	
    }
}

static void xref_add_clause(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) { // since clauseset may temporary have holes!
	long n = (long)cp->size;
	long p;
	for (p = 0; p < n; p++)
	    xref_add(vp, cp, p);
    }
}

static void xref_del_clause(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) { // since clauseset may temporary have holes!
	long n = (long)cp->size;
	long p;
	for (p = 0; p < n; p++)
	    xref_del(vp, cp, p);
    }
}

static int clause_link(varp_t* vp, clause_t* cp)
{
    if (vp->opt.xref)
	xref_add_clause(vp, cp);
    if (vp->opt.edge && (cp->size == 2)) {
	lit_t* lit  = cp->lit;
	edge_insert(vp, neg_l(lit[0]), lit[1], cp->cix);
	edge_insert(vp, neg_l(lit[1]), lit[0], cp->cix);
	cp->wl[0].p = -1;
	cp->wl[1].p = -1;
	// cp->flags |= CLAUSE_FLAG_DEAD;
	DBG("  edge-list added (no watch)\r\n");
	return 1;
    }
    return clause_watch(vp, cp);
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
	symbol_t* sp0;
	ival_t v = get_vv(vp0, var0);
	int j;
	
	switch(v) {
	case I_FALSE:
	case I_TRUE:
	    if (var0->level <= opt.level)
		set_vv(vp, var, v);
	    break;
	case I_BOUND:
	    bnd_vv(vp, var);
	    j = export_ll(var0->bound);
	    var->bound = vindex_ll(vp, j);
	    break;
	case I_UNDEF:
	default:
	    break;
	}

	// copy symbols (maybe use ref count?)
	sp0 = var0->names;
	while(sp0 != NULL) {
	    symbol_t* sp = symbol_copy(vp, var, sp0);
	    if (sp != NULL)
		symbol_insert(vp, var, sp);
	    sp0 = sp0->anext;
	}
    }

    if (opt.level >= (int)dynvar_size(vp->undo))
	undo_set_size(vp, dynvar_size(vp0->undo));
    
    for (i = 0; i <= opt.level; i++) {  // clone undo structure
	variable_t** dstp = &vp->undo[i].bs;
	variable_t* src;
	int li = export_l(vp0->undo[i].decision);
	vp->undo[i].decision = vindex_l(vp, li);
	vp->undo[i].t = vp0->undo[i].t;
	vp->undo[i].size = vp0->undo[i].size;
	
	src = vp0->undo[i].bs;
	dstp = &vp->undo[i].bs;
	while(src) {
	    int ix = src->ix;
	    variable_t* dst = vp->var_map[ix];
	    dst->bound_next = NULL;
	    *dstp = dst;
	    dstp  = &dst->bound_next;
	    src = src->bound_next;
	}
    }

    if (opt.queue) {  // clone queue
	literal_t* src;

	src = slist_first(&vp0->q);
	while(!slist_is_eol(src)) {
	    int l = export_ll(src);
	    literal_t* dst = vindex_ll(vp, l);
	    slist_insert_last(&vp->q, dst);
	    src = slist_next(src);
	}
    }

    for (si = 0; si < NUM_CSET; si++) {
	if (opt.clauseset & (1 << si)) {
	    size_t n = dynvec_size(vp0->clauseset,si);
	    for (i = 0; i < (int)n; i++) {
		clause_t* cp = clause_copy(vp, vp0->clauseset[si][i]);
		if (cp != NULL) {
		    clause_insert(vp, si, cp, cp->hvalue);
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

    for (pl = nyp->elist; pl != NULL; pl = (edge_t*) pl->link.next) {
	literal_t* lp = l2ll(vp, pl->l);  // each L in !Y
	literal_t* nlp = neg_ll(lp);
	edge_t* ql;

	for (ql = nlp->elist; ql != NULL; ql = (edge_t*) ql->link.next) {
	    if (ql->l == yl)
		ql->l = xl;
	    // detect X, !X ? FIXME! MUST
	}
    }

    pl = nyp->elist;
    while(pl) {
	edge_t* pl1 = (edge_t*) pl->link.next;
	
	pl->link.next = (cdlink_t*)nxp->elist;
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
int valid_xref(literal_t* xp)
{
    xref_t* xptr = dynarray_element(xp->xref, 0);
    size_t  xsize = dynarray_size(xp->xref);

    while(xsize > 1) {
	if (!(xptr[0].cix < xptr[1].cix)) return 0;
	xptr++;
	xsize--;
    }
    return 1;
}

// substitute one literal
static void subst_ll(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp   = l2ll(vp, yl);
    literal_t* xp   = l2ll(vp, xl);
    literal_t* nxp  = neg_ll(xp);
    
    xref_t*    xptr = dynarray_element(xp->xref,0);
    size_t     xlen = dynarray_size(xp->xref);

    xref_t*    nxptr = dynarray_element(nxp->xref,0);
    size_t     nxlen = dynarray_size(nxp->xref);    
    
    xref_t*    yptr = dynarray_element(yp->xref,0);
    size_t     ylen = dynarray_size(yp->xref);

    dynarray_t* x1 = dynarray_create(vp, "x1", xlen+ylen, sizeof(xref_t));
    xref_t*    x1ptr = dynarray_element(x1,0);
    xref_t*    x1ptr0 = x1ptr;

    ASSERT (yp != xp);
    ASSERT(valid_xref(yp));

    // scan and rewrite all y's into x's
    while(ylen--) {
	cix_t   cix = yptr->cix;
	clause_t* cp = get_clause(vp, cix);
	int rewatch = 0;

	ASSERT(yl == cp->lit[yptr->p]);

	if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
	    clause_unwatch(vp, cp);
	    rewatch = 1;
	}

	while(xlen && (xptr->cix < cix)) {  // step x
	    *x1ptr++ = *xptr++;  // copy reference
	    xlen--;
	}

	while(nxlen && (nxptr->cix < cix)) { // step !x
	    nxptr++;
	    nxlen--;
	}

	if ( ((xlen==0) || (xptr->cix > cix)) &&
	     ((nxlen==0) || (nxptr->cix > cix)) )  { // Y only 
	    cp->lit[yptr->p] = xl;
	    cp->hvalue = literal_hash_del(cp->hvalue, yl);
	    cp->hvalue = literal_hash_add(cp->hvalue, xl);
	    if (rewatch) {
		if (clause_watch(vp, cp) <= 0) {
		    ASSERT(0);
		}
	    }
	    *x1ptr++ = *yptr;
	}
	else if ((xlen > 0) && (xptr->cix == cix)) { // X, Y
	    cp->lit[yptr->p] = L_FALSE(vp);
	    cp->hvalue = literal_hash_del(cp->hvalue, yl);
	    if (rewatch) {
		if (is_unit_clause(vp, cp)) {
		    // enif_fprintf(stdout, "unit clause in subst(%d,%d)\r\n",
		    // export_l(xl), export_l(yl));
		    // print_clause(vp, "unit", cp);
		    put_ll(vp, xp, I_TRUE, xptr->p, cp->cix, vp->level);
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
	else if ((nxlen > 0) && (nxptr->cix == cix)) { // !X, Y
	    cp->lit[yptr->p] = L_TRUE(vp);
	    cp->hvalue = literal_hash_del(cp->hvalue, yl);
	    // FIXME: swap away TRUE? (may not be a problem since dead)
	    if (!(cp->flags & CLAUSE_FLAG_DEAD)) {
		cp->flags |= CLAUSE_FLAG_DEAD;
		vp->cdead++;
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

    // enif_fprintf(stdout, "x-check: %s\r\n", format_literal(vp, xp));
    ASSERT(valid_xref(xp));
    // enif_fprintf(stdout, "x-check: %s\r\n", format_literal(vp, nxp));    
    ASSERT(valid_xref(nxp));
}

// check if x is bound to y
int is_bound(variable_t* x, variable_t* y)
{
    while(x) {
	if (x == y) return 1;
	if (x->bound == NULL) return 0;
	x = x->bound->var;
    }
    return 0;
}

// substitue [X/Y] == [X/Y], [!X/!Y]

static void subst(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp  = l2ll(vp, yl);
    literal_t* xp  = l2ll(vp, xl);
    variable_t* y = yp->var;
    
    ASSERT(yp != xp);
    ASSERT(get_vv(vp, y) == I_UNDEF);

/*
    enif_fprintf(stdout,"replace x=%d/%s for y=%d/%s\r\n",
		 export_l(xl),format_ival(get_l(vp,xl)),
		 export_l(yl),format_ival(get_l(vp,yl)));
*/

    vp->num_subst++;
    vp->num_bound++;
    log_permanent(vp, xp, yp, 0);

    subst_ll(vp, xl, yl);
    subst_ll(vp, neg_l(xl), neg_l(yl));

    if (vp->opt.edge)
	subst_2_clause(vp, xl, yl);
    
    ASSERT(!is_bound(xp->var, y)); // check circular 
    
    bnd_vv(vp, y);     // mark Y as bound (to X)
    if (is_neg_l(yl))
	y->bound = l2ll(vp, neg_l(xl));
    else
	y->bound = xp;
}

static ERL_NIF_TERM varp_subst(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    lit_t xp, yp;
    ival_t x, y;
    varp_t* vp;
    variable_t* xv;
    variable_t* yv;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_lit(env, vp, argv[1], &xp))
	return enif_make_badarg(env);
    // enif_fprintf(stdout,"xp=%d value=%s\r\n",
    //   export_l(xp),format_ival(get_l(vp,xp)));
    if (!vif_get_lit(env, vp, argv[2], &yp))
	return enif_make_badarg(env);
    // enif_fprintf(stdout,"yp=%d value=%s\r\n",
    //   export_l(yp),format_ival(get_l(vp,yp)));
		 
    if (!vp->opt.xref) // must enable cross reference!
	return enif_make_badarg(env);
    // enif_fprintf(stdout,"xref=ok\r\n");
    if (vp->level != 0) // only on level 0!
	return enif_make_badarg(env);
    // enif_fprintf(stdout,"level=0\r\n");
    
    y = get_l(vp, yp);
    if (IS_CONSTANT(y)) {
	// enif_fprintf(stdout,"y=%s\r\n", format_ival(y));	
	return enif_make_badarg(env);
    }

    x = get_l(vp, xp);
    if (IS_CONSTANT(x)) {
	// enif_fprintf(stdout,"x=%s\r\n", format_ival(x));
	return enif_make_badarg(env);
    }

    xv = var_l(vp, xp);
    yv = var_l(vp, yp);

    vp->caller_env = env;
    if (xv != yv) subst(vp, xp, yp);
    vp->caller_env = NULL;    
    return enif_make_boolean(env, true);
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
    return enif_make_boolean(env, true);
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
    if (level < (int)dynvar_size(vp->undo))
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
    if (level < (int)dynvar_size(vp->undo))
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
	(src < 0) || (src >= (int)dynvar_size(vp->undo)))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[2], &dst) ||
	(dst < 0) || (src >= (int)dynvar_size(vp->undo)))
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
// is called when at least one literal was set to FALSE!
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

    ASSERT (!vp->opt.edge);
    l = cp->lit[wl1->p];  // FIXME: make p = l for binary case!
    if ((lw = get_l(vp, l)) == I_TRUE) {
	COUNT(vp, CLAUSE_D);
	return EV_DEAD;
    }
    if (lw == I_FALSE)
	return EV_CONFLICT;
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
	put_nq_ll(vp, lp1, I_TRUE, wl1->p, cp->cix, vp->level);
	return lp1;
    case I_UNDEF:
    case I_BOUND:
    default:
	// convert 3-clause into 2-clause edge-list?
	// the 3-clause is then dead because it is evaluated by
	// edge lists
	if ((vp->opt.edge) && (vp->level == 0)) {
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
    DBG_BCP("%sMovewp3: %s %d=>%ld\r\n", indent(vp->level), format_lit(vp, cp->lit[wl0->p]), wl0->p, p);
    *wlp = wl0->next;
    wlink_set(wl0, p, l2ll(vp,l));
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
		DBG_BCP("%sMovewp: %s %d=>%ld\r\n",
			indent(vp->level),
			format_lit(vp, cp->lit[wl0->p]), wl0->p, p);
		*wlp = wl0->next;
		wlink_set(wl0, p, l2ll(vp, cp->lit[p]));
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
	
	DBG_BCP("%sEdge: %s -> %s\r\n",
		indent(vp->level),format_literal(vp, lp),format_lit(vp, ep->l));
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
	    put_nq_ll(vp, lp1, I_TRUE, 1, ep->cix, vp->level);
	    if (vp->level == 0) {
		// unlink dead edge!
		*epp = (edge_t*) ep->link.next;
		obj_free(&vp->edge_allocator, ep);
		vp->edead++;
		cont = 1;
	    }
	    if (vp->opt.qtype == recursive) {
		if (bcp1(vp, neg_ll(lp1)) < 0)
		    goto conflict;
	    }
	    else {
		lqueue_insert_ll(vp, neg_ll(lp1));
	    }
	    if (cont)
		continue;
	    break;
	case I_BOUND:
	default:
	    ASSERT(0);
	    break;
	}
	epp = (edge_t**) &(ep->link.next);
    }
    return 0;
conflict:
    return -1;
}

static int is_turbo_clause(varp_t* vp, clause_t* cp, lit_t x, lit_t* zp)
{
    lit_t* yp = cp->lit;
    size_t n  = cp->size;

    while(n--) {
	lit_t y = *yp++;
	if ((y != x) && (get_l(vp,y) == I_TRUE)) {
	    *zp = y;
	    return 1;
	}
    }
    return 0;
}

static int bcp_turbo(varp_t* vp, lit_t xp)
{
    literal_t* lp = l2ll(vp, xp);
    xref_t* xptr  = dynarray_element(lp->xref, 0);
    size_t  n     = dynarray_size(lp->xref);
    lit_t q[n+1];  // preparation for bj clause!
    int j;

#if defined(DEBUG_BCP)
    if (!vp->opt.xref) enif_fprintf(stdout, "turbo without xref!\r\n");
#endif
    if (n == 0)
	return 0;
    j = 1;
    while(n--) {
	clause_t* cp = get_clause(vp, xptr->cix);
	if (cp != NULL) {
	    enif_fprintf(stdout,"turbo check %s\r\n", format_lit(vp, xp));
	    print_lit_array("trubo check", cp->lit, cp->size);
	    if (!is_turbo_clause(vp,cp,xp,&q[j]))
		return 0;
	    j++;
	}
	xptr++;
    }
    q[0] = xp;
    print_lit_array("TURBO clause", q, j);
    return 1;
}

int bcp_is_looping(literal_t* lp)
{
    wlink_t* wl0 = lp->wlist;
    wlink_t* wl = wl0;

    while(wl) {
	wl = wl->next;
	if (wl == wl0) return 1; // loop!
    }
    return 0;
}

// bcp literal chain lp
static int bcp_clauses(varp_t* vp, literal_t* lp0)
{
    wlink_t** wlp = &lp0->wlist;
    wlink_t*  wl;
    literal_t* lp = lp0;

    DBG_BCP("%sBcp_clauses: %s\r\n", indent(vp->level),
	    format_literal(vp, neg_ll(lp)));
    ASSERT(!bcp_is_looping(lp));
    
    while((wl = *wlp) != NULL) {
	clause_t* cp = clause_pointer(wl);
#if defined(DEBUG_BCP)
	print_sym_clause(vp, "  bcp: ", cp);
#endif
	if (!(cp->flags & (CLAUSE_FLAG_CONFLICT|CLAUSE_FLAG_DEAD))) {
	    int i = wlink_index(wl);
	    wlink_t* wl0 = &cp->wl[i];
	    wlink_t* wl1 = &cp->wl[1-i];
	    switch((cp->select)&3) {
	    case 1:
		lp = bcp_2_clause(vp, cp, wl1);
		break;
	    case 2:
		lp = bcp_3_clause(vp, cp, wl0, wl1, wlp);
		break;
	    case 3:
		lp = bcp_n_clause(vp, cp, wl0, wl1, wlp, cp->size);
		break;
	    default:
		enif_fprintf(stdout, "clause %d:%d select=%d\r\n",
			     GET_SI(cp->cix), GET_IX(cp->cix),
			     cp->select);
		print_sym_clause(vp, "  bcp: ", cp);		
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
		if (vp->opt.qtype == recursive) {
		    if (bcp1(vp, neg_ll(lp)) < 0)
			return -1;
		}
		else {
		    lqueue_insert_ll(vp, neg_ll(lp));
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
    int r;
    DBG_BCP("%sBcp1: %s\r\n",indent(vp->level),format_literal(vp, neg_ll(lp)));
    r = bcp_clauses(vp, lp);
    // keep bcp_edge_list after bcp_clauses since some clauses may
    // be converted to edge lists by bcp_clauses
    if ((r >= 0) && vp->opt.edge)
	r = bcp_edge_list(vp, neg_ll(lp));
    if ((vp->level == 0) && vp->opt.xref)
	kill_clauses(vp, neg_ll(lp));
    return r;
}

static int bcp(varp_t* vp)
{
    literal_t* lp;
    DBG_BCP("%sBcp: %s\r\n",
	    indent(vp->level), format_literal(vp, slist_first(&vp->q)));
    while((lp = lqueue_deq(vp)) != NULL) {
	if (bcp1(vp, lp) < 0)
	    return -1;
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
	else if (vp->opt.edge && (cp->flags&CLAUSE_FLAG_TWO)) { // 3 -> 2 clause
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
	clause_unwatch(vp, cp);
	cp->flags &= ~CLAUSE_FLAG_UNWATCH;
	cp = cp->uwatch;
    }
    vp->unwatch = NULL;    
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
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    
    vp->caller_env = env;
    vp->bcp_counter++;
    vp->num_conflicting = 0;
    bcp(vp);
    vp->caller_env = NULL;

    if (vp->unwatch)
	bcp_unwatch(vp);

    if (vp->level > vp->max_level)     vp->max_level = vp->level;
    if (vp->num_bound > vp->max_bound) vp->max_bound = vp->num_bound;
    
    if (vp->num_conflicting) {
	if (vp->level < vp->min_level) vp->min_level = vp->level;
	vp->conflict_counter++;
	lqueue_clear(vp);
	DBG("num conflicts = %d\r\n", vp->num_conflicting);
	// clear all conflict flags
	unmark_cix_clauses(vp,vp->conflicting_clauses, vp->num_conflicting,
			   ~CLAUSE_FLAG_CONFLICT);
	return enif_make_boolean(env, false);
    }

    if (argc >= 2) {
	ERL_NIF_TERM list = argv[1];
	ERL_NIF_TERM head, tail;
	ERL_NIF_TERM turbo_list = enif_make_list(env, 0);
	size_t nturbo = 0;
	bool_t turbo_all = false;  // check all or first? first is default

	if (argc >= 3) {
	    if (!enif_get_boolean(env, argv[2], &turbo_all))
		return enif_make_badarg(env);
	}

	while (enif_get_list_cell(env, list, &head, &tail)) {
	    lit_t xp;
	    if (!vif_get_lit(env, vp, head, &xp))
		return enif_make_badarg(env);
	    if (bcp_turbo(vp, xp)) {
		if (!turbo_all)
		    return ATOM(turbo);
		turbo_list = enif_make_list_cell(env, head, turbo_list);
		nturbo++;
	    }
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
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
	if (vp->undo[level].decision != L_FALSE(vp)) {
	    literal_t* lp = l2ll(vp, vp->undo[level].decision);
#if defined(DEBUG_ORDER)
	    enif_fprintf(stdout, "undo_bound=%s@%d\r\n",
			 format_literal(vp, lp), level);
#endif
	    vp->order_next = lp->var;  // FIXME keep track on level!!!?
	}
	switch(vp->undo[level].t) {
	case uSET:
	    vp->undo[level].decision = neg_l(vp->undo[level].decision);
	    vp->undo[level].t = uTOGGLE;
	    return enif_make_boolean(env, true);
	case uTOGGLE:
	    printf("fixme: undo uTOGGLE\r\n");
	    return enif_make_boolean(env, false);
	case uDONE:
	    init_level(vp, level);
	    break;
	case uUNDEF:
	default:
	    printf("fixme: undo uUNDEF\r\n");
	    return enif_make_boolean(env, false);
	}
	if (level == 1)
	    break;
	vp->level--;
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
    // int i;
    int x;
    int level;
    lit_t xp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    level = vp->level;
    vp->num_conflicting = 0;
    vp->caller_env = env;
    
    DBG("nbcp: level=%d, t=%d, decision=%s\r\n",
	level, vp->undo[level].t,
	format_lit(vp, vp->undo[level].decision));
    
    switch(vp->undo[level].t) {
    case uUNDEF:
        vp->undo[level].decision = L_FALSE(vp);
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
	// note xp is already toggled by undo!
	xp = vp->undo[level].decision;
	put_l(vp, xp, decide_phase(vp, xp),-1, CLAUSE_NONE, level);
	vp->undo[level].t = uDONE;
	DBG_ORDER("%sNbcp: t=uTOGGLE decision=%s\r\n",
		  indent(level), format_lit(vp, xp));
	goto bcp;

    case uDONE:
	printf("try to bcp t=uDONE state\r\n");
	vp->caller_env = NULL;	
	return enif_make_badarg(env);
    default:
	printf("unknown bcp state\r\n");
	vp->caller_env = NULL;
	return enif_make_badarg(env);
    }
    if (level == 0)
	goto bcp;
next:
    xp = vindex_l(vp, x);
    vp->undo[level].decision = xp;
    vp->undo[level].t = uSET;
    put_l(vp, xp, decide_phase(vp, xp),-1, CLAUSE_NONE, level);
    DBG_ORDER("%sNbcp: next decision=%s\r\n",
	      indent(level), format_lit(vp, xp));
bcp:
    vp->bcp_counter++;
    bcp(vp);
    if (vp->unwatch) bcp_unwatch(vp);
    if (vp->level > vp->max_level) vp->max_level = vp->level;
    if (vp->num_bound > vp->max_bound) vp->max_bound = vp->num_bound;
    
    if (vp->num_conflicting == 0) {
	x = next_unbound(vp);
	DBG_ORDER("%sNbcp: step x=%d\r\n", indent(level), x);
	if (x == 0) {
	    vp->caller_env = NULL;
	    return enif_make_boolean(env, true);  // model 
	}
	set_level(vp, level+1);
	level = vp->level;
	goto next;
    }
    DBG_NBCP("%sContradiction\r\n", indent(level));
    // conflict found
    vp->caller_env = NULL;
    if (vp->level < vp->min_level) vp->min_level = vp->level;    
    vp->conflict_counter++;
    lqueue_clear(vp);
    DBG("num conflicts = %d\n", vp->num_conflicting);
    unmark_cix_clauses(vp,vp->conflicting_clauses, vp->num_conflicting,
		       ~CLAUSE_FLAG_CONFLICT);
    return enif_make_boolean(env, false);
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
    if (argv[1] == ATOM(max_conflicting)) {
	return enif_make_int(env, vp->max_conflicting);
    }
    if (argv[1] == ATOM(number_of_conflicting_clauses)) {
	return enif_make_int(env, vp->num_conflicting);
    } 
    if (argv[1] == ATOM(number_of_variables)) {
	return enif_make_int(env, dynvar_size(vp->var_map)-1);
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
    if (argv[1] == ATOM(number_of_learnt_clauses)) {
	return enif_make_int(env, vp->cnum[1]);
    }    
    if (argv[1] == ATOM(number_of_bound_variables)) {
	return enif_make_int(env, vp->num_bound);
    }
    if (argv[1] == ATOM(number_of_subst_variables)) {
	return enif_make_int(env, vp->num_subst);
    }    
    if (argv[1] == ATOM(number_of_unbound_variables)) {
	return enif_make_int(env, (dynvar_size(vp->var_map)-1) - vp->num_bound);
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
    if (argv[1] == ATOM(size)) {
	return enif_make_uint(env, vp->opt.vsize);
    }
    if (argv[1] == ATOM(qtype)) {
	switch(vp->opt.qtype) {
	case lifo: return ATOM(lifo);
	case fifo: return ATOM(fifo);
	case recursive: return ATOM(recursive);
	default: return ATOM(undefined);
	}
    }
    if (argv[1] == ATOM(max_level)) {
	int level = vp->max_level;
	vp->max_level = 0; // and reset
	return enif_make_int(env, level);
    }
    if (argv[1] == ATOM(min_level)) {
	int level = vp->min_level == MAX_INT32 ? 0 : vp->min_level;
	vp->min_level = MAX_INT32; // and reset
	return enif_make_int(env, level);
    }    
    if (argv[1] == ATOM(max_bound)) {
	int bound = vp->max_bound;
	vp->max_bound = 0;
	return enif_make_int(env, bound);
    }    
    if (argv[1] == ATOM(literal_size)) {
	return enif_make_uint(env, 8*sizeof(lit_t));
    }
    if (argv[1] == ATOM(literal_integer)) {
#ifdef LIT_INTEGER
	return enif_make_boolean(env, true);
#else
	return enif_make_boolean(env, false);
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
	return enif_make_boolean(env, vp->opt.edge);
    }
    if (argv[1] == ATOM(xref)) {
	return enif_make_boolean(env, vp->opt.xref);
    }
    if (argv[1] == ATOM(hash)) {
	return enif_make_boolean(env, vp->opt.hash);
    }
    if (argv[1] == ATOM(phase)) {
	return enif_make_boolean(env, (vp->opt.init_phase == I_TRUE));
    }
    if (argv[1] == ATOM(use_phase)) {
	return enif_make_boolean(env, vp->opt.use_phase);
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
    else if (argv[1] == ATOM(xref)) {
	bool_t enable;

	if (!enif_get_boolean(env, argv[2], &enable))
	    return enif_make_badarg(env);

	if (enable && !vp->opt.xref) { // xref all clauses
	    int i, si;
	    vp->opt.xref = true;
	    for (si = 0; si < NUM_CSET; si++) {
		size_t n = dynvec_size(vp->clauseset, si);
		for (i = 0; i < (int)n; i++)
		    xref_add_clause(vp, vp->clauseset[si][i]);
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
	return ATOM(ok);
    }
    else if (argv[1] == ATOM(hash)) {
	bool_t enable;
	if (!enif_get_boolean(env, argv[2], &enable))
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
	return ATOM(ok);
    }
    else if (argv[1] == ATOM(qtype)) {
	if (argv[2] == ATOM(fifo))
	    vp->opt.qtype = fifo;
	else if (argv[2] == ATOM(lifo))
	    vp->opt.qtype = lifo;
	else if (argv[2] == ATOM(recursive))
	    vp->opt.qtype = recursive;
	else
	    return enif_make_badarg(env);
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
    if (a->var->ix == 0)
	return 1;
    else if (b->var->ix == 0)
	return -1;
    else
	return a->var->ix - b->var->ix;
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

    PRINT_LIT_ARRAY("   src", lit, size);

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
#if defined(DEBUG_BCP)    
    enif_fprintf(stdout, "%sclause: ", indent(vp->level));
    print_sym_array_nl(vp, lit, size);
#endif
    
    return size;
}

static cix_t add_clause_array(varp_t* vp, int si, lit_t* lit,
			      size_t size, bool_t put_unit)
{
    clause_t* cp;
    cix_t cix;
    uint32_t hvalue;
    
    size = sort_clause_array(vp, lit, size, false);
    
    if (lit[size-1] == L_TRUE(vp))
	return CLAUSE_TRUE;

    if (size == 1) {  // unit
	if (lit[0] == L_FALSE(vp))
	    return CLAUSE_FALSE;
	if (put_unit) { // else make a real clause of the unit
	    put_l(vp, lit[0], I_TRUE, -1, CLAUSE_NONE, 0);
	    return CLAUSE_TRUE;
	}
    }

    if ((cp = clause_alloc(vp, size)) == NULL)
	return CLAUSE_NONE;
    hvalue = literal_array_hash(vp, lit, size);
    memcpy(cp->lit, lit, sizeof(lit_t)*size);
    if ((cix = clause_insert(vp, si, cp, hvalue)) == CLAUSE_NONE)
	return CLAUSE_NONE;
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
    unsigned int n;
    int len;
    int si = DELTA;
    cix_t cix;
    ERL_NIF_TERM ret;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (argc == 3) {
	if (!vif_get_si(env, argv[2], &si))
	    return enif_make_badarg(env);
    }

    if (!enif_get_list_length(env, argv[1], &n))
	return enif_make_badarg(env);
    dynvar_resize(vp->tlit, n);
    len = n;
    if (!vif_get_lit_list(env, vp, argv[1], &len, vp->tlit))
	return enif_make_badarg(env);
    vp->caller_env = env;
    if ((cix = add_clause_array(vp,si,vp->tlit,len,true)) == CLAUSE_NONE)
	ret = enif_make_badarg(env);
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
    unsigned int n;
    cix_t cix;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (!enif_get_list_length(env, argv[1], &n))
	return enif_make_badarg(env);
    else {
	lit_t literals[n];
	len = n;
	if (!vif_get_lit_list(env, vp, argv[1], &len, literals))
	    return enif_make_badarg(env);
	len = sort_clause_array(vp, literals, len, true);
	if ((cix = clause_find(vp, literals, len)) == CLAUSE_NONE)
	    return enif_make_boolean(env, false);
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
	unsigned int len;

	if (!enif_get_list_length(env, argv[1], &len))
	    return enif_make_badarg(env);
	else {
	    int csize = len;
	    ERL_NIF_TERM elem[csize];
	    uint8_t buffer[5*csize+1];
	    unsigned char* binptr;
	    int x;
	    int i;
	    int n = 0;
	    
	    if (!enif_get_list(env, argv[1], &csize, elem))
		return enif_make_badarg(env);

	    for (i = 0; i < csize; i++) {
		if (!enif_get_int(env, elem[i], &x))
		    return enif_make_badarg(env);
		n += compress_int(x, &buffer[n]);
	    }
	    buffer[n++] = 0;
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
	    uint8_t buffer[5*csize+1];
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

#define BUMP_RANK  -4  // bump implication clause number of steps
#define BUMP_LOG10 -3  // bump value = log10(<number-of-variables>)
#define BUMP_LOG2  -2  // bump value = log2(<number-of-variables>)
#define BUMP_NEXT  -1  // move variable as next unbound
#define BUMP_NONE   0

static void variable_bump(varp_t* vp, variable_t* var, int bump)
{
    variable_t* anchor;

    if (bump == BUMP_NONE)
	return;
    switch(get_vv(vp, var)) {
    case I_UNDEF: break;
    case I_TRUE:
    case I_FALSE:
	if (var->level == 0) return;
	break;
    case I_BOUND:	
    default: return;
    }
    
    if (bump < 0) {
	switch(bump) {
	case BUMP_RANK:
	    if (var->implication_clause != CLAUSE_NONE) {
		clause_t* cp = get_clause(vp, var->implication_clause);
		if (cp != NULL)
		    bump = cp->size;
	    }
	    break;
	case BUMP_LOG10: {
	    double n = (double) (dynvar_size(vp->var_map)-1);
	    bump = log10(n);
	    break;
	}
	case BUMP_LOG2: {
	    double n = (double) (dynvar_size(vp->var_map)-1);
	    bump = log2(n);
	    break;
	}
	case BUMP_NEXT: {
	    if ((vp->order_next != NULL) && (var != vp->order_next)) {
		order_remove(vp, var);
		order_insert_before(vp, vp->order_next, var);
	    }
	    return;
	}
	default:
	    return;
	}
    }
    
#if defined(DEBUG_ORDER)
    enif_fprintf(stdout, "bump variable %s@%d\r\n",
		 format_variable(var), vp->level);
    dump_order("bump-before", vp);
#endif
    if (bump <= 0) bump = 1;
    // undef or non-constants
    anchor = var;
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
		     (cdlist_is_first(&vp->order_list, anchor) ? "FIRST " : ""),
		     format_variable(anchor));
#endif
	order_insert_before(vp, anchor, var);
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
    int i;
    int level;
    int bump;
    double bumpf;
    variable_t* trail;
    literal_t* lp;
    cix_t cix;
    int step = 0;
    lit_t u;
    size_t size;
    uint32_t hvalue;
    clause_t* cp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0) || (level > vp->level))
	return enif_make_badarg(env);
    if (enif_get_double(env, argv[2], &bumpf))
	bump = dynvar_size(vp->var_map)*bumpf;
    else if (!enif_get_int(env, argv[2], &bump))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[3], &i)||(i < 0)||(i >= vp->num_conflicting))
	return enif_make_badarg(env);
    if ((trail = vp->undo[level].bs) == NULL)
	return enif_make_badarg(env);

    unmark_all(vp);  // must clear before use!
    
    cix = vp->conflicting_clauses[i];
    u = L_FALSE(vp);
    
    dynvar_resize(vp->tlit, 0);

    while (step >= 0) {
	if ((cp = get_clause(vp, cix)) == NULL) {
	    unmark_all(vp);
	    return enif_make_badarg(env);
	}
	cp->stamp = vp->bcp_counter;  // mark clause as used in conflict

	// conflict reason
	for (i = 0; i < (int)cp->size; i++) {
	    lit_t q;
	    if ((q = cp->lit[i]) != u) { // skip unit literal!
		literal_t* qp = l2ll(vp, q);
		int qlevel = qp->var->level;
		
		if (!is_marked(qp->var,MARK0) && (qlevel > 0)) {
		    variable_bump(vp, qp->var, bump);
		    mark(vp, qp->var, MARK0);
		    if (qlevel >= level)
			step++;
		    else
			*dynvar_add(vp->tlit) = q;
		}
	    }
	}

	while(trail && !is_marked(trail,MARK0))
	    trail = trail->bound_next;
	ASSERT(trail != NULL);
	lp = literal_vv(vp, trail);
	u = ll2l(vp, lp);
	if (step <= 1) {
	    *dynvar_add(vp->tlit) = neg_l(u);
	    goto make_clause;
	}
	else {
	    cix = trail->implication_clause;
	    unmark(lp->var, MARK0);
	    trail = trail->bound_next;
	    step--;
	}
    }

make_clause:
    unmark_all(vp);
    
    size = sort_clause_array(vp, vp->tlit, dynvar_size(vp->tlit), false);

    if (vp->tlit[size-1] == L_TRUE(vp))
	return enif_make_boolean(env, true);
	
    if (size == 1) {  // unit
	if (vp->tlit[0] == L_FALSE(vp))
	    return enif_make_boolean(env, false);
    }
    hvalue = literal_array_hash(vp, vp->tlit, size);
    // check if this clause alread exist in alpha
    if ((cix=clauseset_find(vp,vp->tlit,size,ALPHA,hvalue)) != CLAUSE_NONE)
	return ATOM(undefined); // It is a copy
    if ((cp = clause_alloc(vp, size)) == NULL)
	return enif_make_badarg(env);
    memcpy(cp->lit, vp->tlit, sizeof(lit_t)*size);
    if ((cix = clause_insert(vp, ALPHA, cp, hvalue)) == CLAUSE_NONE)
	return enif_make_badarg(env);
    return make_cix(env, cix);
}

static void clause_unlink(varp_t* vp, clause_t* cp)
{
    if ((cp->size == 2) && vp->opt.edge) {
	lit_t* lit  = cp->lit;
	edge_remove(vp, neg_l(lit[0]), lit[1], cp->cix);
	edge_remove(vp, neg_l(lit[1]), lit[0], cp->cix);
    }
    clause_unwatch(vp, cp);      // remove watched literals
    if (vp->opt.xref)
	xref_del_clause(vp, cp);
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

	switch(get_l(vp, xp)) {
	case I_TRUE:  return enif_make_boolean(env, true);
	case I_FALSE: return enif_make_boolean(env, false);
	case I_BOUND: return enif_make_badarg(env);
	case I_UNDEF:
	default:
	    vp->caller_env = env;
	    put_l(vp, xp, I_TRUE, -1, CLAUSE_NONE, 0);
	    vp->caller_env = NULL;
	    return enif_make_boolean(env, true);
	}
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

#ifdef VALIDATE_TWL

static void validate_implication_clause(varp_t* vp)
{
    int n = (int) dynvar_size(vp->var_map);
    int i;

    for (i = 1; i < n; i++) {
	cix_t cix = vp->var_map[i]->implication_clause;
	if (cix != CLAUSE_NONE) {
	    if (get_clause(vp, cix) == NULL) {
		enif_fprintf(stdout, "%d: implication clause %d:%d DELETED\r\n",
			     i, GET_SI(cix), GET_IX(cix));
	    }
	}
    }
}

static void validate_twl(varp_t* vp)
{
    int n = (int) dynvar_size(vp->var_map);
    int i;

    for (i = 1; i < n; i++) {
	int j;
	for (j = 0; j < 2; j++) {
	    literal_t* lp = &vp->var_map[i]->lit[j];
	    // check wlink chain!
	    wlink_t* wp = lp->wlist;

	    while(wp) {
		clause_t* cp = clause_pointer(wp);
		int wi = wlink_index(wp);
		
		if (get_clause(vp, cp->cix) != cp) {
		    enif_fprintf(stdout, "wlink: %s wi=%d clause %d:%d does not map\r\n",
				 format_literal(vp, lp), wi, GET_SI(cp->cix), GET_IX(cp->cix));
		}
		wp = wp->next;
	    }
	}
    }
}
#endif

// delete a clause by index or literal list
// may only delete clauses on level 0!
static ERL_NIF_TERM varp_del_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    cix_t cix;
    clause_t* cp;
    int si;
    int ix;
    
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
	    if ((cix = clause_find(vp, literals, size)) == CLAUSE_NONE)
		return enif_make_badarg(env);
	}
    }

    if (vp->level != 0)
	return enif_make_badarg(env);

    si = GET_SI(cix);
    ix = GET_IX(cix);

    if ((cp = get_clause(vp,cix)) == NULL)
	return enif_make_badarg(env);

#ifdef VALIDATE_TWL
    if (cp->stamp == vp->bcp_counter) {
	enif_fprintf(stdout, "deleting a new clause %d:%d\r\n",
		     si, ix);
    }
#endif
    
    clause_remove(vp, cp);

    ASSERT(get_clause(vp, cix) == NULL);

    clauseset_plug_hole(vp, si, ix);
    
#ifdef VALIDATE_TWL
    validate_twl(vp);
    validate_implication_clause(vp);
#endif

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

    clause_unlink(vp, cp);
    if (cp->flags & CLAUSE_FLAG_DEAD) goto remove;
    size = sort_clause_array(vp, lit, size, false);
    if (lit[size-1] == L_TRUE(vp))
	goto remove;
    if ((size == 1) && (lit[0] == L_FALSE(vp)))
	goto error;
    cp->size = size;

    clause_link(vp, cp);
    return ATOM(ok);
    
remove:
    DBG("  %lu-removed\r\n", size);
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
	    *epp = (edge_t*) ep->link.next;
	    obj_free(&vp->edge_allocator, ep);
	}
	else
	    epp = (edge_t**) &(ep->link.next);
    }
    return ATOM(ok);
}

static int cmp_xref QSORT_ARGS(const void* a, const void* b,void* arg)
{
    UNUSED(arg);
    if (((xref_t*) a)->cix < ((xref_t*) b)->cix)
	return -1;
    else if (((xref_t*) a)->cix > ((xref_t*) b)->cix)
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
    xref_t* xptr0 = dynarray_element(lp->xref, 0);
    xref_t* xptr = xptr0;
    size_t len0  = dynarray_size(lp->xref);
    size_t len = len0;

    while(len--) {
	remap_cix(&xptr->cix, "xref", si, remap, n);
	xptr++;
    }
    // must sort for subst to work!
    QSORT(xptr0, len0, sizeof(xref_t), cmp_xref, NULL);
}


static void edge_remap(literal_t* lp, int si, int* remap, int n)
{
    edge_t* ep = lp->elist;
    while(ep != NULL) {
	remap_cix(&ep->cix, "edge", si, remap, n);
	ep = (edge_t*) ep->link.next;
    }
}

static void hashtab_remap(varp_t* vp,int i,int si,int* remap,int n)
{
    hlink_t* hp = vp->hashtab[i];
    while (hp != NULL) {
	remap_cix(&hp->cix, "hash", si, remap, n);
	hp = (hlink_t*) hp->link.next;
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
	return enif_make_badarg(env);
    
    if ((n=(int)dynvec_size(vp->clauseset, si)) == 0)
	return ATOM(ok);

    cm = vp->clauseset[si];

    QSORT(cm, n, sizeof(clause_t*), cmp_stamp, vp);

//    enif_fprintf(stdout, "SORTED clauses si=%d\n", si);
//    print_clauseset(vp, si, n);


    {
	int rmap[n];
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
	if (vp->opt.edge) {
	    size_t vn = dynvar_size(vp->var_map);
	    for (i = 1; i < (int)vn; i++) {
		edge_remap(&vp->var_map[i]->lit[0], si, rmap, n);	    
		edge_remap(&vp->var_map[i]->lit[1], si, rmap, n);
	    }
	}
	if (vp->opt.hash && (si != ALPHA)) {
	    size_t hn = dynvar_size(vp->hashtab);
	    for (i = 0; i < (int)hn; i++)
		hashtab_remap(vp, i, si, rmap, n);
	}

//	enif_fprintf(stdout, "REMAPPED clauses si=%d\n", si);
//	print_clauseset(vp, si, n);	
    }
    return ATOM(ok);
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
	return ATOM(ok);
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
    bool_t raw = 0;
    literal_t* lp;
    ERL_NIF_TERM skip = ATOM(undefined);
    cix_t  cix;
    lit_t* lit;
    size_t csize;
    clause_t* cp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if (!vif_get_cix(env, vp, argv[1], &cix))
	return enif_make_badarg(env);

    if (argc >= 3) {
	if (argv[2] == ATOM(undefined))
	    skip = ATOM(undefined);
	else if (!vif_get_literal(env, vp, argv[2], &lp))
	    return enif_make_badarg(env);
	else
	    skip = external_ll(env,lp);
	if (argc >= 4) {
	    if (!enif_get_boolean(env, argv[3], &raw))
		return enif_make_badarg(env);
	}
    }

    if ((cp = get_clause(vp, cix)) == NULL)
	return enif_make_boolean(env, false);
    
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

// sort descending variable level
static int cmp_lev QSORT_ARGS(const void* ap,const void* bp,void* arg)
{
    varp_t* vp = (varp_t*) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);
    variable_t* av;
    variable_t* bv;
    
    if (a == b) return 0;
    av = var_l(vp, a);
    bv = var_l(vp, b);
    return bv->level - av->level;
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

    j1 = var_l(vp, vp->tlit[0])->level;
    j2 = var_l(vp, vp->tlit[1])->level;
    j3 = (cp->size == 2) ? 0 : var_l(vp, vp->tlit[2])->level;
    return enif_make_tuple6(env,
			    enif_make_long(env, cp->size),
			    enif_make_int(env, j1-j2),
			    enif_make_int(env, j2-j3),
			    enif_make_int(env, j2),
			    enif_make_int(env, j3),
			    make_cix(env, cp->cix));
}

// get status/watch0/watch1/watch/length
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

static ERL_NIF_TERM varp_bump(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t* var;
    int bump;
    double bumpf;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_variable(env, vp, argv[1], &var))
	return enif_make_badarg(env);
    if (enif_get_double(env, argv[2], &bumpf))
	bump = dynvar_size(vp->var_map)*bumpf;
    else if (!enif_get_int(env, argv[2], &bump))
	return enif_make_badarg(env);	
    variable_bump(vp, var, bump);
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
    else if (term == ATOM(number_of_subst_variables))
	*flag = SUB_FLAG_NUM_SUBST;    
    else if (term == ATOM(number_of_clauses))
	*flag = SUB_FLAG_NUM_CLAUSES;
    else if (term == ATOM(number_of_dead_clauses))
	*flag = SUB_FLAG_NUM_DEAD;
    else if (term == ATOM(max_level))
	*flag = SUB_FLAG_MAX_LEVEL;
    else if (term == ATOM(max_bound))
	*flag = SUB_FLAG_MAX_BOUND;
    else if (term == ATOM(min_level))
	*flag = SUB_FLAG_MIN_LEVEL;
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
    // link in first
    sp->link.next = (cdlink_t*) vp->subs;
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
	pl = (edge_t*) pl->link.next;
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
	if (vp->opt.edge) {
	    list = make_edge_list(env, vp, neg_ll(lp), list);
	    list = make_edge_list(env, vp, lp, list);
	}
    }
    else if (argv[2] == ATOM(literal)) {
	xref_t* xptr = dynarray_element(lp->xref, 0);
	size_t  xlen = dynarray_size(lp->xref);
	while(xlen--) {
	    if (get_clause(vp, xptr->cix) != NULL) {
		ERL_NIF_TERM elem = make_cix(env, xptr->cix);
		list = enif_make_list_cell(env, elem, list);
	    }
	    xptr++;
	}
    }
    else if (argv[2] == ATOM(variable)) {
	variable_t* var = lp->var;
	int i;

	for (i = 0; i < 2; i++) {
	    xref_t* xptr = dynarray_element(var->lit[i].xref, 0);
	    size_t  xlen = dynarray_size(var->lit[i].xref);
	    while(xlen--) {
		if (get_clause(vp, xptr->cix) != NULL) {
		    ERL_NIF_TERM elem = make_cix(env, xptr->cix);
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
    literal_t* lp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);    
    if ((lp = slist_first(&vp->q)) != NULL)
	return make_literal(env, lp);
    return enif_make_boolean(env, false);
}

// Get next literal in queue
static ERL_NIF_TERM varp_queue_next(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    literal_t* lp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);
    if (slist_is_empty(&vp->q))
	return enif_make_boolean(env, false);
    if (slist_next(lp) != NULL) 
	return make_literal(env, slist_next(lp));
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
    if (vp->undo[level].decision == L_FALSE(vp))
	return ATOM(f);
    else
	return enif_make_int(env, export_l(vp->undo[level].decision));
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
    switch(vp->undo[level].t) {
    case uSET:   return ATOM(set);
    case uTOGGLE: return ATOM(toggle);
    case uDONE: return ATOM(done);
    case uUNDEF:
    default:
	return ATOM(undefined);
    }
}

//
// get_bindings(Vp, Level, ClauseInfo, Trail, Tuple) ->
//    [literal()] | [{literal(),Pos,Index}] | { literal() }
//

static ERL_NIF_TERM varp_get_bindings(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    bool_t clause_info = false;
    bool_t trail = false;
    bool_t tuple = false;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &level) || (level<0))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[3], &trail))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[4], &tuple))
	return enif_make_badarg(env);
    
    if (level <= vp->level) {
	int size    = (int)vp->undo[level].size;
	variable_t* bp = vp->undo[level].bs;
	ERL_NIF_TERM element[size];
	int i = trail ? 0 : size-1;
	int s  = trail ? 1 : -1;

	while(bp) {
	    if (clause_info)
		element[i] = make_clause_info(env,vp,bp);
	    else
		element[i] = make_binding(env,vp,bp);
	    bp = bp->bound_next;
	    i += s;
	}
	if (tuple)
	    return enif_make_tuple_from_array(env, element, size);
	else
	    return enif_make_list_from_array(env, element, size);
    }
    if (tuple)
	return enif_make_tuple(env, 0);
    else
	return enif_make_list(env, 0);
}

//
// get_nbindings(Vp, Count, ClauseInfo, Trail) ->
//    [literal()] |[{literal(),Pos,Index}]
//
static ERL_NIF_TERM varp_get_nbindings(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int level;
    int size;
    bool_t clause_info = false;
    bool_t trail = false;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &size) || (size < 0))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[2], &clause_info))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[3], &trail))
	return enif_make_badarg(env);
    level = vp->level;
    {
	ERL_NIF_TERM elements[size];
	int i = 0;
	while((level >= 0) && (i < size)) {
	    variable_t* bp = vp->undo[level].bs;
	    while((bp != NULL) && (i < size)) {
		if (clause_info)
		    elements[i] = make_clause_info(env,vp,bp);
		else
		    elements[i] = make_binding(env,vp,bp);
		i++;
		bp = bp->bound_next;
	    }
	    level--;
	}
	return enif_make_list_from_array(env, elements, i);
    }
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
	(level >= (int)dynvar_size(vp->undo)))
	return enif_make_badarg(env);
    return enif_make_uint(env, vp->undo[level].size);
}

static inline void mark0_literal(varp_t* vp, literal_t* lp)
{
    if (!is_marked(lp->var,MARK0)) {
	if (lp->neg)
	    mark(vp, lp->var, MARK0|MARKN);
	else
	    mark(vp, lp->var, MARK0);
    }
}


static inline void mark1_literal(varp_t* vp, literal_t* lp)
{
    if (is_marked(lp->var,MARK0)) {
	int neg = is_marked(lp->var,MARKN);
	if (lp->neg == neg)
	    mark(vp, lp->var, MARK1);
    }
}


// Mark all literals in the list with MARK0 | MARKN
static ERL_NIF_TERM varp_mark_literals(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    const ERL_NIF_TERM* elem;
    int arity;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    
    unmark_all(vp);
    
    if (enif_get_tuple(env, argv[1], &arity, &elem)) { // as tuple
	int i;
	for (i = 0; i < arity; i++) {
	    literal_t* lp;
	    if (!vif_get_ll(env, vp, elem[i], &lp))
		return enif_make_badarg(env);
	    mark0_literal(vp, lp);
	}
    }
    else {  // as list
	list = argv[1];
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    literal_t* lp;
	    if (!vif_get_ll(env, vp, head, &lp))
		return enif_make_badarg(env);
	    mark0_literal(vp, lp);
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
    }	
    return ATOM(ok);
}

// Mark all literals that are marked as MARK0 with MARK1 (MARKN is checked)
// Then marked variables with both MARK0 and MARK1 are kept and
// marked as MARK0 together with MARKN flags, other marks are removed
// 
static ERL_NIF_TERM varp_mark_intersect(ErlNifEnv* env, int argc,
					const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    const ERL_NIF_TERM* elem;
    int arity;
    ERL_NIF_TERM list;
    ERL_NIF_TERM head, tail;
    variable_t*  var;
    variable_t** vpp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (enif_get_tuple(env, argv[1], &arity, &elem)) { // as tuple
	int i;
	for (i = 0; i < arity; i++) {
	    literal_t* lp;
	    if (!vif_get_ll(env, vp, elem[i], &lp))
		return enif_make_badarg(env);
	    mark1_literal(vp, lp);
	}
    }
    else {
	list = argv[1];
	while(enif_get_list_cell(env, list, &head, &tail)) {
	    literal_t* lp;
	    if (!vif_get_ll(env, vp, head, &lp))
		return enif_make_badarg(env);
	    mark1_literal(vp, lp);
	    list = tail;
	}
	if (!enif_is_empty_list(env, list))
	    return enif_make_badarg(env);
    }

    // remove elements not marked with both MARK0 and MARK1 and
    // remove MARK1 in case an element as both MARK0 and MARK1
    vpp = &vp->marked_head;
    while((var=*vpp) != NULL) {
	if (all_marked(var, MARK0|MARK1)) { // both marked
	    unmark(var, MARK1);             // keep MARK0 and MARKN
	    vpp = &var->mark_next;
	}
	else {
	    if ((*vpp = var->mark_next) == NULL) // remove if not both marked
		vp->marked_tailp = vpp;
	    vp->nmarked--;          // remove one element
	    var->mark = 0;          // not on list any more!
	}
    }
    return ATOM(ok);
}

// return a list/tuple of literals that are marked with MARK0 (|MARKN)
static ERL_NIF_TERM varp_get_marked(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    variable_t*  var;
    bool_t tuple = false;    

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[1], &tuple))
	return enif_make_badarg(env);
    {
	size_t size = vp->nmarked;
	ERL_NIF_TERM elements[size];
	int i = 0;
	var = vp->marked_head;
	while(var) {
	    if (is_marked(var,MARK0)) {
		int x = var->ix;
		if (is_marked(var,MARKN))
		    x = -x;
		elements[i++] = enif_make_int(env, x);
	    }
	    var = var->mark_next;
	}
	ASSERT(i == (int)size);

	if (tuple)
	    return enif_make_tuple_from_array(env, elements, size);
	else
	    return enif_make_list_from_array(env, elements, size);
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
	literal_t* xp;
	if (!vif_get_literal(env, vp, x, &xp))
	    return -1;
	if (is_marked(xp->var, MARK0)) {
	    int neg = is_marked(xp->var,MARKN);
	    if (neg == xp->neg)
		element[j++] = x;
	    else {
		ERL_NIF_TERM nx = make_literal(env, neg_ll(xp));
		element[j++] = enif_make_tuple2(env, var, nx);
	    }
	}
    }
    return j;
}

// intersect bindings (var=0) with bindings installed (var=1) return bindings
static ERL_NIF_TERM varp_mark_intersect_var(ErlNifEnv* env, int argc,
					    const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    const ERL_NIF_TERM* elem0;
    int arity;    
    unsigned len;
    ERL_NIF_TERM var;
    lit_t x;
    bool_t tuple = false;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    var = argv[1];
    if (!vif_get_lit(env, vp, argv[1], &x))
	return enif_make_badarg(env);
    if (!enif_get_boolean(env, argv[3], &tuple))
	return enif_make_badarg(env);
    if (enif_get_tuple(env, argv[2], &arity, &elem0)) { // as tuple
	int size;
	ERL_NIF_TERM element[arity];
	if ((size=mark_intersect_var(env, vp, var, elem0, element, arity)) < 0)
	    return enif_make_badarg(env);
	if (tuple)
	    return enif_make_tuple_from_array(env, element, size);
	else
	    return enif_make_list_from_array(env, element, size);
    }
    else if (enif_get_list_length(env, argv[2], &len)) { // as list
	ERL_NIF_TERM elem[len];
	ERL_NIF_TERM element[len];	
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
	if ((size=mark_intersect_var(env, vp, var, elem, element, len)) < 0)
	    return enif_make_badarg(env);
	if (tuple)
	    return enif_make_tuple_from_array(env, element, size);
	else
	    return enif_make_list_from_array(env, element, size);	
    }
    else
	return enif_make_badarg(env);
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
    enif_fprintf(stdout, "LEAVE %s\r\n", (name));		\
    VALIDATE_MEMLIST();						\
    return result;						\
}

NIF_LIST
#undef NIF

#endif


static void load_atoms(ErlNifEnv* env)
{
    LOAD_ATOM(alpha);
    LOAD_ATOM(atom);
    LOAD_ATOM(bcp_counter);
    LOAD_ATOM(beta);    
    LOAD_ATOM(clause_2_counter);
    LOAD_ATOM(clause_3_counter);
    LOAD_ATOM(clause_d_counter);
    LOAD_ATOM(clause_n_counter);
    LOAD_ATOM(conflict_counter);    
    LOAD_ATOM(dead);
    LOAD_ATOM(default);
    LOAD_ATOM(degree);    
    LOAD_ATOM(delta);
    LOAD_ATOM(done);
    LOAD_ATOM(edge);
    LOAD_ATOM(edge_2_counter);
    LOAD_ATOM(edge_d_counter);    
    LOAD_ATOM(error);
    LOAD_ATOM(f);
    LOAD_ATOM(false);
    LOAD_ATOM(fifo);
    LOAD_ATOM(flags);
    LOAD_ATOM(gamma);
    LOAD_ATOM(hash);
    LOAD_ATOM(implication);
    LOAD_ATOM(implication_clause);
    LOAD_ATOM(implication_pos);
    LOAD_ATOM(inqueue);
    LOAD_ATOM(is_atom);
    LOAD_ATOM(jump);
    LOAD_ATOM(length);
    LOAD_ATOM(level);
    LOAD_ATOM(lifo);
    LOAD_ATOM(literal);
    LOAD_ATOM(literal_integer);
    LOAD_ATOM(literal_size);
    LOAD_ATOM(max_bound);
    LOAD_ATOM(max_conflicting);
    LOAD_ATOM(max_level);
    LOAD_ATOM(min_level);
    LOAD_ATOM(number_of_bound_variables);
    LOAD_ATOM(number_of_clauses);
    LOAD_ATOM(number_of_conflicting_clauses);
    LOAD_ATOM(number_of_dead_clauses);
    LOAD_ATOM(number_of_dead_edges);
    LOAD_ATOM(number_of_edges);
    LOAD_ATOM(number_of_learnt_clauses);
    LOAD_ATOM(number_of_subst_variables);
    LOAD_ATOM(number_of_unbound_variables);
    LOAD_ATOM(number_of_variables);
    LOAD_ATOM(off);
    LOAD_ATOM(ok);
    LOAD_ATOM(phase);
    LOAD_ATOM(qtype);
    LOAD_ATOM(queue);
    LOAD_ATOM(recursive);
    LOAD_ATOM(reset);
    LOAD_ATOM(set);
    LOAD_ATOM(size);
    LOAD_ATOM(status);
    LOAD_ATOM(symbol);
    LOAD_ATOM(system_limit);
    LOAD_ATOM(t);
    LOAD_ATOM(toggle);
    LOAD_ATOM(true);
    LOAD_ATOM(turbo);
    LOAD_ATOM(undefined);
    LOAD_ATOM(unit);
    LOAD_ATOM(use);
    LOAD_ATOM(use_phase);
    LOAD_ATOM(user);
    LOAD_ATOM(value_packing);
    LOAD_ATOM(variable);
    LOAD_ATOM(varp);
    LOAD_ATOM(watch);
    LOAD_ATOM(watch0);
    LOAD_ATOM(watch1);
    LOAD_ATOM(xref);
    LOAD_ATOM_STRING(exclamation_mark, "!");
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
	    *spp = (subscription_t*) sp->link.next;
	    obj_free(&vp->sub_allocator, sp);
	    return;
	}
	spp = (subscription_t**) &(sp)->link.next;
    }
}

static void varp_dtor(ErlNifEnv* env, void* obj)
{
    UNUSED(env);
    varp_t* vp = (varp_t*) obj;
#ifdef DEBUG_MEM
    enif_fprintf(stdout, "allocated memory before dtor = %ld\r\n",
		 mem_allocated);
#endif    
    cleanup(vp);
#ifdef DEBUG_MEM
    enif_fprintf(stdout, "allocated memory after dtor = %ld\r\n",
		 mem_allocated);
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

#ifdef DEBUG_MEM
    debug_mem_init();
#endif
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
