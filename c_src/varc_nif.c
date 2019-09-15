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

//
// configurations
// ASSERTIONS         various sanity test in runtime (during test)
// DEBUG              various output during debug
// DEBUG_MEM          special wrapped allocators to find leaks etc
// DEBUG_EVAL         print clauses during eval
// LIT_INTEGER        literals are represented as integers, size=8,16,32
// SIGNED_LITERALS    negative values are used to represent negated litterals
//                    else the lsb bit is used for that, and the variable
//                    index part is shifted one step to the left.
// PACKED_VALUE       pack two bit values in separate vector size=1,4 per byte
// TWO_CLAUSES        represent 2-clauses as implication links
// CLAUSE2_MAP        keep track on all 2clauses installed (implications)
// TWL_CIRCULAR       search for watch points in a circular fashion.
//

// #define LIT_INTEGER 32
// #define SIGNED_LITERALS
// #define PACKED_VALUE 4
// #define CLAUSE2_MAP          // require LIT_INTEGER & !SIGNED_LITERALS
// #define TWO_CLAUSES
// #define ASSERTIONS
// #define DEBUG
// #define DEBUG_MEM
// #define DEBUG_EVAL
// #define CLAUSE_EVAL_COUNT(vp, cnt)
#define CLAUSE_EVAL_COUNT(vp, cnt) vp->clause_eval_counter[(cnt)]++

// #define TWL_CIRCULAR

#ifdef TWL_CIRCULAR
#define TWL_WP0_DIR        1
#define TWL_WP0_INIT       wp0+TWL_WP0_DIR
#define TWL_WP0_NEXT(x)    (x)+TWL_WP0_DIR
#define TWL_WP0_WRAP(x,sz) (((x)>=(sz))?(0):(x))

#define TWL_WP1_DIR        -1
#define TWL_WP1_INIT       wp1+TWL_WP1_DIR
#define TWL_WP1_NEXT(x)    (x)+TWL_WP1_DIR
#define TWL_WP1_WRAP(x,sz) (((x)<0)?((sz)-1):(x))
#else

#define TWL_WP0_DIR     1
#define TWL_WP0_INIT    0
#define TWL_WP0_NEXT(x) (x)+TWL_WP0_DIR
#define TWL_WP0_WRAP(x,sz) (x)

#define TWL_WP1_DIR     1
#define TWL_WP1_INIT    0
#define TWL_WP1_NEXT(x) (x)+TWL_WP1_DIR
#define TWL_WP1_WRAP(x,sz) (x)

#endif

// #define USE_CLAUSE_SHUFFLE
// #define USE_CLAUSE_FIND

#define LOG_ASSIGN_ATOM
// #define NDEBUG
#include <assert.h>

typedef enum {
    false = 0,
    true = 1
} bool_t;

typedef enum {
    lifo = 0,
    fifo = 1,
    recursive = 2
} qtype_t;

// eval counter
#define ALL_CLAUSE    0
#define DEAD_CLAUSE   1
#define PAIR_CLAUSE   2
#define TRIPLE_CLAUSE 3

#ifdef SIGNED_LITERALS

// internal value 
typedef enum {
    I_UNDEF =  0,
    I_FALSE = -1,
    I_TRUE  =  1,
    I_BOUND =  2
} ival_t;

// IMPORT: convert from external value to interval value 

// EXPORT: convert from internal value to external value (true=1,false=-1..)
#define IMPORT(x) ((ival_t)(x))
#define EXPORT(x) ((int)(x))
#define INDEX(x)  (ABS(x))           // variable index
#define NEGATE(x) (-(x))
#define IS_NEGATED(x) ((x)<0)
#define UNPACK(x) ((int)((x)&0x3)-1) // map 0,1,2,3  => -1,0,1,2
#define PACK(x)   (((x)+1)&0x3)      // map -1,0,1,2 => 0,1,2,3
#define IS_CONSTANT(x) (ABS(x)==1)   // true=1, false=-1

#else
// use LSB bit to signal negation, this makes it easy
// to use cantor pair encoding since literals have as
// low numbers as possible

typedef enum {
    I_UNDEF = 0,
    I_BOUND = 1,
    I_TRUE  = 2,
    I_FALSE = 3
} ival_t;

// IMPORT: convert from external value to interval value 
// EXPORT: convert from internal value to external value (true=1,false=-1..)
#define IMPORT(x) (((x)<0) ? (((-(x))<<1)|1) : ((x)<<1))
#define EXPORT(y) (((y)&1) ? -((y)>>1) : ((y)>>1))
#define INDEX(x)  ((x)>>1)   // variable index
#define NEGATE(x) ((x)^1)
#define IS_NEGATED(x) ((x)&1)
#define UNPACK(x) ((x)&0x3)
#define PACK(x)   ((x)&0x3)
#define IS_CONSTANT(x) ((x)>1)   // true=2, false=3 
#endif

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

#define UNUSED(x) (void)(x)

static int varp_load(ErlNifEnv* env, void** priv_data, ERL_NIF_TERM load_info);
static int varp_upgrade(ErlNifEnv* env, void** priv_data, void** old_priv_data, 
			ERL_NIF_TERM load_info);
static void varp_unload(ErlNifEnv* env, void* priv_data);

static ERL_NIF_TERM varp_new(ErlNifEnv* env, int argc,
			     const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_add_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_del_variable(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_add_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_get_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_find_clause(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_compress_clause(ErlNifEnv* env, int argc,
					 const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_clause_info(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_variable_info(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_literal_info(ErlNifEnv* env, int argc,
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
static ERL_NIF_TERM varp_clean_clause(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_clean_literal(ErlNifEnv* env, int argc,
				       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_sort_none_permanent_clauses(
    ErlNifEnv* env,int argc,const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_info(ErlNifEnv* env, int argc,
			      const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_config(ErlNifEnv* env, int argc,
				const ERL_NIF_TERM argv[]);

static ERL_NIF_TERM varp_value(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_bind(ErlNifEnv* env, int argc,
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
static ERL_NIF_TERM varp_find_symbol(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_use_clause(ErlNifEnv* env, int argc,
				    const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_decay(ErlNifEnv* env, int argc,
			       const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_subscribe(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_clause_first(ErlNifEnv* env, int argc,
					  const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_clause_first_none_keep(ErlNifEnv* env, int argc,
						const ERL_NIF_TERM argv[]);
static ERL_NIF_TERM varp_clause_next(ErlNifEnv* env, int argc,
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
    int32_t sign;              // -1=negative,  1=positive
    uint32_t degree;           // degree count for this literal
    struct _variable_t* var;   // "parent"
    struct _wlink_t* wlist;    // list of watch positions
    struct _literal_t* qlink;  // unit propagation queue/stack
    struct _edge_t* elist;     // list of 2-clause triggers
    struct _xref_t* xfirst;    // cross ref clauses, falling cix!
    struct _xref_t** xlast;    // cross ref clauses, falling cix!
} literal_t;

#ifdef LIT_INTEGER

#if LIT_INTEGER == 8
typedef int8_t   lit_t;
typedef uint8_t  ulit_t;
typedef uint16_t ulitx2_t;
#ifdef SIGNED_LITERALS
#define VMAX 0x7f
#else
#define VMAX 0x3f
#endif
#elif LIT_INTEGER == 16
typedef int16_t  lit_t;
typedef uint16_t ulit_t;
typedef uint32_t ulitx2_t;
#ifdef SIGNED_LITERALS
#define VMAX 0x7fff
#else
#define VMAX 0x3fff
#endif
#elif LIT_INTEGER == 32
typedef int32_t   lit_t;
typedef uint32_t ulit_t;
typedef uint64_t ulitx2_t;
#define VMAX 0x07ffffff
#elif LIT_INTEGER == 64
typedef int64_t   lit_t;
typedef uint64_t ulit_t;
#define VMAX 0x07ffffffffffffff
#endif
#define LIT_NONE  0
#define V_TRUE VMAX
#define V_FALSE -VMAX

#else
typedef literal_t *lit_t;
#define LIT_NONE  ((lit_t)0)
#define VMAX 0x07ffffff
#define V_TRUE VMAX
#define V_FALSE -VMAX

#endif

typedef int32_t cix_t;             // clause index type
#define CLAUSE_ERROR ((cix_t) -1)

typedef struct _xref_t // :object_t
{
    struct _xref_t* next;
    cix_t cix;
    long p;
} xref_t;

typedef struct _edge_t // :object
{
    struct _edge_t* next;
    cix_t cix;               // if pair refer to real clause
    lit_t l;
} edge_t;

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
    ival_t    ivalue;
#endif
    int vix;                   // variable index
    float pkey[3];             // sort keys for positive literals
    float nkey[3];             // sort keys for negative literals
    float activity;            // activity 
    int map_index;             // order_map index
    cix_t implication_clause;  // implication clause index (0=none)
    int literal_pos;           // position in implication clause
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
#define CLAUSE_FLAG_TWO       0x0010   // convert into 2-clause

// sizeof wlink should be 8 on 32 bit machine or 16 on 64 bit machine
// 32 bit machine alignement should be 2*8 = 16 bytes
// 64 bit machine alignement should be 2*16 = 32 bytes
#define CLAUSE_ALIGNMENT (2*sizeof(wlink_t))


typedef struct _clause_t
{
    wlink_t    wl[2];        // ALIGNED watch point 1&2+links (DO NOT MOVE!)
    struct _clause_t* next;  // clause list
    struct _clause_t* uwatch;// clauses to unwatch
    uint64_t stamp;          // last used time (eval_counter clock)
    cix_t cix;               // clause id (index) 0..n-1  (<< 1)
    size_t size;             // number of literals in lit
    uint32_t hvalue;         // clause hash value
    uint8_t  flags;          // INQUEUE ...
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
    size_t bs_size;      // count of all elements in bs
    variable_t* bs;      // list of bound variables
} undo_t;

typedef struct arc4_stream_t {
    uint8_t i;
    uint8_t j;
    uint8_t s[256];
} arc4_stream_t;

typedef struct _subscription_t { // :object_t
    struct _subscription_t* next;
    ErlNifPid pid;               // the subscriber pid
    ErlNifMonitor mon;           // monitor the pid
    ERL_NIF_TERM what;           // what is subscribed to
} subscription_t;

typedef struct _varp_t {
    lit_t ltrue;
    lit_t lfalse;
    size_t vnext;       // next free variable number
    size_t vsize;       // allocated size of value map
    size_t vnum;        // number of variables
    size_t cnext;       // next clause number
    size_t csize;       // allocated size of clause map
    size_t cnum;        // number of clauses
    size_t cdead;       // number of dead clauses (level=0)
    size_t cpermanent;  // number of permanent clauses
    
    int num_conflicting;      // number of conflicting clauses saved
    int max_conflicting;      // max number of conflicting <= MAX_CONFLICTING
    int conflicting_clauses[MAX_CONFLICTING];
    size_t grow;              // how much to expand value map
    variable_t** var_map;     // variable map
#ifdef PACKED_VALUE
    uint8_t*     var_value;   // values are stored 8 bit/2 bit packed
#endif
    size_t ssize;             // size of symbol hash table
    size_t snum;              // number of symbols in symbol hash table
    symbol_t**   sym_map;     // symbol hash table
    size_t       chsize;      // size of clause hash table
    size_t       chnum;       // number of clauses in clause hash table (cnext)?
    hlink_t**    clause_hash; // clause hash table    
    int*         order_map;   // literal order table
    int          sort_key[2]; // sort order -1,-2,1,2
    clause_t**   clause_map;  // array of clauses, entries may be null
    size_t       keep;        // number of clauses to keep
    clause_t*    unwatch;     // clauses to unwatch (check after eval)
#ifdef CLAUSE2_MAP
    uint8_t*     clause2_map; // 2-clause map (member set)
#endif
    size_t       unum;        // number of levels allocated
    undo_t*      undo;        // array of undo block, one for each level
    size_t       stack_size;  // number of element in undo stack
    size_t       num_bound;   // number of bound variables
    int level;                // current undo level (mark)
    qtype_t qtype;            // literal queue is fifo/lifo/recursive
    bool_t activity;          // conflict activity in use
    lqueue_t     q;           // literal queue for propagation

    uint64_t  clause_eval_counter[4];
    uint64_t  eval_counter;        // performance counter

    variable_t undef;
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

#define L_TRUE(vp)     ((vp)->ltrue)
#define L_FALSE(vp)    ((vp)->lfalse)
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
    NIF_FUNC( "del_variable",        2,  varp_del_variable ),
    NIF_FUNC( "value",               2,  varp_value ),
    NIF_FUNC( "bind",                2,  varp_bind ),
    NIF_FUNC( "bind",                3,  varp_bind ),    
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
    NIF_FUNC( "get_clause",          4,  varp_get_clause ),
    NIF_FUNC( "find_clause",         2,  varp_find_clause ),
    NIF_FUNC( "compress_clause",     2,  varp_compress_clause ),
    NIF_FUNC( "clause_info",         3,  varp_clause_info ),
    NIF_FUNC( "variable_info",       3,  varp_variable_info ),
    NIF_FUNC( "literal_info",        3,  varp_literal_info ),
    NIF_FUNC( "del_clause",          2,  varp_del_clause ),
    NIF_FUNC( "clean_clause",        2,  varp_clean_clause ),
    NIF_FUNC( "clean_literal",       2,  varp_clean_literal ),
    NIF_FUNC( "sort_none_permanent_clauses",  1,
	      varp_sort_none_permanent_clauses ),
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
    NIF_FUNC( "find_symbol",         2,  varp_find_symbol ),
    NIF_FUNC( "use_clause",          2,  varp_use_clause ),
    NIF_FUNC( "decay",               2,  varp_decay ),
    NIF_FUNC( "subscribe",           2,  varp_subscribe ),
    NIF_FUNC( "clause_first",        1,  varp_clause_first ),
    NIF_FUNC( "clause_first_none_keep",   1,  varp_clause_first_none_keep ),
    NIF_FUNC( "clause_next",         2,  varp_clause_next ), 
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
DECL_ATOM(identity);
DECL_ATOM(random);
DECL_ATOM(degree);
DECL_ATOM(plus_degree);
DECL_ATOM(minus_degree);
DECL_ATOM(rank);
DECL_ATOM(plus_rank);
DECL_ATOM(minus_rank);
// DECL_ATOM(activity);
DECL_ATOM(plus_activity);
DECL_ATOM(minus_activity);

// info
DECL_ATOM(max_clause_length);
DECL_ATOM(max_conflicting);
DECL_ATOM(number_of_conflicting_clauses);
DECL_ATOM(number_of_clauses);
DECL_ATOM(number_of_dead_clauses);
DECL_ATOM(number_of_learned_clauses);
DECL_ATOM(number_of_variables);
DECL_ATOM(number_of_bound_variables);
DECL_ATOM(number_of_unbound_variables);
DECL_ATOM(clause_eval_counter);
DECL_ATOM(dead_eval_counter);
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
DECL_ATOM(activity);
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
DECL_ATOM(edge_list);
DECL_ATOM(exclamation_mark);
DECL_ATOM(literal_size);
DECL_ATOM(literal_integer);
DECL_ATOM(literal_signed);
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

#ifdef CLAUSE2_MAP
static ulitx2_t cantor_pair(ulit_t x, ulit_t y)
{
    ulitx2_t code = ((x+y+1)*(x+y) / 2) + y;
    return code;
}
#endif

// primitive negate a literal
static inline literal_t* neg_ll(literal_t* lp)
{
    return (lp->sign < 0) ? &lp->var->lit[LIT_POS] : &lp->var->lit[LIT_NEG];
}

static inline literal_t* vindex_ll(varp_t* vp, int vix)
{
    assert(vix != 0);    
    if (vix == V_TRUE) return LL_TRUE(vp);
    else if (vix == V_FALSE) return LL_FALSE(vp);
    return (vix < 0) ? &vp->var_map[-vix]->lit[LIT_NEG] :
	&vp->var_map[vix]->lit[LIT_POS];
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
    return (lp->sign < 0) ? -lp->var->vix : lp->var->vix;
}

static inline ERL_NIF_TERM external_ll(ErlNifEnv* env,literal_t* lp)
{
    int x = export_ll(lp);
    if (x == V_FALSE) return ATOM(f);
    if (x == V_TRUE) return ATOM(t);
    return enif_make_int(env, x);
}

static inline int is_neg_l(lit_t l)
{
#ifdef LIT_INTEGER
    return IS_NEGATED(l);
#else
    return (l->sign < 0);
#endif
}

static inline int is_constant(ival_t x)
{
    return IS_CONSTANT(x);
}

static inline int is_constant_l(varp_t* vp, lit_t l)
{
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
    int x = export_l(l);
    if (x == V_FALSE) return ATOM(f);
    if (x == V_TRUE) return ATOM(t);
    return enif_make_int(env, x);
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
    return vindex_ll(vp, EXPORT(l));
#else
    UNUSED(vp);
    return (literal_t*) l;
#endif
}

static inline lit_t ll2l(varp_t* vp, literal_t* lp)
{
    UNUSED(vp);
#ifdef LIT_INTEGER
    int value = export_ll(lp);
    return IMPORT(value);
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

// primitiv get variable value
static inline ival_t get_vv(varp_t* vp, variable_t* var)
{
#ifdef PACKED_VALUE
    ival_t ivalue;
    int i = var->vix;
    if (i == V_TRUE) return I_TRUE;
#if PACKED_VALUE == 1
    ivalue = UNPACK(vp->var_value[i]);
//    printf("get vix=%d, value[%d]=%02x, value=%d\r\n",
//	   var->vix, i, vp->var_value[i], ivalue);
    return ivalue;
#elif PACKED_VALUE == 4
    int j = (i & 0x3) << 1;  // shift 0,2,4,6    
    i >>= 2;
    ivalue = UNPACK(vp->var_value[i] >> j);
//    printf("get vix=%d, value[%d:%d]=%02x, value=%d\r\n",
//	   var->vix, i, j, vp->var_value[i], ivalue);    
    return ivalue;
#endif
    
#else
    UNUSED(vp);
    return var->ivalue;
#endif
}

static inline void set_vv(varp_t* vp, variable_t* var, ival_t ivalue)
{
#ifdef PACKED_VALUE
    int i = var->vix;
    assert(i != V_TRUE);    
#if PACKED_VALUE == 1
    vp->var_value[i] = PACK(ivalue);
//    printf("set vix=%d, vallue=%d, packed[%d]=%02x\r\n",
//	   var->vix, ivalue, i, vp->var_value[i]);
#elif PACKED_VALUE == 4
    int j = (i&0x3) << 1;  // shift 0,2,4,6    
    i >>= 2;
    vp->var_value[i] = (vp->var_value[i] & ~(0x3<<j)) | (PACK(ivalue) << j);
//    printf("set vix=%d, ivalue=%d, packed[%d]=%02x\r\n",
//	   var->vix, ivalue, i, vp->var_value[i]);    
#endif

#else
    UNUSED(vp);
    var->ivalue = ivalue;
#endif
}

// return literal match variables value (only when bound)
static inline literal_t* var_literal(varp_t* vp, variable_t* var)
{
    ival_t v = get_vv(vp,var);
    if (v == I_TRUE) return &var->lit[LIT_POS];
    else if (v == I_FALSE) return &var->lit[LIT_NEG];
    else {
	assert(0);
	return NULL;
    }
}

// primitiv get literal value
static inline ival_t get_ll(varp_t* vp, literal_t* lp)
{
    ival_t v = get_vv(vp,lp->var);
    if (is_constant(v))
	return (lp->sign < 0) ? NEGATE(v) : v;
    return v;
}

// primitive get lit value
static inline ival_t get_l(varp_t* vp, lit_t l)
{
    return get_ll(vp, l2ll(vp, l));
}

// primitive set literal value
static inline void set_ll(varp_t* vp, literal_t* lp, ival_t ivalue)
{
    if (lp->sign < 0)
	set_vv(vp,lp->var,NEGATE(ivalue));
    else
	set_vv(vp,lp->var,ivalue);
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

static inline ival_t get_literal_value(varp_t* vp, literal_t* lp)
{
    lp = lookup_literal(lp);
    return get_ll(vp, lp);
}

static inline void set_literal_value(varp_t* vp,literal_t* lp,ival_t ivalue)
{
    while (lp->var->bound) { // resolve literal
	if (lp->sign < 0) ivalue = NEGATE(ivalue);
	lp = lp->var->bound;
    }
    set_ll(vp, lp, ivalue);
}

static inline ival_t lit_value(varp_t* vp,lit_t l)
{
    literal_t* lp = l2ll(vp, l);
    return get_literal_value(vp, lp);
}

static inline ival_t get_variable_value(varp_t* vp,variable_t* var)
{
    if (var->bound)
	return get_literal_value(vp, var->bound);
    else
	return get_vv(vp, var);
}

static inline void set_variable_value(varp_t* vp,variable_t* var,ival_t ivalue)
{
    if (var->bound)
	set_literal_value(vp, var->bound, ivalue);
    else
	set_vv(vp, var, ivalue);
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
    case I_BOUND: assert(0); return 0;
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

static int32_t literal_array_hash(lit_t* lit, size_t size)
{
    int32_t p = 1;
    int32_t s = 0;
    int32_t x = 0;
    int32_t len = 0;

    while(size--) {
	int32_t li  = export_l(*lit++);
	assert(li != V_TRUE);  // TRUE should never occure!
	// skip constant FALSE, introduce during substition sometimes
	if (li == V_FALSE)
	    continue;
	p *= li;
	s += li;
	x ^= li;
	len++;
    }
    return len + (s<<10) - s + (p^((x<<5)-x));
}

static inline uint32_t clause_hash(clause_t* cp)
{
    return (uint32_t) literal_array_hash(cp->lit, cp->size);
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
	snprintf(litname, sizeof(ln1), "%s$%d", n, lp->var->vix);
    return litname;
}

char* format_lit(varp_t* vp, lit_t l)
{
    return format_literal(vp, l2ll(vp, l));
}

#ifdef DEBUG
#define PRINT_LIT_ARRAY(msg,lit,size) print_lit_array((msg),(lit),(size))
#define PRINT_CLAUSE(vp,msg,cp) print_clause((vp),(msg),(cp))
#else
#define PRINT_LIT_ARRAY(msg,lit,size)
#define PRINT_CLAUSE(vp,msg,cp)
#endif

void print_lit_array(char* label, lit_t* lit, size_t size)
{
    if (size == 0)
	enif_fprintf(stdout, "%s=[]", label);
    else {
	unsigned k;
	enif_fprintf(stdout, "%s=[%d", label, export_l(lit[0]));
	for (k=1; k<size; k++)
	    enif_fprintf(stdout, ",%d", export_l(lit[k]));
	enif_fprintf(stdout, "]\r\n");
    }
}

void print_clause(varp_t* vp, char* label, clause_t* cp)
{
    unsigned k;
    enif_fprintf(stdout, "%s id=%d,[%ld:%ld] [%d/%d",
	   label, cp->cix, cp->wl[0].p, cp->wl[1].p,
	   export_l(cp->lit[0]),lit_value(vp,cp->lit[0]));
    for (k=1; k<cp->size; k++)
	enif_fprintf(stdout, ",%d/%d", export_l(cp->lit[k]),
		     lit_value(vp,cp->lit[k]));
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
    enif_fprintf(stdout, "]\r\n");
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

static void unwatch_ll(varp_t* vp, clause_t* cp, literal_t* lp)
{
    UNUSED(vp);
    wlink_t** wlp = &lp->wlist;
    wlink_t* wl;

    DBG("UNWATCH cix=%lu lit=%d wl=%p\r\n", cp->cix, export_ll(lp), *wlp);

    while((wl = *wlp) && (clause_pointer(wl) != cp))
	wlp = &(wl->next);
    if (wl != NULL) {
	*wlp = wl->next;  // unlink
	wl->p = -1;       // mark as not used
    }
}

static inline void unwatch(varp_t* vp, clause_t* cp, lit_t l)
{
    unwatch_ll(vp, cp, l2ll(vp, l));
}

// remove the 2-WL watch points
static void unwatch_clause(varp_t* vp, clause_t* cp)
{
    long p;
    if ((p = cp->wl[0].p) >= 0) unwatch(vp, cp, cp->lit[p]);
    if ((p = cp->wl[1].p) >= 0) unwatch(vp, cp, cp->lit[p]);
}

static void schedule_unwatch_clause(varp_t* vp, clause_t* cp)
{
    if (!(cp->flags & CLAUSE_FLAG_UNWATCH)) {
	cp->uwatch = vp->unwatch;
	vp->unwatch = cp;
	cp->flags |= CLAUSE_FLAG_UNWATCH;
	// print_sym_clause(vp, "SCHEDULE", cp);
    }
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

static inline void lqueue_put_ll(varp_t* vp, literal_t* lp)
{
    lqueue_t* q = &vp->q;

    DBG("ENQ %s qsize=%ld\r\n", format_literal(vp,lp), q->size);

    if (vp->qtype == lifo) {  // put element first
	lp->qlink = q->head;
	q->head = lp;
	if (lp->qlink == NULL)
	    q->tail = &(lp->qlink);
    }
    else {  // recursive | fifo
	lp->qlink = NULL;
	*q->tail = lp;
	q->tail = &(lp->qlink);
    }
    q->size++;
}

static inline void lqueue_put(varp_t* vp, lit_t l)
{
    lqueue_put_ll(vp, l2ll(vp,l));
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
    q->size--;
    DBG("DEQ %s(%d,%d) qsize=%ld\r\n", format_literal(vp,lp),
	lp->var->vix, lp->var->literal_pos,  q->size);
    return lp;
}

static inline void push_variable(varp_t* vp, variable_t* var, int level)
{
    assert(get_vv(vp, var) == I_UNDEF);
    DBG("PUSH VARIABLE: var=%s, level=%d\r\n", format_variable(var), level);
    var->next = vp->undo[level].bs;
    vp->undo[level].bs = var;
    vp->undo[level].bs_size++;
    vp->stack_size++;
    vp->num_bound++;
}

static ERL_NIF_TERM make_cix(ErlNifEnv* env,cix_t cix)
{
    return enif_make_int(env, (int)cix);
}

static ERL_NIF_TERM make_binding(ErlNifEnv* env, varp_t*vp, variable_t* var)
{
    assert(var->bound == NULL);
    return enif_make_int(env,export_vv(vp, var));
}

static ERL_NIF_TERM make_clause_info(ErlNifEnv* env,varp_t* vp,variable_t* var)
{
    assert(var->bound == NULL);

    return enif_make_tuple3(env,
			    enif_make_int(env,export_vv(vp, var)),
			    enif_make_int(env, var->literal_pos),
			    make_cix(env, var->implication_clause));
}

//
// send message to process(es) interested in permanent assignments
// of variables.
//
static void log_permanent(varp_t* vp, literal_t* x, literal_t* y, int level)
{
#ifdef LOG_ASSIGN_ATOM
    if ((level == 0) && (x->var->flags & VAR_FLAG_ATOM)) {
	subscription_t* sp;
	if (y == NULL) {
	    DBG("PERMANENT(ATOM) %s=%d\r\n", format_literal(vp,x),
		(EXPORT(get_ll(vp,x))+1)>>1);
	}
	else if (y->var->flags & VAR_FLAG_ATOM) {
	    DBG("PERMANENT(ATOM) %s=%s\r\n", format_literal(vp,y),
		format_literal(vp,x));
	}
	sp = vp->subs;
	while(sp != NULL) {
	    if (sp->what == ATOM(atom)) {
		ERL_NIF_TERM xt;
		ERL_NIF_TERM yt;
		ERL_NIF_TERM bnd = ATOM(false);
		ERL_NIF_TERM msg;

		if (y == NULL) {
		    xt = external_ll(vp->msg_env,x);
		    bnd = xt;
		}
		else { // if (y->var->flags & VAR_FLAG_ATOM) {
		    yt = external_ll(vp->msg_env,y);
		    xt = external_ll(vp->msg_env,x);
		    bnd = enif_make_tuple2(vp->msg_env, xt, yt);
		}
		if (bnd != ATOM(false)) {
		    msg = enif_make_tuple2(vp->msg_env, ATOM(varp), bnd);
		    if (vp->caller_env != NULL) {
			enif_send(vp->caller_env, &sp->pid, vp->msg_env, msg);
			enif_clear_env(vp->msg_env);
		    }
		    else {
			DBG("caller_env NOT set!!!\r\n");
		    }
		}
	    }
	    sp = sp->next;
	}
    }
#else
    UNUSED(vp);
    UNUSED(x);
    UNUSED(y);    
    UNUSED(level);
#endif
}

static inline void set_literal(varp_t* vp,lit_t l,ival_t ivalue,
			       long li, cix_t cix, int level)
{
    literal_t* lp = l2ll(vp, l);
    variable_t* var = lp->var;
    DBG("SET_LITERAL %s = %d\r\n", format_lit(vp,l), ivalue);
    assert(!is_constant(get_variable_value(vp, var)));
    assert(var->bound == NULL);
    set_vv(vp, var, is_neg_l(l) ? NEGATE(ivalue) : ivalue);
    var->implication_clause = cix;
    var->literal_pos = li;
    var->level = level;
    log_permanent(vp, lp, NULL, level);
}

#if 0
static void put_literal_old(varp_t* vp,lit_t l,ival_t ivalue,
			    long li, cix_t cix,int level)
{
    variable_t* var = var_l(vp, l);
    assert(level >= 0);  // if (level < 0) level = vp->level;
    push_variable(vp, var, level);
    if (is_constant(ivalue))
	lqueue_put(vp, (ivalue==I_TRUE) ? neg_l(l) : l);
    set_literal(vp, l, ivalue, li, cix, level);
}
#endif

static void kill_x_clauses(varp_t* vp, literal_t* xp)
{
    xref_t* xptr = xp->xfirst;

    // enif_fprintf(stdout, "KILL %s=TRUE : \r\n", format_literal(vp, xp));
    
    while(xptr) {
	clause_t* cp = vp->clause_map[xptr->cix];
	if (cp && !(cp->flags & CLAUSE_FLAG_DEAD)) {
	    int maybe_watched = 1;
#ifdef TWO_CLAUSES
	    if (cp->size == 2) // not watched
		maybe_watched = 0;
#endif
	    if (maybe_watched) {
		schedule_unwatch_clause(vp, cp);
		// print_sym_clause(vp, "  DEAD", cp);
	    }
	    vp->cdead++;
	    cp->flags |= CLAUSE_FLAG_DEAD;
	}
	xptr = xptr->next;
    }
}

#ifdef TWO_CLAUSES

// insert implication edge a -> b, this will trigger
// when a=1 and yield b=1
static void edge_insert(varp_t* vp, lit_t a, lit_t b, cix_t cix)
{
    edge_t* pp;
    literal_t* ap = l2ll(vp, a);
    
    pp = varp_alloc(&vp->edge_allocator);
    pp->l = b;
    pp->cix = cix;
    pp->next = ap->elist;
    ap->elist = pp;
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
	    return;
	}
	ppp = &(pp->next);
    }
}

static void check_2_clauses(varp_t* vp, literal_t* xp)
{
    xref_t* xptr = xp->xfirst;
    
    // enif_fprintf(stdout, "CHECK %s=FALSE : \r\n", format_literal(vp, xp));
    
    while(xptr) {
	clause_t* cp  = vp->clause_map[xptr->cix];
	if (cp && !(cp->flags & CLAUSE_FLAG_DEAD)) {
	    if (cp->size == 3) { // fixme: general case 3-WL later
		if ((cp->wl[0].p >= 0) && (cp->wl[1].p >= 0)) {
		    cp->flags |= CLAUSE_FLAG_TWO;
		    schedule_unwatch_clause(vp, cp);
		    // print_sym_clause(vp, "  3->2", cp);
		}
	    }
	}
	xptr = xptr->next;
    }
}

#endif

static void put_nq_ll(varp_t* vp, literal_t* lp, ival_t ivalue,
		      long li,cix_t cix,int level)
{
    variable_t* var = lp->var;

    DBG("PUT_LITERAL %s = %d\r\n", format_literal(vp,lp), ivalue);
    
    assert(level >= 0);  // if (level < 0) level = vp->level;
    assert(!is_constant(get_variable_value(vp, var)));
    assert(var->bound == NULL);
    
    push_variable(vp, var, level);
    
    set_vv(vp, var, (lp->sign < 0) ? NEGATE(ivalue) : ivalue);
    var->implication_clause = cix;
    var->literal_pos = li;
    var->level = level;
    log_permanent(vp, lp, NULL, level);
}

static void put_ll(varp_t* vp, literal_t* lp, ival_t ivalue,
		   long li,cix_t cix,int level)
{
    put_nq_ll(vp, lp, ivalue, li, cix, level);
    if (is_constant(ivalue))
	lqueue_put_ll(vp, (ivalue==I_TRUE) ? neg_ll(lp) : lp);
}

static inline void put_l(varp_t* vp,lit_t l,ival_t ivalue,
			 long li,cix_t cix,int level)
{
    put_ll(vp,l2ll(vp, l),ivalue,li,cix,level);
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
	set_vv(vp, bp, I_UNDEF);
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

// update activity on one level
static void activate_level(varp_t* vp, int level, float delta)
{
    variable_t* bp = vp->undo[level].bs;

    while(bp != NULL) {
	bp->activity += delta;
	bp = bp->next;
    }
}

// update activity on all levels
static void activate_levels(varp_t* vp, float delta)
{
    int i;
    for (i = 0; i <= vp->level; i++)
	activate_level(vp, i, delta);
}

static void activity_decay(varp_t* vp, float decay)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++)
	vp->var_map[i]->activity /= decay;
}

static void init_literal(literal_t* lp, variable_t* var, int sign)
{
    lp->sign = sign;
    lp->degree = 0;
    lp->var  = var;
    lp->wlist = NULL;
    lp->qlink = NULL;
    lp->elist = NULL;
    lp->xfirst = NULL;
    lp->xlast  = &lp->xfirst;
}

static void init_variable(varp_t* vp, variable_t* var, ival_t value, int vix)
{
    var->vix       = vix;
    var->next      = NULL;    
    var->flags     = 0;
    var->bound     = NULL;
    var->pkey[0]   = var->pkey[1] = var->pkey[2] = 0.0f;
    var->nkey[0]   = var->nkey[1] = var->nkey[2] = 0.0f;    
    var->activity  = 1.0f;
    var->map_index = vix;
    var->implication_clause = CLAUSE_ERROR;
    var->literal_pos = -1;
    var->level = -1;
    var->strname = NULL;
    var->names = NULL;

    if (vix == V_TRUE) {
#ifndef PACKED_VALUE
	var->ivalue = value;
#endif
    }
    else {
	set_vv(vp, var, value);
    }
    init_literal(&var->lit[LIT_POS], var, 1);
    init_literal(&var->lit[LIT_NEG], var, -1);
}


// FIXME clauses should really be heap allocated?
// except we need to garbage collect in that case when
// deleting clauses...or

static clause_t* clause_alloc(varp_t* vp, int size)
{
    UNUSED(vp);
    clause_t* cp;
    int r;
    
    if (size < 1)
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
	if (cp->cix >= 0) {
	    clause_hash_unlink(vp, cp);
	    vp->clause_map[cp->cix] = NULL;
	    vp->cnum--;
	}
	free(cp);
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
// return CLAUSE_ERROR otherwise
cix_t clause_find(varp_t* vp, lit_t* lit, size_t size)
{
    uint32_t hvalue = (uint32_t) literal_array_hash(lit, size);
    
    if (vp->clause_hash) {
	hlink_t* hp = vp->clause_hash[hvalue & (vp->chsize-1)];

	// enif_fprintf(stdout, "find hvalue=%u ", hvalue);
	// print_lit_array("", lit, size);
	
	while(hp) {
	    if (hp->hvalue == hvalue) {
		clause_t* cp = vp->clause_map[hp->cix];
		assert(cp != NULL);
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
	int i;
	
	DBG("warning slow clause_find in use\r\n");
	// enif_fprintf(stdout, "find hvalue=%u ", hvalue);
	// print_lit_array("", lit, size);
	
	for (i = 0; i < (int)vp->cnext; i++) {
	    clause_t* cp = vp->clause_map[i];
	    if ((cp != NULL) && (cp->size == size) && (cp->hvalue == hvalue) &&
		clause_is_equal(lit, cp->lit, size)) {
		// enif_fprintf(stdout, "found %d\r\n", cp->cix);
		return cp->cix;
	    }
	}
	// enif_fprintf(stdout, "not found\r\n");
    }
    return CLAUSE_ERROR;
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

static cix_t clause_insert(varp_t* vp, clause_t* cp, uint32_t hvalue)
{
    int i = vp->cnext++;

    cp->cix = (cix_t) i;
    cp->stamp = vp->eval_counter;
    cp->hvalue = hvalue;
    
    if (vp->cnext == vp->csize) {
	unsigned int new_csize = vp->csize + vp->grow;
	clause_t** cpp;
	
	if (!(cpp = VARP_REALLOC(vp->clause_map, new_csize*sizeof(clause_t**))))
	    return CLAUSE_ERROR;
	vp->clause_map = cpp;
	vp->csize = new_csize;
    }
    vp->cnum++;
    vp->clause_map[i] = cp;

    clause_hash_link(vp, cp);

    return cp->cix;
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
	if (x == 0) return 0;
	else if (ABS(x) < (int)vp->vnext) *lpp = vindex_ll(vp, x);
	else {
	    DBG("literal %d out of range\r\n", x);
	    return 0;
	}
    }
    else if (arg == ATOM(t)) *lpp = LL_TRUE(vp);
    else if (arg == ATOM(f)) *lpp = LL_FALSE(vp);
    else return 0;
    return 1;
}

// get primitive lit value
static int vif_get_l(ErlNifEnv* env, varp_t* vp, ERL_NIF_TERM arg, lit_t* l)
{
    int x;
    if (enif_get_int(env, arg, &x)) {
	if (x == 0) return 0;
	else if (ABS(x) < (int)vp->vnext) *l = vindex_l(vp, x);
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

static int vif_get_cix(ErlNifEnv* env,varp_t* vp,ERL_NIF_TERM term,cix_t* cix)
{
    int ix;
    if (!enif_get_int(env, term, &ix))
	return 0;
    if ((ix < 0) || (ix >= (int)vp->cnext))
	return 0;
    *cix = ix;
    return 1;
}

static ERL_NIF_TERM make_literal(ErlNifEnv* env, literal_t* lp)
{
    return enif_make_int(env, export_ll(lp));
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

    if (vp->clause_hash) {
	VARP_FREE(vp->clause_hash);
	vp->clause_hash = NULL;		    
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

#ifdef CLAUSE2_MAP
    if (vp->clause2_map) {
	VARP_FREE(vp->clause2_map);
	vp->clause2_map = NULL;
    }
#endif
    
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
    bool_t activity = false;
    bool_t clause_hash = false;

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
	else if (elem[0] == ATOM(activity) && (elem[1] == ATOM(true))) {
	    activity = true;
	}
	else if (elem[0] == ATOM(activity) && (elem[1] == ATOM(false))) {
	    activity = false;
	}
	else if (elem[0] == ATOM(clause_hash) && (elem[1] == ATOM(true))) {
	    clause_hash = true;
	}
	else if (elem[0] == ATOM(clause_hash) && (elem[1] == ATOM(false))) {
	    clause_hash = false;
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
    vp->activity = activity;
    vp->vnext = 1;
    vp->vsize = vsize;
    vp->vnum  = 0;

    vp->grow = grow;
    if (!(vp->var_map = VARP_ALLOC(vsize*sizeof(variable_t**))))
	goto error;
#ifdef PACKED_VALUE
    if (!(vp->var_value = VARP_ALLOC(PACKED_BYTES(vsize)*sizeof(uint8_t))))
	goto error;
#endif

#ifdef CLAUSE2_MAP
    {
	size_t size = cantor_pair(2*vsize,2*vsize)*sizeof(uint8_t);
	if (!(vp->clause2_map = VARP_ALLOC(size)))
	    goto error;
	printf("clause2_map: alloc size=%d, alloc=%ld\r\n",
	       2*vsize, size);
	memset(vp->clause2_map, 0, size);
    }
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
    vp->cnext = 0;
    vp->csize = csize;
    vp->cnum = 0;
    vp->cdead = 0;
    vp->cpermanent = 0;
    vp->keep = 0;
    vp->unwatch = NULL;
    
    if (!(vp->clause_map = VARP_ALLOC(csize*sizeof(clause_t**))))
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

    vp->max_conflicting = MAX_CONFLICTING;
    vp->eval_counter = 0;
    vp->clause_eval_counter[ALL_CLAUSE] = 0;     // overall counter
    vp->clause_eval_counter[DEAD_CLAUSE] = 0;    // dead clause counter
    vp->clause_eval_counter[PAIR_CLAUSE] = 0;    // 2-clause
    vp->clause_eval_counter[TRIPLE_CLAUSE] = 0;  // 3-clauses

    vp->order_map[0] = 0;
    init_variable(vp, &vp->undef, I_UNDEF, 0);
    vp->var_map[0] = &vp->undef;
    init_variable(vp, &vp->constant, I_TRUE, V_TRUE);
#ifdef LIT_INTEGER
    vp->ltrue  = IMPORT(V_TRUE);
    vp->lfalse = IMPORT(V_FALSE);
#else
    vp->ltrue = &vp->constant.lit[LIT_POS];
    vp->lfalse = &vp->constant.lit[LIT_NEG];
#endif
    
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

#ifdef LIT_INTEGER
    if (vp->vnext >= VMAX)
	enif_raise_exception(env, ATOM(system_limit));
#endif
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
	if (!(ptr = VARP_REALLOC(vp->var_value,
				 PACKED_BYTES(new_vsize)*sizeof(uint8_t))))
	    return enif_make_badarg(env);
	vp->var_value = ptr;
#endif

#ifdef CLAUSE2_MAP
	{
	    size_t old_vsize = vp->vsize;
	    ulit_t size0 = cantor_pair(2*old_vsize,2*old_vsize)*sizeof(uint8_t);
	    size_t size1 = cantor_pair(2*new_vsize,2*new_vsize)*sizeof(uint8_t);
	    if (!(ptr = VARP_REALLOC(vp->clause2_map, size1)))
		return enif_make_badarg(env);
	    printf("clause2_map: realloc size=%d, alloc=%ld, grow=%ld\r\n",
		   2*new_vsize, size1, (size1-size0));
	    memset(ptr+size0, 0, (size1-size0));
	    vp->clause2_map = ptr;
	}
#endif
	vp->vsize = new_vsize;
    }
    vp->vnum++;
    vp->order_map[vix] = vix;
    init_variable(vp, var, I_UNDEF, vix);
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

    // check that variable is not refered to any where
    if ((var->lit[0].degree != 0) || (var->lit[1].degree != 0))
	return enif_make_badarg(env);
    assert(var->lit[0].xfirst == NULL);
    assert(var->lit[1].xfirst == NULL);
    
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
    if (argv[2] == ATOM(edge_list)) {
	ERL_NIF_TERM list = enif_make_list(env, 0);
	edge_t* ep = lp->elist;
	
	while(ep) {
	    ERL_NIF_TERM elem;
	    elem = enif_make_tuple2(env,
				    enif_make_int(env, ep->cix),
				    enif_make_int(env, export_l(ep->l)));
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
		if (lp->sign < 0)
		    term = enif_make_tuple2(env, ATOM(exclamation_mark), term);
	    }
	    else {
		size_t size = sp->size + (lp->sign < 0);
		uint8_t* data = enif_make_new_binary(env, size, &term);
		if (lp->sign < 0)
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


static ERL_NIF_TERM varp_order_first(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;

    if (!enif_get_resource(env, argv[0], varp_res, (void**)&vp))
	return enif_make_badarg(env);

    for (i = 1; i < (int)vp->vnext; i++) {
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
	    if (!skip) {
		return enif_make_tuple2(env,enif_make_int(env, i),
					enif_make_int(env, vix));
	    }
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
    b = 1;
    u = vp->vnext;

    for (i = 1; i < (int)vp->vnext; i++) {
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
    for (i = 1; i < (int)vp->vnext; i++) {
	vp->var_map[i]->pkey[k] = (float) i;
	vp->var_map[i]->nkey[k] = (float) i;	
    }
}

static void order_k_random(varp_t* vp, int k)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++) {
	int v1 = arc4_random_uniform(&vp->as, 0x7fffff);
	int v2 = arc4_random_uniform(&vp->as, 0x7fffff);
	vp->var_map[i]->pkey[k] = v1 / (float)0x7fffff;
	vp->var_map[i]->nkey[k] = v2 / (float)0x7fffff;
    }
}

static void order_k_undefined(varp_t* vp, int k)
{
    int i;
    for (i = 1; i < (int)vp->vnext; i++) {
	vp->var_map[i]->pkey[k] = 0.0f;
	vp->var_map[i]->nkey[k] = 0.0f;
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
    int i;
    
    for (i = 1; i < (int)vp->vnext; i++) {
	vp->var_map[i]->pkey[k] = 0.0f;
	vp->var_map[i]->nkey[k] = 0.0f;
    }

    for (i = 0; i < (int)vp->cnext; i++) {
	clause_t* cp = vp->clause_map[i];
	int j;
	if (cp != NULL) {
	    int n = cp->size;
	    if (n > 0) {
		float r = 1/(float)n;
		for (j = 0; j < n; j++) {
		    int x = export_l(cp->lit[j]);
		    if (x < 1)
			vp->var_map[-x]->nkey[k] += r;
		    else if (x > 1)
			vp->var_map[x]->pkey[k] += r;
		}
	    }
	}
    }
}


// scan through all variables and calculate the "rank"
// foreach literal calculate Rj = Sum(1/Ni) where ni is the
// size of the clause that the literal Lj is a member
static void order_k_activity(varp_t* vp, int k)
{
    int i;
    
    for (i = 1; i < (int)vp->vnext; i++) {
	variable_t* var = vp->var_map[i];
	var->pkey[k] = var->activity;
	var->nkey[k] = var->activity;
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
    float a = (ap->pkey[k] >= ap->nkey[k]) ? ap->pkey[k] : ap->nkey[k];
    float b = (bp->pkey[k] >= bp->nkey[k]) ? bp->pkey[k] : bp->nkey[k];
    if (a < b) return -1;
    else if (a > b) return 1;
    return 0;
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
	else if ((argv[i] == ATOM(degree)) || (argv[i] == ATOM(plus_degree))) {
	    order_k_degree(vp, k);
	}
	else if (argv[i] == ATOM(minus_degree)) {
	    order_k_degree(vp, k);
	    k = -k;
	}
	else if ((argv[i] == ATOM(rank)) || (argv[i] == ATOM(plus_rank))) {
	    order_k_rank(vp, k);
	}
	else if (argv[i] == ATOM(minus_rank)) {
	    order_k_rank(vp, k);
	    k = -k;
	}
	else if ((argv[i] == ATOM(activity)) ||
		 (argv[i] == ATOM(plus_activity))) {
	    order_k_activity(vp, k);
	}
	else if (argv[i] == ATOM(minus_activity)) {
	    order_k_activity(vp, k);
	    k = -k;
	}	
	else
	    return enif_make_badarg(env);
	vp->sort_key[i-1] = k;
    }
    // install identity order
    u = order_reset(vp);

//    for (i = u; i < (int)vp->vnext; i++)
//	printf("order_map[%d] = %d\r\n", i, vp->order_map[i]);
    
    // sort unbound variables according to sort_keys
    QSORT_R(vp->order_map+u, vp->vnext-u, sizeof(int), cmp_keys, vp);

//    for (i = u; i < (int)vp->vnext; i++)
//	printf("order_map[%d] = %d\r\n", i, vp->order_map[i]);

    k1 = ABS(vp->sort_key[0]);
    k2 = ABS(vp->sort_key[1]);
    // update map_index of sorted variables also update the sign
    for (i = u; i < (int)vp->vnext; i++) {
	int v = vp->order_map[i];
	variable_t* var = vp->var_map[v];
	float r;

	var->map_index = i;
	if ((r = (var->pkey[k1] - var->nkey[k1])) == 0.0)
	    r = (var->pkey[k2] - var->nkey[k2]);
	if (r < 0.0)
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
    literal_t* lp;
    varp_t* vp;

    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!vif_get_literal(env, vp, argv[1], &lp))
	return enif_make_badarg(env);
    switch(get_ll(vp, lp)) {
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
			    make_cix(env, var->implication_clause),
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
    case I_BOUND: {
	literal_t* lp = l2ll(vp,xp);
	printf("lp->sign=%d\r\n", lp->sign);
	printf("lp->var->bound=%p\r\n", lp->var->bound);
	printf("was bound\r\n");
	return enif_make_badarg(env);
    }
    case I_UNDEF:
    default:
	vp->caller_env = env;
	put_l(vp, xp, I_TRUE, -1, -1, level);
	vp->caller_env = NULL;	
	return ATOM(true);
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
	switch(lit_value(vp,l)) {  // FIXME: get_l? instead
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

    for (p = 0; p < (long)cp->size; p++) {
	lit_t l = cp->lit[p];
	switch(lit_value(vp,l)) {
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


static void add_xref(varp_t* vp, clause_t* cp, long p)
{
    literal_t* lp   = l2ll(vp, cp->lit[p]);
    xref_t*    xp   = varp_alloc(&vp->xref_allocator);

    lp->degree++;
    
    xp->cix  = cp->cix;
    xp->p    = p;
    xp->next = NULL;

    *lp->xlast = xp;
    lp->xlast = &(xp->next);
}

static void del_xref_ll(varp_t* vp, clause_t* cp, long p, literal_t* lp)
{
    xref_t* xp;
    xref_t** xpp = &lp->xfirst;
    // locate and remove xref link

    while((xp = *xpp)) {
	if ((xp->cix == cp->cix) && (xp->p == p)) {
	    if (lp->xlast == &xp->next)
		lp->xlast = xpp;
	    *xpp = xp->next;
	    varp_free(&vp->xref_allocator, xp);
	    lp->degree--;
	    return;
	}
	xpp = &(xp->next);
    }
    DBG("xref not found for clause %lu pos = %ld\r\n", cp->cix, p);
}

static inline void del_xref(varp_t* vp, clause_t* cp, long p)
{
    del_xref_ll(vp, cp, p, l2ll(vp, cp->lit[p]));
}

static int link_clause(varp_t* vp, clause_t* cp)
{
    size_t size = cp->size;
    long p;
    
    // re-add cross reference
    for (p = 0; p < (int)size; p++)
	add_xref(vp, cp, p);
    
#ifdef TWO_CLAUSES
    if (size == 2) {
	lit_t* lit  = cp->lit;
	edge_insert(vp, neg_l(lit[0]), lit[1], cp->cix);
	edge_insert(vp, neg_l(lit[1]), lit[0], cp->cix);
	cp->wl[0].p = -1;
	cp->wl[1].p = -1;
	DBG("  2-clause\r\n");
	return 1;
    }
#endif    
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
#ifdef TWO_CLAUSES
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
#endif

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

// substitute one literal
static void subst_ll(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp   = l2ll(vp, yl);
    literal_t* xp   = l2ll(vp, xl);
    literal_t* nxp  = neg_ll(xp);
    xref_t**   xpp  = &xp->xfirst;
    xref_t**  nxpp  = &nxp->xfirst;
    xref_t*    yptr = yp->xfirst;
    
    assert (yp != xp);

    // reset y xref
    yp->xfirst = NULL;
    yp->xlast  = &yp->xfirst;

    // scan and rewrite all y's into x's
    while(yptr) {
	xref_t* xptr = *xpp;
	xref_t* nxptr = *nxpp;

	if (((xptr == NULL) || (yptr->cix < xptr->cix)) &&
	    ((nxptr == NULL) || (yptr->cix < nxptr->cix))) { // Y only
	    xref_t* yptr1 = yptr->next;
	    clause_t* cp  = vp->clause_map[yptr->cix];
	    lit_t yyl     = cp->lit[yptr->p];
	    int rewatch = 0;

//	    enif_fprintf(stdout, "subst cix=%d, Y [%d/%d]\r\n",
//			 cp->cix, export_l(xl), export_l(yyl));
	    
	    // check if Y was TWL then update
	    if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
		unwatch_clause(vp, cp);
		rewatch = 1;
	    }
	    if (yl == yyl) {  // same sign as x
		cp->lit[yptr->p] = xl;
		xp->degree++;
	    }
	    else {
		cp->lit[yptr->p] = neg_l(xl);
		nxp->degree++; 
	    }
	    yp->degree--;

	    if (rewatch) {
		if (watch_clause(vp, cp) <= 0)
		    assert(0);
	    }
	    *xpp = yptr;
	    yptr->next = xptr;
	    xpp = &(yptr->next);
	    yptr = yptr1;
	}
	else if (xptr && (yptr->cix == xptr->cix)) { // X and Y case
	    xref_t* yptr1 = yptr->next;
	    clause_t* cp = vp->clause_map[yptr->cix];
	    lit_t yyl = cp->lit[yptr->p];
	    lit_t xxl = cp->lit[xptr->p];
	    int rewatch = 0;

//	    enif_fprintf(stdout, "subst cix=%d, X,Y [%d/%d]\r\n",
//			 cp->cix, export_l(xxl), export_l(yyl));
	
	    // check if Y was TWL then update
	    if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
		unwatch_clause(vp, cp);
		rewatch = 1;
	    }

	    // ((a=b)&&(c!=d))||((a!=b)&&(c=d)) -> !((a=b)=(c=d))
	    if ((yl == yyl) == (xl == xxl)) {
		cp->lit[yptr->p] = L_FALSE(vp);
		if (!rewatch && is_unit_clause(vp, cp)) {
		    // enif_fprintf(stdout, "UNIT\r\n");
		    put_l(vp, xxl, I_TRUE, xptr->p, cp->cix, vp->level);
		}
	    }
	    else {
		cp->lit[yptr->p] = L_TRUE(vp);
		// enif_fprintf(stdout, "DEAD\r\n");
		if (!(cp->flags & CLAUSE_FLAG_DEAD)) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    vp->cdead++;
		}
		rewatch = 0;
	    }
	    yp->degree--;
	    if (rewatch) {
		if (watch_clause(vp, cp) <= 0)
		    assert(0);
	    }
	    
	    varp_free(&vp->xref_allocator, yptr);
	    yptr = yptr1;
	}
	else if (nxptr && (yptr->cix == nxptr->cix)) { // !X and Y case
	    xref_t* yptr1 = yptr->next;
	    clause_t* cp = vp->clause_map[yptr->cix];
	    lit_t yyl = cp->lit[yptr->p];
	    lit_t xxl = cp->lit[nxptr->p];
	    int rewatch = 0;

//	    enif_fprintf(stdout, "subst cix=%d, !X,Y [%d/%d]\r\n",
//			 cp->cix, export_l(xxl), export_l(yyl));
	
	    // check if Y was TWL then update
	    if ((yptr->p == cp->wl[0].p) || (yptr->p == cp->wl[1].p)) {
		unwatch_clause(vp, cp);
		rewatch = 1;
	    }

	    // ((a=b)&&(c!=d))||((a!=b)&&(c=d)) -> !((a=b)=(c=d))
	    if ((yl == yyl) == (xl == xxl)) {
		cp->lit[yptr->p] = L_FALSE(vp);
		if (!rewatch && is_unit_clause(vp, cp)) {
		    // enif_fprintf(stdout, "UNIT\r\n");
		    put_l(vp, xxl, I_TRUE, nxptr->p, cp->cix, vp->level);
		}
	    }
	    else {
		cp->lit[yptr->p] = L_TRUE(vp);
//		enif_fprintf(stdout, "DEAD\r\n");
		if (!(cp->flags & CLAUSE_FLAG_DEAD)) {
		    cp->flags |= CLAUSE_FLAG_DEAD;
		    vp->cdead++;
		}
		rewatch = 0;
	    }
	    yp->degree--;

	    if (rewatch) {
		if (watch_clause(vp, cp) <= 0)
		    assert(0);
	    }
	    varp_free(&vp->xref_allocator, yptr);
	    yptr = yptr1;
	}
	else {
	    // step xpp and nxpp
	    if (xptr)
		xpp = &(xptr->next);
	    if (nxptr)
		nxpp = &(nxptr->next);
	}
    }
    
    // all the way and update xlast just in case
    while(*xpp != NULL) {
	xref_t* xptr = *xpp;	
	xpp = &(xptr->next);
    }
    // the new last x
    xp->xlast = xpp;
    
    // all the way and update xlast just in case
    while(*nxpp != NULL) {
	xref_t* nxptr = *nxpp;	
	nxpp = &(nxptr->next);
    }
    nxp->xlast = nxpp;
}

// substitue [X/Y] == [X/Y], [!X/!Y]

static void subst(varp_t* vp, lit_t xl, lit_t yl)
{
    literal_t* yp  = l2ll(vp, yl);
    literal_t* xp  = l2ll(vp, xl);
    variable_t* y = yp->var;
    
    assert (yp != xp);
    assert(get_vv(vp, y) == I_UNDEF);

    log_permanent(vp, xp, yp, 0);

    subst_ll(vp, xl, yl);
    subst_ll(vp, neg_l(xl), neg_l(yl));

#ifdef TWO_CLAUSES
    subst_2_clause(vp, xl, yl);
#endif
    
    // mark Y as bound (to X)
    set_vv(vp, y, I_BOUND);
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
    if (is_constant(y)) {
	return enif_make_badarg(env);
    }

    x = get_l(vp, xp);
    if (is_constant(x)) {
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

#define EV_CONFLICT ((literal_t*) -1)
#define EV_NONE     ((literal_t*) 0)
#define EV_DEAD     ((literal_t*) 1)

// eval clause
// return (literal_t*) -1  conflict
// return (literal_t*)  0  non conclusive
// return (literal_t*)  1   dead
// return assigned literal otherwise
//
static inline literal_t* eval_clause(varp_t* vp, clause_t* cp,
				     int wi, wlink_t** wlp)
{
    wlink_t* wl0 = &cp->wl[0];
    wlink_t* wl1 = &cp->wl[1];
    int wp0 = wl0->p;
    int wp1 = wl1->p;

    PRINT_CLAUSE(vp,"ev: ",cp);

    assert(wp0 >= 0);
    assert(wp1 >= 0);
#ifdef TWO_CLAUSES
    assert(cp->size > 2);
#endif
    
    if (wi==0) {  // watch point 0
	size_t csize;
	long   cnt;
	long   p;
	ival_t lw;
	literal_t* lp1;

	lp1 = l2ll(vp, cp->lit[wp1]);
	if ((lw = get_ll(vp, lp1)) == I_TRUE) {
	    CLAUSE_EVAL_COUNT(vp, DEAD_CLAUSE);
	    return EV_DEAD;
	}
	CLAUSE_EVAL_COUNT(vp, ALL_CLAUSE);
	csize = cp->size;
	if (csize <= 3) CLAUSE_EVAL_COUNT(vp, csize);
	cnt = csize;
	
	p = TWL_WP0_INIT;
	while(cnt--) {
	    p = TWL_WP0_WRAP(p,(long)csize);
	    if (p != wp1) {
		lit_t l = l = cp->lit[p];
		ival_t lv = get_l(vp, l);
		if (lv != I_FALSE) {  // I_TRUE | I_UNDEF
		    if (lv == I_TRUE)
			return EV_DEAD;
		    break;  // new watch point found
		}
	    }
	    p = TWL_WP0_NEXT(p);
	}

	DBG("  wp0: %s %d=>%ld\r\n", format_lit(vp, cp->lit[wp0]), wp0, p);
	if (cnt < 0) {  // no new watch point found
	    if (lw == I_FALSE)
		return EV_CONFLICT;
	    else {
		put_nq_ll(vp, lp1, I_TRUE, wp1, cp->cix, vp->level);
		return lp1;
	    }
	}
	else {  // move watch
	    literal_t* mp = l2ll(vp, cp->lit[p]);
	    *wlp = wl0->next;
	    set_wlink(wl0, p, mp);
	}
    }
    else { // watch point 1
	size_t csize;	
	long   cnt;
	long   p;
	ival_t lw;
	literal_t* lp0;

	lp0 = l2ll(vp, cp->lit[wp0]);
	if ((lw = get_ll(vp, lp0)) == I_TRUE) {
	    CLAUSE_EVAL_COUNT(vp, DEAD_CLAUSE);
	    return EV_DEAD;
	}
	CLAUSE_EVAL_COUNT(vp, ALL_CLAUSE);
	csize = cp->size;
	if (csize <= 3) CLAUSE_EVAL_COUNT(vp, csize);
	cnt = csize;
	
	p = TWL_WP1_INIT;
	while(cnt--) {
	    p = TWL_WP1_WRAP(p,(long)csize);
	    if (p != wp0) {
		lit_t l = cp->lit[p];
		ival_t lv = get_l(vp, l);
		if (lv != I_FALSE) {  // I_TRUE | I_UNDEF
		    if (lv == I_TRUE)
			return EV_DEAD;			
		    break;  // new watch point found
		}
	    }
	    p = TWL_WP1_NEXT(p);
	}
	DBG("  wp1: %s %d=>%ld\r\n", format_lit(vp, cp->lit[wp1]), wp1, p);
	if (cnt < 0) {  // no new watch point found
	    if (lw == I_FALSE) // contradiction
		return EV_CONFLICT;
	    else {
		put_nq_ll(vp, lp0, I_TRUE, wp0, cp->cix, vp->level);
		return lp0;
	    }
	}
	else {  // move watch
	    literal_t* mp = l2ll(vp, cp->lit[p]);
	    *wlp = wl1->next;
	    set_wlink(wl1, p, mp);
	}
    }
    return EV_NONE;
}

static int eval1(varp_t* vp, literal_t* lp);

#ifdef TWO_CLAUSES
// eval 2-clauses
static int eval_2_clauses(varp_t* vp, literal_t* lp)
{
    edge_t* pl;
    // lit_t l = ll2l(vp, lp); 
	
    lp = neg_ll(lp);
    pl = lp->elist;

    while(pl) {
	literal_t* lp1;
	    
	CLAUSE_EVAL_COUNT(vp, ALL_CLAUSE);
	CLAUSE_EVAL_COUNT(vp, 2);

#if defined(DEBUG) && defined(DEBUG_EVAL)		
	enif_fprintf(stdout, "eval2: [%s,%s]\r\n",
		     format_lit(vp, l), format_lit(vp, pl->l));
#endif
	lp1 = l2ll(vp, pl->l);
	switch(get_ll(vp, lp1)) {
	case I_TRUE:
	    CLAUSE_EVAL_COUNT(vp, DEAD_CLAUSE);
	    break; // noop
	case I_FALSE:
	    if (vp->max_conflicting == 1) {
		vp->conflicting_clauses[vp->num_conflicting++] = pl->cix;
		return -1;
	    }
	    else if (vp->num_conflicting < vp->max_conflicting) {
		vp->conflicting_clauses[vp->num_conflicting++] = pl->cix;
	    }
	    else
		return -1;
	    break;
	case I_UNDEF:
	    put_nq_ll(vp, lp1, I_TRUE, 1, pl->cix, vp->level);
	    if (vp->qtype == recursive) {
		if (eval1(vp, neg_ll(lp1)) < 0)
		    return -1;
	    }
	    else {
		lqueue_put_ll(vp, neg_ll(lp1));
	    }
	    break;
	case I_BOUND: {
	    enif_fprintf(stdout, "lp->sign=%d\r\n", lp1->sign);
	    enif_fprintf(stdout, "lp->var->bound=%p\r\n", lp1->var->bound);
	    enif_fprintf(stdout, "was bound\r\n");
	    break;
	}
	default:
	    assert(0);
	    break;
	}
	pl = pl->next;
    }
    return 0;
}
#endif

// eval literal chain lp 
static int eval_clauses(varp_t* vp, literal_t* lp)
{
    wlink_t** wlp = &lp->wlist;
    wlink_t*  wl;

    while((wl = *wlp) != NULL) {
	clause_t* cp = clause_pointer(wl);
#if defined(DEBUG) && defined(DEBUG_EVAL)
	print_sym_clause(vp, "eval: ", cp);
#endif
	if (!(cp->flags & (CLAUSE_FLAG_CONFLICT|CLAUSE_FLAG_DEAD))) {
	    int wi = wlink_index(wl);
	    lp = eval_clause(vp, cp, wi, wlp);
	    if (lp == EV_CONFLICT) {
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
	    }
	    else if (lp == EV_DEAD) {
		if (vp->level == 0) {
		    // print_sym_clause(vp, "DIE", cp);
		    schedule_unwatch_clause(vp, cp);
		    vp->cdead++;
		    cp->flags |= CLAUSE_FLAG_DEAD;
		}
	    }
	    else if (lp == EV_NONE) {
		;
	    }
	    else {
		if (vp->qtype == recursive) {
		    if (eval1(vp, neg_ll(lp)) < 0)
			return -1;
		}
		else {
		    lqueue_put_ll(vp, neg_ll(lp));
		}
	    }
	}
	if (*wlp == wl)
	    wlp = &wl->next;
    }
    return 0;
}

static int eval1(varp_t* vp, literal_t* lp)
{
    int r = 0;

    r = eval_clauses(vp, lp);

#ifdef TWO_CLAUSES
    if (r >= 0) r = eval_2_clauses(vp, lp);
#endif
    if (vp->level == 0) {
	// kill clauses on the TRUE side
	kill_x_clauses(vp, neg_ll(lp));
#ifdef TWO_CLAUSES
	// convert 3-clauses to 2-clauses when possible
	check_2_clauses(vp, lp);
#endif
    }
    return r;
}

static int eval(varp_t* vp)
{
    literal_t* lp;
    while((lp = lqueue_get(vp)) != NULL) {
	if (eval1(vp, lp) < 0)
	    break;
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
    clause_t* cp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    vp->eval_counter++;
    vp->num_conflicting = 0;

    DBG("EVAL %ld\r\n", vp->eval_counter);

    vp->caller_env = env;
    eval(vp);
    vp->caller_env = NULL;

    if ((cp = vp->unwatch) != NULL) {
	while(cp != NULL) {
#ifdef TWO_CLAUSES
	    if (cp->flags & CLAUSE_FLAG_TWO) {
		lit_t a = cp->lit[cp->wl[0].p];
		lit_t b = cp->lit[cp->wl[1].p];
		edge_insert(vp, neg_l(a), b, cp->cix);
		edge_insert(vp, neg_l(b), a, cp->cix);		
#if 0    
		if ((cp->wl[0].p >= 0) && (cp->wl[1].p >= 0)) {
		    lit_t a = cp->lit[cp->wl[0].p];
		    lit_t b = cp->lit[cp->wl[1].p];
		    if ((get_l(vp,a) == I_UNDEF) && (get_l(vp,b) == I_UNDEF)) {
			edge_insert(vp, neg_l(a), b, cp->cix);
			edge_insert(vp, neg_l(b), a, cp->cix);
		    }
		}
#endif
	    }
#endif
	    unwatch_clause(vp, cp);
	    cp->flags &= ~CLAUSE_FLAG_UNWATCH;
	    cp = cp->uwatch;
	}
	vp->unwatch = NULL;
    }
    
    if (vp->num_conflicting) {
	int i;
	lqueue_clear(&vp->q);
	DBG("num conflicts = %d\n", vp->num_conflicting);
	if (vp->activity)
	    activate_levels(vp, 1.0);
	for (i = 0; i < vp->num_conflicting; i++) {
	    cix_t cix = vp->conflicting_clauses[i];
	    if ((cp = vp->clause_map[cix]) != NULL)
		cp->flags &= ~CLAUSE_FLAG_CONFLICT;
	}
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
    else if (argv[1] == ATOM(number_of_conflicting_clauses)) {
	return enif_make_int(env, vp->num_conflicting);
    } 
    else if (argv[1] == ATOM(number_of_variables)) {
	return enif_make_int(env, vp->vnum);
    }
    else if (argv[1] == ATOM(number_of_clauses)) {
	return enif_make_int(env, vp->cnum);
    }
    else if (argv[1] == ATOM(number_of_dead_clauses)) {
	return enif_make_int(env, vp->cdead);
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
	return enif_make_uint64(env, vp->clause_eval_counter[ALL_CLAUSE]);
    }
    else if (argv[1] == ATOM(clause2_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter[PAIR_CLAUSE]);
    }
    else if (argv[1] == ATOM(clause3_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter[TRIPLE_CLAUSE]);
    }
    else if (argv[1] == ATOM(dead_eval_counter)) {
	return enif_make_uint64(env, vp->clause_eval_counter[DEAD_CLAUSE]);
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
    else if (argv[1] == ATOM(qtype)) {
	switch(vp->qtype) {
	case lifo: return ATOM(lifo);
	case fifo: return ATOM(fifo);
	case recursive: return ATOM(recursive);
	default: return ATOM(undefined);
	}
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
    else if (argv[1] == ATOM(literal_size)) {
	return enif_make_uint(env, 8*sizeof(lit_t));
    }
    else if (argv[1] == ATOM(literal_integer)) {
#ifdef LIT_INTEGER
	return ATOM(true);
#else
	return ATOM(false);
#endif
    }
    else if (argv[1] == ATOM(literal_signed)) {
#ifdef SIGNED_LITERALS
	return ATOM(true);
#else
	return ATOM(false);
#endif
    }
    else if (argv[1] == ATOM(value_packing)) {
#ifdef PACKED_VALUE
	return enif_make_uint(env, PACKED_VALUE);
#else
	return ATOM(undefined);
#endif
    }
    else if (argv[1] == ATOM(edge_list)) {
#ifdef TWO_CLAUSES
	return ATOM(true);
#else
	return ATOM(false);
#endif
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
static int cmp_abs_lit QSORT_R_ARGS(const void* ap,const void* bp,void* arg)
{
    (void) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);

    if (a == b) return 0;
#ifdef LIT_INTEGER
    if (INDEX(a) == INDEX(b)) {
	if (IS_NEGATED(a)) return -1;
	return 1;
    }
    return INDEX(a) - INDEX(b);
#else
    if (a->var == b->var) {
	if (a->sign < 0) return -1;
	else return 1;
    }
    return a->var->vix - b->var->vix;
#endif
}

#if 0
static int cmp_rev_abs_lit QSORT_R_ARGS(const void* ap,const void* bp,void* arg)
{
    (void) arg;
    lit_t a = *((lit_t*) ap);
    lit_t b = *((lit_t*) bp);

    if (a == b) return 0;
#ifdef LIT_INTEGER
    if (INDEX(a) == INDEX(b)) {
	if (IS_NEGATED(a)) return -1;
	return 1;
    }
    return INDEX(b) - INDEX(a);
#else
    if (a->var == b->var) {
	if (a->sign < 0) return -1;
	else return 1;
    }
    return b->var->vix - a->var->vix;
#endif
}
#endif

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
		if (lp->var->level == 0) {
		    switch(get_literal_value(vp,lp)) {
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
    PRINT_LIT_ARRAY("   filt0", lit, size);
    
    // sort all literals by absolute value
    QSORT_R(lit, size, sizeof(lit_t), cmp_abs_lit, vp);

    PRINT_LIT_ARRAY(" sorted", lit, size);

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

    PRINT_LIT_ARRAY("   dest", lit, size);
    return size;
}


static ERL_NIF_TERM add_clause_array(ErlNifEnv* env, varp_t* vp,
				     lit_t* lit, size_t size)
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
	shuffle_key_t skey[size];
	for (i = 0; i < size; i++) {
	    skey[i].lit = lit[i];
	    skey[i].key = arc4_random(&vp->as);
	}
	QSORT_R(skey, size, sizeof(shuffle_key_t), cmp_shuffle, 0);
	for (i = 0; i < size; i++)
	    lit[i] = skey[i].lit;
    }
    PRINT_LIT_ARRAY("shuffle", lit, size);
#endif

#ifdef CLAUSE2_MAP
    if (size == 2) {
	ulitx2_t index2 = cantor_pair(lit[0], lit[1]);
	if (vp->clause2_map[index2]) {
	  print_lit_array("clause already installed", lit, 2);
	  return ATOM(true);
	}
	vp->clause2_map[index2] = 1;
	// return index index2!!!
    }
#endif
    
    if ((cp = clause_alloc(vp, size)) == NULL)
	goto error;
    hvalue = (uint32_t) literal_array_hash(lit, size);
    if ((cix = clause_insert(vp, cp, hvalue)) == CLAUSE_ERROR)
	goto error;

    // enif_fprintf(stdout, "add cix=%d hvalue=%u ", cp->cix, hvalue);
    // print_lit_array("", lit, size);

    memcpy(cp->lit, lit, sizeof(lit_t)*size);

    switch (link_clause(vp, cp)) {
    case -1:
	goto error;
    case 0:
	return enif_make_tuple2(env, ATOM(false), make_cix(env, cix));
    case 1:
	return enif_make_tuple2(env, ATOM(true), make_cix(env, cix));
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
    UNUSED(argc);
    varp_t* vp;
    int size;
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
	ret = add_clause_array(env, vp, literals, size);
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
	if ((cix=clause_find(vp, literals, size)) == CLAUSE_ERROR)
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
	if ((cp = vp->clause_map[cix]) == NULL) {
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
    size_t size = cp->size;
    long p;
    
#ifdef TWO_CLAUSES
    if (size == 2) {
	lit_t* lit  = cp->lit;    
	edge_remove(vp, neg_l(lit[0]), lit[1], cp->cix);
	edge_remove(vp, neg_l(lit[1]), lit[0], cp->cix);
    }
#endif
    unwatch_clause(vp, cp);      // remove watched literals
    // remove xref
    for (p = 0; p < (int)size; p++)
	del_xref(vp, cp, p);
}

static void remove_clause(varp_t* vp, clause_t* cp)
{
    if (cp != NULL) {
	unlink_clause(vp, cp);
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
	    if ((cix=clause_find(vp, literals, size)) == CLAUSE_ERROR)
		return enif_make_badarg(env);
	}
    }

    if (vp->level != 0)
	return enif_make_badarg(env);
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);

    remove_clause(vp, cp);
    
    assert(vp->clause_map[cix] == NULL);

    // check if we have a hole at the end, update cnext
    if (cix+1 == (int)vp->cnext) {  // we remove the last clause
	while((cix>0) && (vp->clause_map[cix-1] == NULL))
	    cix--;
	vp->cnext = cix;
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
    if ((cp = vp->clause_map[cix]) == NULL)
	return ATOM(ok);

    size = cp->size;
    lit  = cp->lit;

    DBG("cleanup: clause %d, size=%lu\r\n", cix, size);

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
    vp->clause_map[cix] = NULL;    
    clause_free(vp, cp);
    return ATOM(ok);

error:
    return enif_make_badarg(env);    
}

// may only clean literal on level 0!
static ERL_NIF_TERM varp_clean_literal(ErlNifEnv* env, int argc,
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
//	    enif_fprintf(stdout, "remove 2-clause cix=%d, lit=%d\r\n",
//			 ep->cix, export_l(ep->l));
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

static ERL_NIF_TERM varp_sort_none_permanent_clauses(ErlNifEnv* env, int argc,
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

    // sort the upper part of clauses, the conflict clauses
    // k elements
    k = vp->cnext - vp->cpermanent; // number of conflict clauses
    
    QSORT_R(vp->clause_map+vp->cpermanent, k, sizeof(clause_t*), cmp_stamp, vp);

    // update all cix after sort
    for (i = vp->cpermanent; i < (int)vp->cnext; i++)
	vp->clause_map[i]->cix = i;
    return ATOM(ok);
}

static ERL_NIF_TERM varp_clause_first(ErlNifEnv* env, int argc,
				      const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    i = 0;
    while(i < (int)vp->cnext) {
	if (vp->clause_map[i] != NULL)
	    return make_cix(env, (cix_t)i);
	i++;
    }
    return ATOM(false);
}

static ERL_NIF_TERM varp_clause_first_none_keep(ErlNifEnv* env, int argc,
						const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    int i;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    i = vp->cpermanent+vp->keep;
    while(i < (int)vp->cnext) {
	if (vp->clause_map[i] != NULL)
	    return make_cix(env, (cix_t)i);
	i++;
    }
    return ATOM(false);
}

static ERL_NIF_TERM varp_clause_next(ErlNifEnv* env, int argc,
				     const ERL_NIF_TERM argv[])
{
    UNUSED(argc);    
    varp_t* vp;
    int cix;
    int i;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);
    if (!enif_get_int(env, argv[1], &cix) || (cix < 0))
	return enif_make_badarg(env);
    for (i=cix+1; i < (int)vp->cnext; i++) {
	if (vp->clause_map[i] != NULL)
	    return make_cix(env, (cix_t)i);
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

    if ((cp = vp->clause_map[cix]) == NULL)
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
    if ((cp = vp->clause_map[cix]) == NULL)
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
    if ((cp = vp->clause_map[cix]) == NULL)
	return enif_make_badarg(env);
    
    if (cix >= (int)vp->cpermanent) // WTF
	cp->stamp = vp->eval_counter;
    return ATOM(ok);
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
    if (decay <= 1.0)  // maybe allow values < 1.0...
	return enif_make_badarg(env);
    if (vp->activity)
	activity_decay(vp, decay);
    return ATOM(ok);
}

static ERL_NIF_TERM varp_subscribe(ErlNifEnv* env, int argc,
				   const ERL_NIF_TERM argv[])
{
    UNUSED(argc);
    varp_t* vp;
    
    if (!enif_get_resource(env, argv[0], varp_res, (void**) &vp))
	return enif_make_badarg(env);

    if ((argv[1] == ATOM(atom)) ||
	(argv[1] == ATOM(variable))) {
	subscription_t* sp;
	int r;
	if ((sp = varp_alloc(&vp->sub_allocator)) == NULL)
	    return enif_make_badarg(env);
	r = enif_monitor_process(env, vp, enif_self(env,&sp->pid), &sp->mon);
	if (r != 0) {
	    // r < 0 no down callback, r > 0 process not alive
	    varp_free(&vp->sub_allocator, sp);
	    return enif_make_badarg(env);
	}
	sp->what = argv[1];
	// link in first
	sp->next = vp->subs;
	vp->subs = sp;
	
	return ATOM(ok);	
    }
    return enif_make_badarg(env);
}

#ifdef TWO_CLAUSES
static ERL_NIF_TERM get_2_clauses(ErlNifEnv* env, varp_t* vp,
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
#endif

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
#ifdef TWO_CLAUSES
	list = get_2_clauses(env, vp, neg_ll(lp), list);
	list = get_2_clauses(env, vp, lp, list);
#endif
    }
    else if (argv[2] == ATOM(literal)) {
	xref_t* xp = lp->xfirst;
	while(xp) {
	    if (vp->clause_map[xp->cix] != NULL) {
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
		if (vp->clause_map[xp->cix] != NULL) {
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
    LOAD_ATOM(identity);
    LOAD_ATOM(random);
    LOAD_ATOM(degree);
    LOAD_ATOM_STRING(plus_degree, "+degree");
    LOAD_ATOM_STRING(minus_degree,"-degree");
    LOAD_ATOM(rank);
    LOAD_ATOM_STRING(plus_rank, "+rank");
    LOAD_ATOM_STRING(minus_rank,"-rank");
    // LOAD_ATOM(activity);
    LOAD_ATOM_STRING(plus_activity, "+activity");
    LOAD_ATOM_STRING(minus_activity,"-activity");
    
    // info
    LOAD_ATOM(max_clause_length);
    LOAD_ATOM(max_conflicting);
    LOAD_ATOM(number_of_conflicting_clauses);
    LOAD_ATOM(number_of_clauses);
    LOAD_ATOM(number_of_dead_clauses);
    LOAD_ATOM(number_of_learned_clauses);    
    LOAD_ATOM(number_of_variables);
    LOAD_ATOM(number_of_bound_variables);
    LOAD_ATOM(number_of_unbound_variables);    
    LOAD_ATOM(clause_eval_counter);
    LOAD_ATOM(dead_eval_counter);
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
    LOAD_ATOM(symbol);    
    LOAD_ATOM(activity);
    LOAD_ATOM(clause_hash);    
    LOAD_ATOM(implication);    
    LOAD_ATOM(implication_clause);
    LOAD_ATOM(implication_pos);
    LOAD_ATOM(is_atom);
    LOAD_ATOM(edge_list);
    LOAD_ATOM_STRING(exclamation_mark, "!");
    LOAD_ATOM(literal_size);
    LOAD_ATOM(literal_signed);
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
	    char buf[80];
	    enif_snprintf(buf, sizeof(buf), "process %T died",
			  enif_make_pid(env, &sp->pid));
	    enif_fprintf(stdout, "%s\r\n", buf);
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
