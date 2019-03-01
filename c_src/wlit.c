//
// Test of watched literals data structures
//
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>

#define UNSAT  -1
#define OK     0
#define ERROR  1

#define UNDEF  0
#define FALSE -1
#define TRUE   1

#ifdef DEBUG
#define DBG(args...) printf(args)
#else
#define DBG(args...)
#endif

typedef struct _literal_t
{
    int sign;                  // -1=negative,  1=positive
    struct _variable_t* var;
    struct _wlink_t* wlist;    // list of watch positions
    struct _literal_t* qlink;  // unit propagation queue
} literal_t;

typedef struct _lqueue_t
{
    literal_t* head;
    literal_t** tail;
} lqueue_t;

typedef struct _variable_t
{
    char* name;
    int  value;               // -1=false  0=unassigned  1=true
    struct _variable_t* next; // variable list
    literal_t lit[2];         // literal containers pos=0 neg=1
} variable_t;


// p > 0   p increase
// p < 0   p decrease
// trunc (wlink) to get clause_t* pointer
typedef struct _wlink_t
{
    struct _wlink_t* next;
    long p;
} wlink_t;

// sizeof wlink should be 8 on 32 bit machine or 16 on 64 bit machine
// 32 bit machine alignement should be 2*8 = 16 bytes
// 64 bit machine alignement should be 2*16 = 32 bytes
#define CLAUSE_ALIGNMENT (2*sizeof(wlink_t))

typedef struct _clause_t
{
    wlink_t    wl[2];        // watch point 1&2+links
    struct _clause_t* next;  // clause list
    unsigned long id;        // clause id
    unsigned long size;      // number of literals in lit
    literal_t* lit[];        // literal array
} clause_t;

typedef struct _sat_t
{
    size_t num_variables;
    size_t num_clauses;
    variable_t* variable_list;  // all variables
    clause_t*   clause_list;    // all clauses
    variable_t  cnst;           // true & false
    lqueue_t    q;              // literal queue for propagation
} sat_t;


void lqueue_init(lqueue_t* q)
{
    q->head = NULL;
    q->tail = &q->head;
}

void lqueue_enq(lqueue_t* q, literal_t* lp)
{
    lp->qlink = NULL;
    *q->tail = lp;
    q->tail = &(lp->qlink);
}

literal_t* lqueue_deq(lqueue_t* q)
{
    literal_t* lp;
    
    if ((lp = q->head) == NULL)
	return NULL;
    if ((q->head = lp->qlink) == NULL)
	q->tail = &q->head;
    return lp;
}

int get_literal(literal_t* lp)
{
    if (lp->sign < 0) return -lp->var->value;
    return lp->var->value;
}

// assume literal is unassigned!
void set_literal(literal_t* lp, int value)
{
    if (lp->sign < 0)
	lp->var->value = -value;
    else
	lp->var->value = value;
}

literal_t* negate_literal(literal_t* lp)
{
    variable_t* var = lp->var;
    return (lp == &var->lit[0]) ? &var->lit[1] : &var->lit[0];
}

int assign_literal(literal_t* lp, int value)
{
    if (lp->var->value == UNDEF) 
	set_literal(lp, value);
    else if (get_literal(lp) != value)
	return UNSAT;
    return OK;
}


void print_literal(FILE* f, literal_t* lp)
{
    if (strcmp(lp->var->name, "true") == 0) {
	if (lp->sign < 0)
	    fprintf(f, "false");
	else
	    fprintf(f, "true");
    }
    else {
	if (lp->sign < 0)
	    fprintf(f, "!%s", lp->var->name);
	else
	    fprintf(f, "%s", lp->var->name);
    }
}

void print_literal_array(FILE* f, literal_t** lv, size_t size)
{
    fprintf(f, "{");
    if (size > 0) {
	int i;
	print_literal(f, lv[0]);
	for (i = 1; i < size; i++) {
	    fprintf(f, ",");
	    print_literal(f, lv[i]);
	}
    }
    fprintf(f, "}");
}

void print_clause(FILE* f, clause_t* cp)
{
    fprintf(f, "%ld:", cp->id);
    print_literal_array(f, cp->lit, cp->size);
}

void print_clause_info(FILE* f, clause_t* cp)
{
    print_clause(f, cp);
    fprintf(f, " wp0=%ld, wp1=%ld\n", cp->wl[0].p, cp->wl[1].p);
}

static void init_var(variable_t* vp)
{
    vp->value = UNDEF;

    vp->lit[0].sign = 1;
    vp->lit[0].var  = vp;
    vp->lit[0].wlist = NULL;

    vp->lit[1].sign = -1;
    vp->lit[1].var  = vp;
    vp->lit[1].wlist = NULL;    
}

void clear_wlink(clause_t* cp, int i)
{
    cp->wl[i].p = -1;      // mark dead for debug
    cp->wl[i].next = NULL;		
}

void add_wlink(clause_t* cp, int i, long p)
{
    cp->wl[i].p = p;                     // new watch point
    cp->wl[i].next = cp->lit[p]->wlist;  // link literal
    cp->lit[p]->wlist = &cp->wl[i];
}

variable_t* new_variable(sat_t* sat, char* name)
{
    variable_t* v;
    
    if ((v = malloc(sizeof(variable_t))) != NULL) {
	v->name = strdup(name);
	init_var(v);
	v->next = sat->variable_list;
	sat->variable_list = v;
	sat->num_variables++;
    }
    return v;
}

// lookup variable (or constant)
variable_t* find_variable(sat_t* sat, char* name)
{
    variable_t* v = sat->variable_list;
    
    if (strcmp(name, "false") == 0)
	return &sat->cnst;
    else if (strcmp(name, "true") == 0)
	return &sat->cnst;
    while(v && (strcmp(name, v->name) != 0))
	v = v->next;
    return v;
}


// lookup or create variable
variable_t* variable(sat_t* sat, char* name)
{
    variable_t* v;
    if ((v = find_variable(sat, name)) == NULL)
	v = new_variable(sat, name);
    return v;
}


literal_t* literal(sat_t* sat, char* name)
{
    int sign = 0;
    variable_t* v;

    while(*name == '!') {
	sign ^= 1;
	name++;
    }
    if (strcmp(name, "false") == 0)
	sign ^= 1;
    v = variable(sat, name);
    return &v->lit[sign];
}

static int cmp_literals(const void* a, const void* b)
{
    literal_t* ap = *((literal_t**) a);
    literal_t* bp = *((literal_t**) b);

    if (ap == bp) return 0;
    else if (ap->var == bp->var) {
	if (ap->sign < 0) return -1;
	else return 1;
    }
    if (strcmp(ap->var->name, "true") == 0)
	return 1;
    return strcmp(ap->var->name, bp->var->name);
}

int new_clause(sat_t* sat, clause_t** cpp, size_t size, literal_t** lit)
{
    clause_t* cp;
    literal_t* lp;
    int i, r, wp0, wp1;
    unsigned Tc=0, Fc=0;    

    if ((r=posix_memalign((void**)&cp, CLAUSE_ALIGNMENT,
			  sizeof(clause_t) + sizeof(literal_t*)*size)) != 0) {
	errno = r;
	if (cpp) *cpp = NULL;
	return ERROR;
    }

    cp->id   = ++sat->num_clauses;
    cp->next = sat->clause_list;
    sat->clause_list = cp;

    memcpy(cp->lit, lit, sizeof(literal_t*)*size);

    printf("INPUT: ");
    print_literal_array(stdout,cp->lit,size); printf("\n");
    
    // sort literals
    qsort(cp->lit, size, sizeof(literal_t*), cmp_literals);

    printf("QSORT: ");
    print_literal_array(stdout,cp->lit,size); printf("\n");
    
    i = size-1;
    // remove TRUE literals
    while((i >= 0) && (cp->lit[i] == &sat->cnst.lit[0])) {
	i--; size--; Tc++;
    }
    printf("TRUE: ");
    print_literal_array(stdout,cp->lit,size); printf("\n");
    
    // remove FALSE literals
    while((i >= 0) && (cp->lit[i] == &sat->cnst.lit[1])) {
	i--; size--; Fc++;
    }
    printf("FALSE: ");
    print_literal_array(stdout,cp->lit,size); printf("\n");

    { // remove duplicates 
	unsigned u=0,v=0,w=0;
	while(v < size) {
	    while((w < size) && (cp->lit[v] == cp->lit[w]))
		w++;
	    if ((u > 0) && (cp->lit[u-1] == negate_literal(cp->lit[v]))) {
		u--;
		Tc++;
	    }
	    else
		cp->lit[u++] = cp->lit[v];
	    v = w;
	}
	size = u;
    }
    printf("DUP: ");
    print_literal_array(stdout,cp->lit,size); printf("\n");    

    if (size == 0) {
	if ((Tc==0) && (Fc>0)) // make sure it's not empty
	    cp->lit[size++] = &sat->cnst.lit[1];
    }
    if (Tc>0) // add the T constant
	cp->lit[size++] = &sat->cnst.lit[0];
    printf("CONST: ");
    print_literal_array(stdout,cp->lit,size); printf("\n");    

    cp->size = size;

    cp->wl[0].p = -1;
    cp->wl[1].p = -1;

    wp0 = 0;
    wp1 = size-1;
    
    while(wp0 < size) {
	switch(get_literal(cp->lit[wp0])) {
	case FALSE: break;
	case TRUE:  goto dead;
	case UNDEF: goto next_wp;
	}
	wp0++;
    }
    if (wp0 == size) {  // all literals are false
	if (cpp) *cpp = cp;
	return UNSAT;
    }
next_wp:
    while(wp1 > wp0) {
	switch(get_literal(cp->lit[wp1])) {
	case FALSE: break;
	case TRUE:  goto dead;
	case UNDEF: goto done_wp;
	}
	wp1--;
    }
    // wp1 == wp2 unit propagation 
    set_literal(cp->lit[wp0], TRUE);
    lqueue_enq(&sat->q, negate_literal(cp->lit[wp0]));
    if (cpp) *cpp = cp;
    return OK;
done_wp:
    add_wlink(cp, 0, wp0);       // watch literal 0
    add_wlink(cp, 1, wp1);       // watch literal 1
dead:
    if (cpp) *cpp = cp;
    return OK;
}


//
// Fixme:
//   remove duplicates
//   remove constant FALSE
//   mark clause as dead if contain constant TRUE or A !A
//   ...
//
int clause(sat_t* sat, clause_t** cpp, size_t size, ...)
{
    va_list ap;
    literal_t* lit[size];
    int i;

    va_start(ap, size);
    for (i = 0; i < size; i++) {
	char* lname = va_arg(ap, char*);
	lit[i] = literal(sat, lname);
    }
    va_end(ap);
    
    return new_clause(sat, cpp, size, lit);
}

// Clause point from wlink_t pointer
clause_t* clause_pointer(wlink_t* wl)
{
    intptr_t w = (intptr_t) wl;
    return (clause_t*) (w & ~(CLAUSE_ALIGNMENT-1));
}

int wlink_index(wlink_t* wl)
{
    intptr_t w = (intptr_t) wl;
    return (w & (CLAUSE_ALIGNMENT-1)) / sizeof(wlink_t);
}


void sat_init(sat_t* sat)
{
    memset(sat, 0, sizeof(sat_t));

    sat->cnst.name = "true";
    init_var(&sat->cnst);
    sat->cnst.value = TRUE;

    sat->cnst.next = sat->variable_list;
    sat->variable_list = &sat->cnst;
    lqueue_init(&sat->q);
}

// check watch points and update clauses
// we clear the literal watch list 
int propagate(sat_t* sat)
{
    literal_t* lp;
    
    while((lp = lqueue_deq(&sat->q)) != NULL) {
	wlink_t* wl = lp->wlist;

	DBG("deq: %s=%d\n", lp->var->name, get_literal(lp));
	
	lp->wlist = NULL;  // wlist is cleared
	
	while(wl) {
	    wlink_t* wln = wl->next;  // save next before process
	    clause_t* cp = clause_pointer(wl);
	    int wp0 = cp->wl[0].p;
	    int wp1 = cp->wl[1].p;
	    long p;
	    int lv;

	    
	    DBG("eval clause:");
	    #ifdef DEBUG
	    print_clause(stdout, cp);
	    printf("\n");
	    #endif
	    if (wlink_index(wl)==0) {  // move forward
		DBG("  fwd: %s=%d\n",
		    cp->lit[wp0]->var->name, get_literal(cp->lit[wp0]));
		p = wp0;
		while((p <= wp1) && ((lv=get_literal(cp->lit[p])) == FALSE))
		    p++;
		cp->wl[0].p = p;
		if (p > wp1) // all false
		    return UNSAT;
		else if (p == wp1) {
		    if (lv == UNDEF) {  // unit propagation
			set_literal(cp->lit[p], TRUE);
			lqueue_enq(&sat->q, negate_literal(cp->lit[p]));
		    }		    
		    else if (lv == TRUE) {
			clear_wlink(cp, 0);
		    }
		}
		else {
		    add_wlink(cp, 0, p);
		}
	    }
	    else { // move backward
		DBG("  bwd: %s=%d\n",
		    cp->lit[wp1]->var->name, get_literal(cp->lit[wp1]));
		p = wp1;
		while((p >= wp0) && ((lv=get_literal(cp->lit[p])) == FALSE))
		    p--;
		cp->wl[1].p = p;
		if (p < wp0) // all false
		    return UNSAT;
		else if (p == wp0) {
		    if (lv == UNDEF) { // unit propagation
			set_literal(cp->lit[p], TRUE);
			lqueue_enq(&sat->q, negate_literal(cp->lit[p]));
		    }
		    else if (lv == TRUE) {
			clear_wlink(cp, 1);			
		    }
		}
		else {
		    add_wlink(cp, 1, p);
		}
	    }
	    wl = wln;
	}
    }
    return OK;
}

int set_variable(sat_t* sat, variable_t* xp, int value)
{
    if (xp->value) {
	if (xp->value != value)
	    return UNSAT;  // UNSAT
	return OK;
    }
    if (value == FALSE) {
	xp->value = value;
	lqueue_enq(&sat->q, &xp->lit[0]);
	return OK;
    }
    else if (value == TRUE) {
	xp->value = value;
	lqueue_enq(&sat->q, &xp->lit[1]);
	return OK;
    }
    return ERROR;  // bad value?
}

int set(sat_t* sat, char* name, int value)
{
    literal_t* lp = literal(sat, name);
    if (lp->sign < 0)
	return set_variable(sat, lp->var, -value);
    else
	return set_variable(sat, lp->var, value);
}

void dump_literals(FILE* f, sat_t* sat)
{
    variable_t* vp;

    for (vp = sat->variable_list; vp != NULL; vp = vp->next) {
	int i;
	fprintf(f, "%s = %d, ", vp->name, vp->value);
	for (i = 0; i < 2; i++) {
	    literal_t* lp;
	    wlink_t* wl;
	    int wi;
	    lp = &vp->lit[i];
	    fprintf(f,"  "); print_literal(f, lp); fprintf(f," -> {");
	    if ((wl = lp->wlist) != NULL) {
		clause_t* cp = clause_pointer(wl);
		wi = wlink_index(wl);
		fprintf(f,"%ld:%ld", cp->id, cp->wl[wi].p);
		wl = wl->next;
	    }
	    while(wl) {
		clause_t* cp = clause_pointer(wl);
		wi = wlink_index(wl);
		fprintf(f,",%ld:%ld", cp->id, cp->wl[wi].p);
		wl = wl->next;
	    }
	    fprintf(f, "}");
	}
	fprintf(f,"\n");
    }    
}

int main(int argc, char** argv)
{
    sat_t sat;
    clause_t* cp;
    variable_t* vp;

    sat_init(&sat);

    clause(&sat, NULL, 5, "a", "!a", "b", "b", "!a");
    clause(&sat, NULL, 5, "false", "!b", "!c", "true", "false");
    clause(&sat, NULL, 2, "c", "d");
    clause(&sat, NULL, 4, "!b", "c", "e", "!d");

    for (cp = sat.clause_list; cp != NULL; cp = cp->next) {
	print_clause(stdout, cp);
	fprintf(stdout, "\n");
    }

    dump_literals(stdout, &sat);

    if (set(&sat, "a", FALSE) == UNSAT)
	printf("UNSAT\n");
    else if (propagate(&sat) == UNSAT)
	printf("UNSAT\n");

    for (cp = sat.clause_list; cp != NULL; cp = cp->next) {
	print_clause(stdout, cp);
	fprintf(stdout, "\n");
    }
    
    dump_literals(stdout, &sat);

    exit(0);
}
