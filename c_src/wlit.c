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
} sat_t;


int literal_value(literal_t* lp)
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

int assign_literal(literal_t* lp, int value)
{
    if (lp->var->value == UNDEF) 
	set_literal(lp, value);
    else if (literal_value(lp) != value)
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

void print_clause(FILE* f, clause_t* cp)
{
    fprintf(f, "{%ld: ", cp->id);
    if (cp->size > 0) {
	int i;
	print_literal(f, cp->lit[0]);
	for (i = 1; i < cp->size; i++) {
	    fprintf(f, ",");
	    print_literal(f, cp->lit[i]);
	}
    }
    fprintf(f, "} wp1=%ld, wp2=%ld\n", cp->wl[0].p, cp->wl[1].p);
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

// lookup or create variable
variable_t* variable(sat_t* sat, char* name)
{
    variable_t* v = sat->variable_list;

    if (strcmp(name, "false") == 0)
	return &sat->cnst;
    else if (strcmp(name, "true") == 0)
	return &sat->cnst;
    while(v && (strcmp(name, v->name) != 0))
	v = v->next;
    if (v == NULL) {
	v = malloc(sizeof(variable_t));
	v->name = strdup(name);

	init_var(v);
    
	v->next = sat->variable_list;
	sat->variable_list = v;
	sat->num_variables++;
    }
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

//
// Fixme:
//   remove duplicates
//   remove constant FALSE
//   mark clause as dead if contain constant TRUE or A !A
//   ...
//
clause_t* clause(sat_t* sat, size_t size, ...)
{
    va_list ap;
    clause_t* cp;
    literal_t* lp;
    int i, r, wp1, wp2;

    if ((r=posix_memalign((void**)&cp, CLAUSE_ALIGNMENT,
			  sizeof(clause_t) + sizeof(literal_t*)*size)) != 0) {
	errno = r;
	return NULL;
    }
    
    va_start(ap, size);
    for (i = 0; i < size; i++) {
	char* lname = va_arg(ap, char*);
	cp->lit[i] = literal(sat, lname);
    }
    va_end(ap);
    cp->id = sat->num_clauses++;
    cp->size = size;
    cp->next = sat->clause_list;
    sat->clause_list = cp;

    cp->wl[0].p = -1;
    cp->wl[1].p = -1;

    wp1 = 0;
    while(wp1 < size) {
	switch(literal_value(cp->lit[wp1])) {
	case FALSE: break;
	case TRUE:  goto dead;
	case UNDEF: goto next_wp;
	}
	wp1++;
    }
next_wp:
    wp2 = size-1;
    while(wp2 > wp1) {
	switch(literal_value(cp->lit[wp2])) {
	case FALSE: break;
	case TRUE:  goto dead;
	case UNDEF: goto done_wp;
	}
	wp2--;
    }
done_wp:
    if (wp1+1 == wp2) {
	// FIXME propagate! put on queue? 
    }
    add_wlink(cp, 0, wp1);       // watch literal 1
    add_wlink(cp, 1, wp2);       // watch literal 2    

dead:
    return cp;
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

void init_sat(sat_t* sat)
{
    memset(sat, 0, sizeof(sat_t));

    sat->cnst.name = "true";
    init_var(&sat->cnst);
    sat->cnst.value = TRUE;

    sat->cnst.next = sat->variable_list;
    sat->variable_list = &sat->cnst;
}

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

// check watch points and update clauses
// we clear the literal watch list 
int propagate(lqueue_t* qp)
{
    literal_t* lp;
    
    while((lp = lqueue_deq(qp)) != NULL) {
	wlink_t* wl = lp->wlist;

	printf("deq: "); print_literal(stdout, lp); printf("\n");
	
	lp->wlist = NULL;  // wlist is cleared
	
	while(wl) {
	    wlink_t* wln = wl->next;  // save next before process
	    clause_t* cp = clause_pointer(wl);
	    long p;
	    int lv;

	    printf("eval clause:"); print_clause(stdout, cp);
	
	    if (wlink_index(wl)==0) {  // move forward
		p = cp->wl[0].p+1;
		while((p <= cp->wl[1].p) &&
		      ((lv=literal_value(cp->lit[p])) == FALSE))
		    p++;
		if (p > cp->wl[1].p) // all false (fixme wlist!?)
		    return UNSAT;
		if (lv == UNDEF) {
		    if (p == cp->wl[1].p) { // unit propagation
			literal_t* lq = cp->lit[p];
			set_literal(cp->lit[p], TRUE);
			lqueue_enq(qp, lq);
		    }
		    else {
			add_wlink(cp, 0, p);
		    }
		}
		else {
		    clear_wlink(cp, 0);
		}
	    }
	    else { // move backward
		p = cp->wl[1].p;
		while((p >= cp->wl[0].p) &&
		      ((lv=literal_value(cp->lit[p])) == FALSE))
		    p--;
		if (p < cp->wl[0].p) // all false
		    return UNSAT;
		if (lv == UNDEF) {
		    if (p == cp->wl[0].p) { // unit propagation
			literal_t* lq = cp->lit[p];
			set_literal(cp->lit[p], TRUE);
			lqueue_enq(qp, lq);
		    }
		    else {
			add_wlink(cp, 1, p);
		    }
		}
		else {  // dead, no need to touch?
		    clear_wlink(cp, 1);
		}
	    }
	    wl = wln;
	}
    }
    return OK;
}

int set_variable(variable_t* xp, int value)
{
    lqueue_t q;
    
    if (xp->value) {
	if (xp->value != value)
	    return UNSAT;  // UNSAT
	return OK;
    }
    if (value == FALSE) {
	xp->value = value;
	lqueue_init(&q);
	lqueue_enq(&q, &xp->lit[0]);
	return propagate(&q);
    }
    else if (value == TRUE) {
	xp->value = value;
	lqueue_init(&q);
	lqueue_enq(&q, &xp->lit[1]);
	return propagate(&q);
    }
    return ERROR;  // bad value?
}

int set(sat_t* sat, char* name, int value)
{
    literal_t* lp = literal(sat, name);
    if (lp->sign < 0)
	return set_variable(lp->var, -value);
    else
	return set_variable(lp->var, value);
}



int main(int argc, char** argv)
{
    sat_t sat;
    clause_t* cp;
    variable_t* vp;
    literal_t* lp;
    wlink_t* wl;

    init_sat(&sat);

    clause(&sat, 2, "a", "b");
    clause(&sat, 2, "!b", "c");
    clause(&sat, 2, "!c", "d");
    clause(&sat, 4, "!b", "!c", "e", "!d");

    set(&sat, "a", FALSE);

    for (cp = sat.clause_list; cp != NULL; cp = cp->next)
	print_clause(stdout, cp);

    for (vp = sat.variable_list; vp != NULL; vp = vp->next) {
	int i;
	printf("%s value = %d\n", vp->name, vp->value);
	for (i = 0; i < 2; i++) {
	    int wi;
	    lp = &vp->lit[i];
	    print_literal(stdout, lp);
	    printf("= {");
	    if ((wl = lp->wlist) != NULL) {
		cp = clause_pointer(wl);
		wi = wlink_index(wl);
		printf("%ld:%ld", cp->id, cp->wl[wi].p);
		wl = wl->next;
	    }
	    while(wl) {
		cp = clause_pointer(wl);
		wi = wlink_index(wl);
		printf(",%ld:%ld", cp->id, cp->wl[wi].p);
		wl = wl->next;
	    }
	    printf("}\n");
	}
    }
    exit(0);
}
