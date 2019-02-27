//
// Test of watched literals data structures
//
#include <stdio.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>

#define UNDEF  0
#define FALSE -1
#define TRUE   1

typedef struct _literal_t
{
    int sign;                  // -1=negative,  1=positive
    struct _variable_t* var;
    struct _watch_t* wlist;    // list of watch literal positions
} literal_t;

typedef struct _variable_t
{
    char* name;
    int  value;               // -1=false  0=unassigned  1=true
    struct _variable_t* next; // variable list
    literal_t lit[2];         // literal containers
} variable_t;

typedef struct _clause_t
{
    unsigned   id;           // clause number
    unsigned   size;         // number of literals
    struct _clause_t* next;  // clause list
    int wp1;                 // watch point 1
    int wp2;                 // watch point 2
    literal_t* lit[];        // literal array
} clause_t;

typedef struct _watch_t
{
    struct _watch_t* next;
    clause_t* clause;
} watch_t;


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

static void init_var(variable_t* vp)
{
    vp->value = 0;

    vp->lit[0].sign = 1;
    vp->lit[0].var  = vp;
    vp->lit[0].wlist = NULL;

    vp->lit[1].sign = -1;
    vp->lit[1].var  = vp;
    vp->lit[1].wlist = NULL;    
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
    watch_t* wp;
    int i, wp1, wp2;
    
    cp = malloc(sizeof(clause_t) + sizeof(literal_t*)*size);
    va_start(ap, size);
    for (i = 0; i < size; i++) {
	char* lname = va_arg(ap, char*);
	cp->lit[i] = literal(sat, lname);
    }
    va_end(ap);
    cp->id   = sat->num_clauses++;
    cp->size = size;
    cp->next = sat->clause_list;
    sat->clause_list = cp;

    cp->wp1 = -1;
    cp->wp2 = -1;

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
    cp->wp1 = wp1;
    cp->wp2 = wp2;
    if (wp1+1 == wp2) {
	// propagate!
    }

    // watch literal 1
    lp = cp->lit[wp1];
    wp = malloc(sizeof(watch_t));
    wp->clause = cp;
    wp->next = lp->wlist;
    lp->wlist = wp;

    // watch literal 2
    lp = cp->lit[wp2];
    wp = malloc(sizeof(watch_t));
    wp->clause = cp;
    wp->next = lp->wlist;
    lp->wlist = wp;
	
dead:
    return cp;
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
    fprintf(f, "{%d: ", cp->id);
    if (cp->size > 0) {
	int i;
	print_literal(f, cp->lit[0]);
	for (i = 1; i < cp->size; i++) {
	    fprintf(f, ",");
	    print_literal(f, cp->lit[i]);
	}
    }
    fprintf(f, "} wp1=%d, wp2=%d\n", cp->wp1, cp->wp2);
}

void init_sat(sat_t* sat)
{
    memset(sat, 0, sizeof(sat_t));

    sat->cnst.name = "true";
    init_var(&sat->cnst);
    sat->cnst.value = 1;

    sat->cnst.next = sat->variable_list;
    sat->variable_list = &sat->cnst;
}


int main(int argc, char** argv)
{
    sat_t sat;
    clause_t* cp;
    variable_t* vp;
    literal_t* lp;
    watch_t* wp;

    init_sat(&sat);

    clause(&sat, 4, "a", "b", "c", "d");
    clause(&sat, 2, "!a", "!c");
    clause(&sat, 2, "!b", "!d");
    clause(&sat, 2, "!a", "!d");
    clause(&sat, 5, "false", "true", "!true", "!!false", "!false");

    for (cp = sat.clause_list; cp != NULL; cp = cp->next)
	print_clause(stdout, cp);

    for (vp = sat.variable_list; vp != NULL; vp = vp->next) {
	int i;
	for (i = 0; i < 2; i++) {
	    lp = &vp->lit[i];
	    print_literal(stdout, lp);
	    printf("= {");
	    if ((wp = lp->wlist) != NULL) {
		printf("%d", wp->clause->id);
		wp = wp->next;
	    }
	    while(wp) {
		printf(",%d", wp->clause->id);
		wp = wp->next;
	    }
	    printf("}\n");
	}
    }
    
    exit(0);
}
