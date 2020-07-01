/* EXTRA NIF Functions */

#include <stdio.h>
#include "erl_nif.h"
#include "xnif_funcs.h"
ERL_NIF_TERM ATOM_TRUE;
ERL_NIF_TERM ATOM_FALSE;

void xnif_init(ErlNifEnv* env)
{
    ATOM_TRUE = enif_make_atom(env, "true");
    ATOM_FALSE = enif_make_atom(env, "false");
}

int enif_is_true(ErlNifEnv* env, ERL_NIF_TERM term)
{
    (void) env;
    return (term == ATOM_TRUE);
}

int enif_is_false(ErlNifEnv* env, ERL_NIF_TERM term)
{
    (void) env;
    return (term == ATOM_FALSE);
}

int enif_is_boolean(ErlNifEnv* env, ERL_NIF_TERM term)
{
    (void) env;
    return enif_is_true(env,term) || enif_is_false(env, term);
}

int enif_get_boolean(ErlNifEnv* env, ERL_NIF_TERM term, bool_t* bool)
{
    (void) env;
    if (enif_is_true(env, term))
	*bool = true;
    else if (enif_is_false(env, term))
	*bool = false;
    else
	return 0;
    return 1;
}

ERL_NIF_TERM enif_make_boolean(ErlNifEnv* env, int value)
{
    (void) env;
    return value ? ATOM_TRUE : ATOM_FALSE;
}

int enif_get_number(ErlNifEnv* env,ERL_NIF_TERM arg,double* dp)
{
    if (!enif_get_double(env, arg, dp)) {
	int i;
	if (!enif_get_int(env, arg, &i))
	    return 0;
	*dp = (double) i;
    }
    return 1;
}

int enif_print(FILE* out, ERL_NIF_TERM term)
{
    return enif_fprintf(out, "%T", term);
}

int enif_get_list(ErlNifEnv* env, ERL_NIF_TERM list,
		  int* lenp, ERL_NIF_TERM* elem)
{
    int len;
    if (!enif_get_list_length(env, list, &len)) {
	*lenp = -1;
	return 0;
    }
    if (elem == NULL) {
	*lenp = len;
	return 1;
    }
    else if (*lenp < len) {
	*lenp = len;
	return 0;
    }
    else {
	ERL_NIF_TERM tail;
	int i;
	for (i = 0; i < len; i++) {
	    enif_get_list_cell(env, list, &elem[i], &tail);
	    list = tail;
	}
	*lenp = len;
	return 1;
    }
}
