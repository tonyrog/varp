#ifndef __XNIF_FUNCS_H__
#define __XNIF_FUNCS_H__

#include <stdint.h>

#define false 0
#define true  1
typedef uint8_t bool_t;

extern void xnif_init(ErlNifEnv* env);

extern int enif_is_true(ErlNifEnv* env, ERL_NIF_TERM term);
extern int enif_is_false(ErlNifEnv* env, ERL_NIF_TERM term);
extern int enif_is_undefined(ErlNifEnv* env, ERL_NIF_TERM term);
extern int enif_is_boolean(ErlNifEnv* env, ERL_NIF_TERM term);
extern int enif_get_boolean(ErlNifEnv* env, ERL_NIF_TERM term, bool_t* bool);
extern ERL_NIF_TERM enif_make_boolean(ErlNifEnv* env, int value);
extern ERL_NIF_TERM enif_make_undefined(ErlNifEnv* env);
extern ERL_NIF_TERM enif_make_ok(ErlNifEnv* env);
extern int enif_get_number(ErlNifEnv* env,ERL_NIF_TERM arg,double* dp);
extern int enif_print(FILE* out, ERL_NIF_TERM term);
extern int enif_get_list(ErlNifEnv* env, ERL_NIF_TERM list,
			 int* lenp, ERL_NIF_TERM* elem);

#endif
