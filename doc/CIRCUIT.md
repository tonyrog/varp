# Circuits

A `circuit` is a named, reusable block of assignments.  It is a *closed
module*: the only names it shares with its surroundings are its formal
parameters, `define` macros and the names of other circuits.

    circuit <name> ( <params> ) { <body> }

## Parameters

Parameters are grouped with `;` and listed with `,`:

    circuit adder(in y, z; in ci; return x; out co) { ... }

| group    | meaning                                                    |
|----------|------------------------------------------------------------|
| `in`     | the value of the argument is read by the body (default)    |
| `out`    | the body assigns to the caller's variable                  |
| `return` | at most one, its value is the value of the call            |

A parameter may be typed and sized, and may have a default value:

    circuit plus(in Y:4, Z:4 = 3; return X:4) { X = Y+Z; }

Without an explicit `in`/`out`/`return` keyword a group is `in`.

## Sizes of parameters

A parameter size may be a meta variable, `in a:n`, and then it is
unified with the width of the argument: the first argument binds `n`,
later ones must agree, and the argument may be a declared vector, an
expression or a constant (`addn(A + 1, B, ...)`, `addn(5, B, ...)`).
Different parameters may have different size variables, `a:n, b:m`,
and the body can use them in sizes and ranges, `return s:(max(n,m))`,
`[A i=0..(n-1)]`, and as values, `x = n;`, `(i < n) ? a[i] : a[n-1]`,
the way `A * B == n` works at the top level.  A meta variable of the
caller (`-m k=5`) is a value in the body too; a `declare` or `define`
of the same name in the body shadows it.  A bit read past the end of a
vector, `a[i]` with `i >= n`, is false, so an adder written this way
adds operands of any two widths.  `a:n, b:n`
with a 3 and a 4 bit argument is an error.

## Meta parameters and arrays

A parameter in the `meta` group is an integer at build time, not a
signal: an index, a shift count, a width.  The argument is evaluated
like a quantifier bound (a constant, a meta variable, an expression of
them) and the name is bound in the body the way `n` from the command
line is:

    define K = [7, 12, 17, 22];          // an array, indexed at build time
    circuit round(meta i; in x:32; return r:32)
    {
        r = (x + K[i]) <<< K[i];
    }
    [A i=0..3] Y(i) = round(i, X(i));

`define K = [..]` is an array; `K[i]` is its element `i` (0 based,
out of range is an error) and the elements may be formulas as well as
constants, `define F = [p, q, r];`.  A `define` may also stand in a
circuit body, where it is a macro of the instance: `define HW = [a,
b, c, d];` over the locals.  Quantifier variables in a body are
integers and are not renamed, so `[A i=0..15] stir(i, WORD(i), ...)`
passes the round number on.

`formulas/varp/md5.varp` is the worked example: the 64 round
constants and rotations are arrays, the round circuit takes the round
number as a meta parameter, `md5(in X:512; return digest:128)` is 64
quantified calls, and the message comes from an input module
(`input md5_io;`), a `.txt` file on the command line that md5_io pads
into the words `M(0..15)`; the output module prints a model's digest
as md5sum does:

    varp sat bj formulas/varp/md5.varp formulas/varp/fox.txt
    9e107d9d372bb6826bd81d3542a419d6

The message may also be the binding `msg=...`, and it is a pattern:
`*` is a byte the solver may choose.  The digest can be given the
same way as a hex pattern, so the questions run both ways:

    varp sat bj msg='hello*world' digest=5eb63bbbe01eeed093cb22bb8f5acdc3 md5.varp
    5eb63bbbe01eeed093cb22bb8f5acdc3
    msg="hello world"

    varp --partial sat bj --timeout 1 mlen=11 digest='5eb63bbbe01eeed0****************' md5.varp
    5eb63bbbe01eeed0****************
    msg="***********"

The first finds the missing byte; the second is a preimage question
that a SAT solver will not answer, and with `--partial` a timed out
run prints what it knows.  `src/varp_pattern.erl` parses the patterns
and formats partial vectors, for any input module to use.  An input
module's result may bind meta variables as well (md5_io binds
`mlen`, the message length).

## Calls

A circuit is called wherever a logic expression is allowed.  The
scanner recognises the name as a circuit (`cname`) because
`varp_formula:is_circuit_def/2` is consulted while scanning, so a
circuit must be *defined before it is used* in the text.

    S = half_adder(A, B, C);        % positional
    S = half_adder(A, b = B, C);    % named
    Y = and3(A, B);                 % a3 takes its default

Positional arguments fill `in`+`out` parameters from the left, in
declaration order.  Named arguments (`name = expr`) bind by parameter
name, and a parameter with a default may be left out.  Mixing the two
is allowed as long as they do not collide.

The value of the call is the value of the `return` parameter, or `true`
when the circuit has no return parameter.

Each argument is built exactly once and then substituted into the body
as a value, so an `out` parameter really does constrain the caller's
variable:

    circuit half_adder(in y, z; return x; out co)
    {
        x  = y xor z;
        co = y and z;
    }

    S = half_adder(A, B, C);   % S = A xor B,  C = A and B

If a parameter is typed and the corresponding argument is a plain,
not yet declared, symbol then the argument is declared with the
parameter's type and size.  `R = plus(A, B);` therefore gives `A` and
`B` four bits without a separate `declare`.

## Scope

Every name in the body is local to the *instance*.  Locals are given
the symbol prefix `<name>#<seq>.`, so two instances of the same circuit
never share internal variables, and the locals are visible in models:

    1: A1,B1,C1,full_adder#2.s1

Names that are not localised:

  * the formal parameters, replaced by the argument values
  * anything that matches a `define` macro
  * circuit names, including circuits nested inside the body

`declare` inside a body creates a local, sized, variable.  A nested
`circuit` definition is visible for the rest of the enclosing body and
disappears with it.

    circuit mix(in a, b, c; return x; out t)
    {
        circuit c1(in y, z; return x) { x = y xor z; }
        t = c1(a, b);
        x = and3(t, c);
    }

## Statements

A body may contain

    declare <decls> ;          a local, sized, variable
    circuit <name> (...) {...} a nested circuit
    <lvalue> = <expr> ;        an assignment
    <formula> ;                a constraint, it must hold

The constraint form is what lets a body describe a structure of any
width: the quantifier is the loop, and the width comes in as a meta
variable.  An n bit ripple carry adder written in varp:

    declare A:n, B:n, S:n, C:(n+1);

    circuit rca(in Y:n, Z:n; out CO:(n+1); return X:n)
    {
        !CO[0];
        [A i=0..n-1] ( (X[i]    <-> (Y[i] xor Z[i] xor CO[i])) and
                       (CO[i+1] <-> ((Y[i] and Z[i]) or
                                     (CO[i] and (Y[i] xor Z[i])))) );
    }

    S = rca(A, B, C);

Run it with `n=8` on the command line.  Bit indexed assignment
(`CO[0] = false;`) works too, when a fixed width is what you want.

Because a circuit is an ordinary formula, varp can check one against
another.  This is a tautology, for every width:

    T = A + B;
    (S == T[0:n-1]) && (C[n] == T[n])

    $ varp p bj verify_rca.varp n=8
    % TRUE

## Generating structures

An assignment may be quantified: `[A i=0..n-1] s[i] = fa(...);` is
the statement for every index, and that is how a circuit of any width
is built from a fixed one, the "generate" of hardware languages:

    circuit fa(in a, b, ci; return s; out co)
    {
        s  = a ^ b ^ ci;
        co = (a && b) || (ci && (a ^ b));
    }

    circuit rca(in a:n, b:n, ci; return s:n; out co)
    {
        declare RC:(n+1);
        RC[0] = ci;
        [A i=0..n-1]
            s[i] = fa(a[i], b[i], RC[i], RC[i+1]);
        co = RC[n];
    }

The bits of a vector are read and assigned with `a[i]`, also as `out`
arguments, so the carry chain is a vector `RC` of `n+1` bits and
`RC[i+1]` of one full adder feeds the next.  A quantified assignment
is the constraint "target equals value" for every index; the target
is anything an assignment accepts.  Quantifiers nest and may bind
several indices: `[A i=0..1] [A j=0..2] M(i,j) = i + 2*j;` and
`[A i=0..n-1, j=0..m-1] ...`.  The same works at the file level, and
a quantified plain call, `[A i=0..n-1] fa(a[i], b[i], C(i), S(i),
C(i+1));`, instantiates a circuit without a return value.
`formulas/varp/rca_gen.varp` and `addn.varp` are whole examples and
`rca_gen_proof.varp` proves the generated adder equal to the built in
`+`.

## The library

`lib/default/` holds the arithmetic and comparison operators written
in varp, one circuit per file named after the circuit, and a circuit
is loaded the first time its name is used:

    declare X:4, Y:4, Z:8;
    Z == op_mul(X, Y) && op_lt(Y, X)

| circuit                   | built in         | result width          |
|---------------------------|------------------|-----------------------|
| `op_add(a:n, b:m)`        | `a + b`          | `max(n,m)+1`, carry on top |
| `op_sub(a:n, b:m)`        | `a - b`          | `max(n,m)`, modulo    |
| `op_neg(a:n)`             | `0 - a`          | `n`                   |
| `op_mul(a:n, b:m)`        | `a * b`          | `n+m`                 |
| `op_sadd(a:n/signed, b:m/signed)` | `a + b` signed | `max(n,m)+1` signed |
| `op_ssub(a:n/signed, b:m/signed)` | `a - b` signed | `max(n,m)+1` signed |
| `op_smul(a:n/signed, b:m/signed)` | `a * b` signed | `n+m` signed        |
| `op_div(a:n, b:m; out r:m)` | `a / b`, `a % b` | `n`, remainder in `r` |
| `op_rem(a:n, b:m)`        | `a % b`          | `m`                   |
| `op_sdiv(a:n/signed, b:m/signed; out r:m/signed)` | `a / b`, `a % b` signed | `n+1` signed, remainder in `r` |
| `op_srem(a:n/signed, b:m/signed)` | `a % b` signed | `m` signed           |
| `op_lt op_lte op_gt op_gte op_eq op_neq` | `< <= > >= == !=` | boolean |
| `op_slt op_slte op_sgt op_sgte op_seq op_sneq` | `< <= > >= == !=` signed | boolean |
| `op_min op_max`           | `min max`        | `max(n,m)`            |
| `op_band op_bor op_bxor op_bnot` | `& \| ^ ~`  | `max(n,m)`, `n`       |
| `op_smin op_smax(a:n/signed, b:m/signed)` | `min max` signed | `max(n,m)` signed |
| `op_sneg(a:n/signed)`     | `0 - a` signed   | `n+1` signed          |
| `op_shl(meta k; a:n)`     | `a << k`         | `n+k`, wiring         |
| `op_shr(meta k; a:n)`     | `a >> k`         | `n`, zeros in         |
| `op_sar(meta k; a:n/signed)` | `a >> k` signed | `n` signed, sign in |

Unsigned except the `op_s*` circuits; a narrower operand is zero
extended.  The signed circuits sign extend their operands first:
`op_sadd` and `op_ssub` to `max(n,m)+1` bits, where every sum and
difference fits, and `op_smul` to `n+m` bits, since two's complement
multiplication is unsigned multiplication of the sign extended
operands modulo `2^(n+m)`, so the body is `p = op_mul(A, B);` with the
assignment cutting the product to the width of `p`.  `op_slt` sign
extends to `max(n,m)` bits, inverts the two sign bits and compares
with `op_lt`; `op_seq` sign extends and compares the bits, so
`-1:3 == -1:5`.  `op_full_adder` is the cell the adders are built from,
`op_mul` adds partial products with `op_add`, `op_div` is restoring
division with `op_gte` and `op_sub`.  `op_sdiv` takes the magnitudes
with `op_neg`, divides them with `op_div` and puts the signs back:
the quotient is negative when the signs differ and the remainder has
the sign of the dividend, which is what the built in `/` and `%` do
with a signed operand (truncation toward zero, as in C).  A parameter
or return declared `:n/signed` is a signed vector to the caller, and
the body reads its bits with `a[i]` like any other.  `test/varp_lib_tests.erl` runs the value tests of the
built in operators against the library and proves, with `prove`, that
every circuit agrees with its operator for all inputs of widths 2 to
4.

Importing: `import op_add;` (a name, looked up as `op_add.varp` in
the directories of `--lib`, default `lib/default` of the
installation) or `import "dir/file.varp";` parses the file once and
its circuits, with the ones it imports in turn, join the file's
definitions.  An unknown circuit name is imported the same way
without a statement, so `op_mul(X, Y)` just works; the statement is
for files that want to say what they depend on.  A circuit the file
defines itself shadows the library's.  Another encoding is another
directory with the same names, `varp --lib lib/fast ...`.

## The library in place of the operators

`varp --ops lib ...` builds every arithmetic and comparison operator
of the formula from the library instead of the encoders in
`varp_arith.erl`: `X + Y` becomes `op_add(X, Y)`, and with a signed
operand `op_sadd` with the unsigned operand widened by a zero sign
bit, as the encoders do.  The table says which circuit serves which
operator; `-` and unary `-` always take `op_ssub` and `op_sneg`,
since the encoders give a signed result for those, `<<` and `>>` take
`op_shl`, `op_shr` or `op_sar` with the constant shift count as the
meta parameter, and `/` passes a fresh symbol of the caller for the
remainder.  Division by zero gets the `--divz` status like the
encoders; `--carry`, `--borrow` and `--overflow` are not reproduced.
Rotation, the bitwise operators on signed operands and the `=` test
stay built in.  A circuit the file defines itself shadows the
library's under `--ops lib` as well, so a formula can carry its own
`op_add`.  `varp_lib_tests:ops_lib_test_` checks that every model of
a formula is the same whichever way the operators are built.

The encoders stay as the reference implementation and the default.
Another encoding is another library directory with the same circuit
names: `varp --lib lib/fast --ops lib ...`.

## Errors

| error                                       | cause                              |
|---------------------------------------------|------------------------------------|
| `{circuit_undefined, Name}`                 | no such circuit                    |
| `{circuit_arity, Name, Given, Expected}`    | too many positional arguments      |
| `{circuit_missing_argument, Name, Param}`   | no argument and no default         |
| `{circuit_unknown_argument, Name, [Param]}` | named argument that is not a param |
| `{circuit_duplicate_argument, Name, Param}` | bound positionally and by name     |
| `{circuit_multiple_return, Name}`           | more than one `return` group       |

A constraint in a body that cannot hold makes the whole formula false,
the same way a contradiction inside the formula does.

## Implementation

`varp_formula:build_circuit/3` does the work:

1.  `circuit_params/2` splits the parameter list into `{In, Out, Return}`.
2.  `circuit_bind/4` matches the arguments to the parameters and builds
    each argument once.
3.  `circuit_prefix/2` allocates the instance prefix from the `cseq`
    counter in `#bs{}`.
4.  `circuit_rename/4` rewrites the body: parameters become `{value,V}`
    nodes, other names get the prefix.
5.  `build_circuit_body/2` runs the body statements in order, asserting
    any bare formula with `assert_formula/2`.
6.  `circuit_value/2` reads the return parameter.

The `{value,V}` node is an escape hatch in `bld/3` for an
already built value.

---

# Shift left

X << S

Can be coded as

S' = S & (1 << bitsize(X)-1)  // reduce shift size
X << S'

T == X*( ((S==k)<<k) + ... ((S==2)<<2)+((S==1)<<1)+(S==0))

could write (more efficient?)

T == maskl(X,(S==k),k) | ... | maskl(X,(S==2),2) |
     maskl(X,(S==1),1) | maskl(X,(S==0),0)

maskl(Y,bool,shift) ==
example bool=b, shift=4, bitsize(y)=5
  ( (bbbbb) 0000 ) & ( (yyyyy) 0000 )

example bool=c, shift=3, bitsize(y)=5
  ( ((ccccc)&(yyyyy)) 000 )
