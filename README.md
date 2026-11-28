Varp
====

Varp is a theorem prover for propositional logic with a language on top
of it. Besides the usual connectives it has quantifiers over finite
domains, two's complement integer arithmetic, bit vectors and reusable
circuits, all of which are compiled down to CNF and handed to a SAT
engine written in C.

    [A p=1..n] [E h=1..(n-1)] P(p,h)          quantifiers
    declare X:8/signed;  (X * Y == 15)        arithmetic
    circuit rca(in Y:n, Z:n; return X:n) {}   circuits

The solver is a NIF (`c_src/varp_nif.c`); everything above it -- scanner,
parser, formula builder, arithmetic encodings and the search plugins --
is Erlang.

Build
-----

Needs Erlang/OTP (with `wx` for the GUI) and a C compiler.

    make            # src + c_src
    make test       # build and run the eunit suites
    make test-gui   # the same, and start the gui window under Xvfb

To run it from anywhere, put a symlink to `priv/varp.sh` on your PATH.
The script finds its own `ebin` relative to itself, so the repository
can live wherever you like:

    ln -s $PWD/priv/varp.sh ~/bin/varp
    ln -s $PWD/priv/varp_gui.sh ~/bin/varp-gui

Quick start
-----------

    $ varp -f "A && !A" sat bj
    % 0

    $ varp -f "(A -> B) and (B -> C) -> (A -> C)" p bj
    % TRUE

    $ varp -f "A || B || C" sat bt --max 0
    1: A,B,C
    2: A,B
    ...
    % 7

    $ varp sat bj formulas/varp/send_more.varp
    1: D=7,E=5,M=1,N=6,O=0,R=8,S=9,Y=2
    % 1

    $ varp sat bj formulas/varp/pigeon.varp n=5
    % 0

Command line
------------

    varp [global options] [<plugin> [plugin options]]* [bindings] [files]

**The order matters.** An option is parsed against the option spec of
whatever comes before it, so global options go *before* the first
plugin name and a plugin's own options go *after* it:

    varp --timeout 30 sat bt --max 0 formulas/varp/eq4.varp
         └ global ──┘ └────┘ └──────┘

`-f "A && B" sat bj` works, `sat bj -f "A && B"` does not: by then
`-f` is being looked up among `backjump`'s options.

Options take their value as the next argument or after `=`
(`--max 0`, `--max=0`, `-n 0`).

### Result

Varp prints one line per model and a summary line:

| output    | meaning                                          |
|-----------|--------------------------------------------------|
| `% N`     | N models found                                   |
| `% 0`     | unsatisfiable                                    |
| `% TRUE`  | with `p`/`prove`: the formula is a tautology     |
| `% FALSE` | with `p`/`prove`: a counter model exists         |

The exit status is 0, or 1 on an error. With `--starexec=true` an
unsatisfiable instance prints `s UNSATISFIABLE` and exits 20.

### Bindings

    <var> = <value>

A lowercase name on the command line becomes a *meta* variable, usable
in quantifier domains, in declared sizes and as a predicate index:

    $ varp sat bj formulas/varp/die_hard.varp n=6

The value is an integer, or a float (`limit=4.0`, `eps=1e-6`) that
meets a fixed or floating point operand like a literal in the formula.

### Plugins

A plugin is named by its long or its short name. They run in the order
given, each one seeing the state the previous one left behind.

| short      | long         | what it does                                      |
|------------|--------------|---------------------------------------------------|
| `sat`      | `satisfy`    | bind the formula to true                          |
| `unsat`    | `falsify`    | bind the formula to false                         |
| `p`        | `prove`      | bind to false, an inconsistency proves the formula |
| `bt`       | `backtrack`  | plain backtracking search                         |
| `bj`       | `backjump`   | CDCL with clause learning and restarts            |
| `ord`      | `order`      | choose the variable order                         |
| `par`      | `parallel`   | run the rest of the chain in cloned instances     |
| `s`        | `saturate`   | saturation / lookahead preprocessing              |
| `so`       | `satord`     | pick an order by sampling models                  |
| `red`      | `reduction`  | add reduced clauses                               |
| `rat`      | `rat`        | remove RAT clauses                                |
| `cnf`      | `cnf`        | write the built formula out as DIMACS or SNF      |
| `succ`     | `succ`       | successor encoding output                         |
| `validate` | `validate`   | check a proof log                                 |
| `mon`      | `monitor`    | live counters                                     |
| `clean`    | `clean`      | remove dead clauses                               |
| `dbg`      | `debug`      | dump internals                                    |
| `wx`       | `wx`         | the GUI                                           |

`satisfy`, `falsify` and `prove` only *set* the goal; they do not
search. Follow one with `bt` or `bj`:

    varp sat bj file.varp        # find one model
    varp sat bt --max 0 file.varp # enumerate all of them

### Global options

`varp --help` prints the current list; the ones you reach for most:

    --formula, -f <string>     formula on the command line (repeatable)
    --print, -p <how>          false|literal|erlang|model|dimacs   (model)
                               false suppresses the summary line too;
                               literal prints false literals as well and
                               a substituted Y whose representative X has
                               no value as Y=X (or Y=!X)
    --method <how>             collect|count                       (collect)
    --timeout, -t <seconds>    float|infinity                      (infinity)
    --log <level>              debug|info|...|none                 (none)
    --undeclared <when>        none|typo|once|all                  (typo)
    --icase, -i <bool>         case insensitive keywords/variables (false)
    --gui <bool>               start the GUI                       (false)
    --starexec <bool>          report in starexec format           (false)
    --statistics <bool>        show counters                       (false)
    --version, -V              print the version
    --help, -h[=<plugin>]      this, or a plugin's options
    --lib <dir>                circuit library, <name>.varp loaded on use
    --hex                      print unsigned vector values in hex
    --check                    parse and build only; an undeclared symbol
                               is an error with its line (and a guess)
                               (lib/default: op_add, op_mul, op_lt, ...)

Encoding and search behaviour:

    --adder plain|fast                  style of adder            (plain)
    --ops builtin|lib                   operators (also <<< >>>) from the circuit library (builtin)
    --locals <bool>                     show circuit locals in models (false)
    --assoc left|right|balanced|none    how all/any are built     (none)
    --carry, --borrow, --overflow       true|false|ignore         (ignore)
    --divz true|false|ignore            divide by zero            (false)
    --fixpoint <bits>                   fraction bits of a bare /fixpoint
                                        and of a float literal         (16)
    --float <format>                    what a /float declaration is:
                                        float754, 32/float754, 32/float754(23),
                                        float754(8,23), fixpoint, 32/fixpoint(8),
                                        fixpoint(16,16)         (float754)
    --inf true|false|ignore             a float754 result that overflows (ignore)
    --nan true|false|ignore             a float754 result that is NaN  (ignore)
    --underflow true|false|ignore       a float754 result that is tiny
                                        and inexact                  (ignore)
    --ftz <bool>                        flush a tiny float754 result to
                                        zero instead of a subnormal  (false)
    --fdivz true|false|ignore           float754 division by zero       (false)

`X << K` and `X >> K` with a constant `K` widen or narrow the vector;
with a variable `K` they are a barrel shifter that keeps the width of
`X` (the bits that leave are gone, an amount of the width or more gives
zero, or the sign for a signed `>>`), and `K` is read as unsigned.  A
constant has only the bits its value needs, so `1 << K` gets the bits
`K` can reach, at most 64, and `Z = X << K;` widens `X` to `Z` first,
as C promotes before it shifts.

`/` and `%` are unsigned when both operands are unsigned, otherwise
signed with truncation toward zero as in C: `-13 / 4 == -3` and
`-13 % 4 == -1`, so `X == (X / Y) * Y + X % Y` always holds and the
remainder has the sign of the dividend.  With `--divz false`, the
default, a division by zero has no model.  `+`, `-` and `*` are signed
in the same way as soon as one operand is; the statement form
`Z = X * Y;` keeps the width of `Z`, the low bits of a wide product or
the product sign extended.

Arithmetic is exact otherwise: `X + Y` of two 32 bit values is 33 bits
wide, and `Z == X + Y` with a 32 bit `Z` has no model when the sum
does not fit, so a run that overflows simply ends.  `wrap(E, T)` is
the C cast: the low bits of `E` read as the type `T`, two's complement,
what a store into a `T` sized memory cell keeps.

    declare X:8/signed, Y:8/unsigned;
    wrap(X + X, 8/signed) == -56 && X == 100      # 200 wraps to -56
    Y == wrap(X, 8/unsigned) && X == -3           # 253
    Y = wrap(X + X);                               # the destination says the type
    Y == wrap(X + X)                               # so does the other side of ==

`T` is what a declaration says after the name: `32/unsigned`,
`8/signed`, `32/fixpoint`, `16/fixpoint(4)`, `fixpoint(8,8)`,
`32/float`.  A shorter value is extended first (the sign of a signed
one).  `fits(E, T)` is the overflow `wrap` hides: true when the exact
value of `E` is representable in `T`, so `fits(X + X, 8/signed)` holds
for `X == 60` and fails for `X == 64`; `invariant fits(..)` proves a
system never wraps, `assume fits(..)` keeps the runs that do not.
Both are gates over the bits, no arithmetic.  `wrap` to `float754` is an
error (the bits of an integer are no float); a fixed point or float
value into an integer type needs `floor`, `ceil`, `round` or `trunc`
first, as an assignment does.

`cast(E, T)` is the third form: the same bits read as another type of
the same width, no logic at all, what memory does when a float is
stored and read back as bytes.  `E/unsigned`, `E/signed` and `E/float`
are `cast(E, T)` at the width of `E`; `cast(E)` takes the type from
the destination like `wrap(E)`.  Any type goes, `float754` included,
and a constant has the bits of its width:

    declare F:32/float754, U:32, Q:32/fixpoint;
    F == 1.5 && U == F/unsigned                   # U == 0x3FC00000
    F == cast(0xC0490FDB, 32/float754)            # F == -3.1415927
    isnan(F) && F/unsigned == 0x7FC00000          # the quiet NaN pattern
    Q == 1.5 && U == cast(Q, 32/unsigned)         # U == 0x18000, the raw Q16.16
    U == cast(Q)                                  # the same, typed by U

The widths must agree, `cast(X:16, 32/float754)` is an error (`wrap`
cuts or extends); a float literal has no bits until it has a type.

`X + 0`, `X - 0`, `X * 1` are `X`, `X * 0` is `0` and `X * 2^n` is
`X << n`: no adder or multiplier is built for them.

A bitwise operator with a constant costs nothing: `X & 0xFF`,
`X | 0`, `X ^ ~0` and the field extraction `(X & 0xFFFF0000) | (X & 0xFFFF)`
are wiring, the constant bits fold in the gates.  `&`, `|` and `^` bind
looser than `==` (as in C), so `Y == X & M` is `(Y == X) & M`, a vector
where a formula is expected and an error: write `Y == (X & M)`.

### Fixed point

A fixed point variable is a two's complement integer read as
`value / 2^F`:

    declare X:32/fixpoint;        # Q16.16: 16 integer bits, 16 fraction bits
    declare Y:16/fixpoint(4);     # 16 bits of which 4 are fraction
    declare Z/fixpoint(8,8);      # 8 integer bits and 8 fraction bits
    X == 1.5 && Y < X / 3 && Z == floor(X) + 0.25

The fraction width of a bare `/fixpoint` is `--fixpoint`, 16 by default.
A float literal (`1.5`, `2.5e3`, `1e2`) is a fixed point constant with
the fraction width of the operand it meets, or `--fixpoint` when it
meets an integer, so `X * 1.0 / Y` divides two integers in Q16.16.  An
integer operand is converted exactly, two fixed point operands of
different widths meet at the wider fraction.  The arithmetic is exact,
`X + X` of two Q16.16 values is 33 bits, so `next(X) == X + X` in a
system has no successor once the sum leaves 32 bits; `wrap(X + X)`
(or `wrap(X + X, 32/fixpoint)`) keeps the low 32 raw bits as a C
`int32_t` store does, `20000.0 + 20000.0` wraps to `-25536.0`, and
`fits(X + X, 32/fixpoint)` tells whether the exact sum would have fit.
An integer wrapped into a fixed point type is scaled first, so
`wrap(-3, 16/fixpoint(4))` is `-3.0`.  `+ - min max % < == ...`
work on the scaled integers, `*` drops the low F bits of the product
(floor), `/` is `(a << F) / b` truncating toward zero like the signed
integer division, and `& | ^ << >>` act on the raw bits.  `floor(X)`,
`ceil(X)`, `round(X)` (half up) and `trunc(X)` (toward zero) give an
integer; assigning a fixed point value to an integer variable without
one of them is an error.  `sqrt(X)` is the root rounded down with the
same fraction width (an integer operand gets `--fixpoint`), a negative
operand has no model; `sqrt(2)` of a constant is the meta function, a
literal.  A model prints the value as a decimal number,
exact (`X=-1.5`, `Y=0.0625`), `--hex` the raw bits; the trace of `bmc`
does the same (`formulas/varp/tank_system.varp`).  Everything is built
from the integer operators, so `--ops lib` (`op_fixmul`, `op_fixdiv`
over `op_smul`/`op_sdiv`) and `--overflow` apply as for integers.

### Floating point, IEEE 754

    declare X:32/float754;        # binary32: 8 exponent bits, 23 fraction bits
    declare Y:16/float754;        # binary16 (5,10); 64 is binary64 (11,52)
    declare S:8/float754;         # E5M2 (5,2), the 8 bit format with IEEE rules
    declare B:16/float754(7);     # bfloat16: 7 fraction bits, 8 exponent, 1 sign
    declare Z/float754(8,23);     # explicit, 1+8+23 bits

As with `/fixpoint(4)`, one argument is the fraction width; `(E,M)`
names the exponent and fraction widths, the sign bit comes on top, so
`X:32/float754`, `X:32/float754(23)` and `X/float754(8,23)` are the
same thing.  A fixed or floating point declaration whose width is not
8, 16, 32, 64 ... gets a warning, as `(8,8)` for bfloat16 would.

Operands and results follow IEEE 754: a subnormal pattern is its
small value, inf and NaN are what they are, a result below the normal
range is rounded to a subnormal (gradual underflow) and a literal above
the range is an error.
Rounding is to nearest even.  There are the type, the literals, the
comparisons (`-0.0 == 0.0`), `-X`, `abs`, `min`, `max`, `?:`, `+ - * /`,
`sqrt(X)` (correctly rounded; `-0.0` stays, a negative number is NaN),
`fma(A, B, C)` (`A * B + C` with one rounding, so `fma(X, Y, -Z)` with
`Z == X * Y` is the exact rounding error of the product), and the
conversions: an integer or fixed point operand that meets a float
becomes a float, `floor ceil round trunc` give an integer, a float
assigned to a fixed point variable is truncated toward zero, and
assigning one to an integer variable is an error.  A result that
overflows is `inf`, with `inf` as a literal too (`X != inf`, `-inf`);
`--inf false` makes an overflow a contradiction instead, `--inf true`
demands one.  `inf - inf`, `0 * inf`, `0 / 0`, `inf / inf` and any
operation on a NaN give the quiet NaN pattern, printed `nan`, and
`--nan` says whether that may, may not or must happen; a NaN compares
unordered (`X != X` is its signature, every other comparison is false)
so `Z == X / Y` cannot bind a NaN, the statement `Z = X / Y;` can, and
`isnan(X)`, `isinf(X)` test a value.  Division by a zero of a nonzero
is `--fdivz`, the `--divz` of floats: no model by default, `ignore`
gives `inf` with the sign of the quotient.  A difference that cancels
is `+0.0`.  Two
literals fold as floats, `1.5 / 2.0` is `0.75` whatever meets it; a
literal above the range is an error.  Two float formats do not mix.
Note that `Z == X + Y` leaves the sign of a zero result open (`-0.0 ==
0.0`), the statement `Z = X + Y;` pins the bits.  A model prints the shortest
decimal that reads back as the same number (`X=0.1`, `Y=-1.5e-30`),
`--hex` the raw bits.  Like fixed point everything is built from the
integer operators, so `--ops lib` applies.

`--ops lib` builds the arithmetic and comparison operators (`+ - * / %
min max < <= > >= == != & | ^ ~ << >>`) from the circuits in the
library instead of the built in encoders, `op_add` for `X + Y`, the
`op_s*` circuits when an operand is signed, so that another encoding
is a matter of another `--lib` directory; `doc/CIRCUIT.md` has the
details.  The built in encoders stay the reference: `--carry`,
`--borrow` and `--overflow` are theirs only, `--divz` holds in both.
The locals of a circuit instance (`op_add#3.C`) are not in the symbol
table and a model does not list them; `--locals true` keeps them all,
`declare t:4 /visible;` in a body keeps one.
    --phase true|false|undefined        initial phase             (true)
    --bump-decay <f>           VSIDS activity decay per conflict; 0 keeps
                               the old order-list bump             (0.95)
    --use-phase <bool>                  phase saving              (false)
    --qtype fifo|lifo|recursive         queue type            (recursive)
    --seed <integer>                    random seed                   (0)

Proof output:

    --proof-output none|user|text|binary   (none)
    --proof-file <name>                    (proof.out)
    --outdir <dir>                         ()

`text` is readable (symbol names), `binary` is what the `validate`
plugin reads back:

    varp --proof-output binary --outdir /tmp sat bj file.varp
    varp validate -t binary -f /tmp/proof.out sat file.varp

Underflow is a result that is tiny, below the normal range before
rounding, and inexact; an exact subnormal (`2^-100 * 2^-33`) is not
one.  `--underflow false` makes it a contradiction, `true` demands it,
and a literal counts: `X == 1.0e-39` has no model under `false`, since
binary32 cannot hold it exactly.  `--ftz true` is flush to zero, what
many DSPs and NEON in its default mode do: a tiny result, literal or
converted value becomes zero (with its sign), and every tiny nonzero
result is then an underflow.  Operands are still read as IEEE does.
Under `--ops lib` the operations are the library circuits `op_fmul`,
`op_fadd`, `op_fdiv`, `op_fsqrt` and `op_ffma` (`doc/CIRCUIT.md`), with
the flags as out parameters; `varp_float754_tests:float_lib_test_` checks them
against the same references, every pair of `float754(3,2)`.

### /float: one declaration, either format

    declare X:32/float, Y/float;
    $ varp --float fixpoint sat bj f.varp          # X is Q16.16
    $ varp --float float754(8,23) sat bj f.varp    # X and Y are binary32

A `/float` declaration (also as a circuit parameter and as a typed left
hand side `X:32/float = ...`) is fixed or floating point as `--float`
says, so one formula runs in both: the format is what follows the slash
of a declaration, with the width in front when the declaration has
none (`32/float754`, `32/fixpoint(8)`; `float754(8,23)` and
`fixpoint(16,16)` carry theirs).  A declared width must agree with the
option, and a bare `X/float` needs the option to give one.  The default
is `float754`, the standard format of the declared width.

### Plugin options

`varp --help=<plugin>` prints them, and so does `-h` or `--help` right after the plugin name (`varp bj -h`). The two search plugins:

    backtrack   --max, -n <N>        models to find, 0 = all       (1)
                --timeout, -t <s>                          (infinity)

    backjump    --max, -n <N>                                      (1)
                --timeout, -t <s>                          (infinity)
                --max-learned <L>          learned clause limit    (0)
                --max-learned-factor <F>   L = F * |clauses|       (0)
                --keep-factor <P>          fraction to keep      (0.5)
                --min-keep-clauses <K>                             (0)
                --max-conflicts <N>        conflicts to analyse    (1)
                --minimize none|local|global|recursive          (none)
                --bump <N>|none|next|log2|log10|rank    VSIDS bump (1)
                                           (with --bump-decay only none matters)
                --restart-counter <N>                              (0)
                --restart-interval <s>                     (infinity)
                --restart "<step> | <step> | ..."   restart strategy
                --stumble <L>              extra jump if D1 >= L   (0)
                --olle <K>                 extra jump if D1 >= K*D2 (0)
                --stumble-olle <bool>      require both        (false)
                --display delta|histogram|bool                 (false)

with `D1` the backjump distance and `D2` the distance from the backjump
to the next level. The learned clause limit is

    MaxLearned = min(L, F*|Clauses|)   when both L and F are set
                 F*|Clauses|           when only F is set
                 L                     when only L is set
                 infinity              otherwise

and the number kept on a reduction is `max(K, P*MaxLearned)`.

A restart (the limit, the counter or the timer) pops to level 0, and
`--restart` says what to do there before the search starts over: a
chain of plugin steps with their ordinary options, separated by `|`,
taken in turn, one per restart. `skip` is a plain restart. Every
plugin is a possible step; a `saturate` step reports no models (the
search finds them), an `order` step with `random` and no `--seed`
gets a new seed every time, and a step's own `--timeout` ends the
step only. Under `parallel`, clone i takes step i first.

    varp sat bj --restart-counter 100000 \
        --restart "order --sort rank,random | saturate -k 1 -l 1 --timeout 1 | skip" f.varp

`bmc` is a driver for bounded model checking (see
[`doc/MODEL_CHECKING.md`](doc/MODEL_CHECKING.md)): it rebuilds the
formula for every bound, runs the search plugin that follows it, and
prints a counterexample as a trace, one row per step:

    bmc         --k-min <N>, --k-max <N>, --step <N>     bounds  (0, 20, 1)
                --bound <name>             the bound's meta variable  (k)
                --trace <bool>             print the trace           (true)
                --induction <bool>         prove an invariant by k-induction (false)
                --property <macro>         which property, e.g. dining_invariant
                --incremental <bool>       one clause database for all bounds (true)
                --saturate <N>             probe every new step at level N  (0)
                --saturate-friend <N>, --saturate-random <N>   wider vectors
                --saturate-laps <N>        laps per step, 0 = fixpoint   (1)
                --saturate-timeout <s>     probing time per step  (infinity)
                --keep-learned auto|<bool> keep learned clauses between bounds
                --reset-order auto|<bool>  restore the variable order per bound
                                           (auto: keep and no reset with --bump-decay)

    varp bmc formulas/varp/die_hard_system.varp
    varp bmc --bound n bj --minimize recursive formulas/varp/die_hard.varp

    parallel    --clones, -n <N>     clones of the built formula, one process
                                     each, the rest of the chain runs in every
                                     clone and the first to finish answers
                                     (default: the online schedulers)
                --seed <N>           base seed, clone i gets seed+i  (-1: the
                                     formula's)
                --shuffle <bool>     random variable order in every clone but
                                     the first                       (true)
                --share <bool>       permanent bindings and substitutions
                                     found in one clone go to all (imported
                                     at a restart of bj, between two probes
                                     of saturate) and to the original
                                     instance                        (true)
                --cubes <K>          split the search instead of repeating
                                     it: cubes over the first K variables
                                     of the order, from a queue      (0)
                --share-len <N>      learned clauses up to this length go
                                     to the other clones, imported at a
                                     restart (0: none)              (8)
                --stat <bool>        report the winner, what was shared and
                                     every clone's counters

    varp sat parallel --clones 8 --stat bj formula.varp
    varp sat parallel --clones 8 saturate -k 2 bj formula.varp
    varp --method count sat order --first A,B,C parallel --clones 8 --cubes 3 bt --max 0 f.varp

Without `--cubes` every clone searches the whole formula (a
portfolio: the clones differ in seed, order and restart step, and the
first one wins). With `--cubes K` the search is split: a cube is an
assignment of the first K unbound variables of the order that
propagation does not refute, the clones take cubes from a queue and
search under them as assumptions, and what they learn is still valid
for the whole formula, so sharing goes on. The cubes are disjoint, so
`--max 0` counts every model exactly once across the clones; with the
default `--max 1` the first model wins. A cube without models is just
the next cube, when every cube is empty the formula has no models,
and a clone that refutes the formula at level 0 ends it all at once.
The part of the chain before the search (`order`, `saturate`) runs
once in every clone. `order --first` before `parallel` picks the cube
variables.

    The first clone with a decisive answer (models, no models, an abort)
    wins. A saturate in the chain is divided: clone i probes segment i
    of the variables (by equivalence class, so a class has one owner
    whichever member stands for it), the clones share what they find
    and lap again on each other's facts until none of them has anything
    left, and then every clone goes on with the rest of the chain. With
    nothing after saturate every clone just continues, and the answer is
    the original instance with all the facts, so a monitor before
    parallel sees them all. The fixpoint of saturation with substitution
    depends on the order the facts are found in, so a divided run can end
    a few bindings off a sequential one, either way.

    The learned clauses are shared through a ring (an ETS table with a
    sequence number per clause): bj in a clone puts every learned clause
    of at most --share-len literals in it, and reads the clauses of the
    others from its own cursor at a restart, into its learned set, where
    the purge treats them as its own. Facts are the cheap and always
    useful part; clauses cost memory in every clone, so the length is
    kept short.

    order       --sort <order>[,<order>]  identity|random|degree|rank,
                                          each with an optional +, - or =:
                                          + ascending, - descending, =
                                          interleaved, the ascending order
                                          woven from both ends (1,2,3,4,5
                                          becomes 1,5,2,4,3) so the search
                                          attacks it from the top and the
                                          bottom; the second key breaks
                                          ties of the first. identity is
                                          +identity, the others are -
                --first, -f "v1,..,vn"    literals sorted first; the bare
                                          name of a predicate with arguments
                                          (Move for Move(p,q,time)) is every
                                          instance, earliest step first
                --last, -l "v1,..,vn"     literals sorted last
                --ignore-file <bool>      ignore the order section in the
                                          file; otherwise each of --sort,
                                          --first and --last given on the
                                          command line wins over the file
                --display, -d <bool>

    saturate    --level, -k <N>       saturation level             (1)
                --laps, -l <N>                                     (0)
                --threshold <N>                                    (0)
                --subst, -s <bool>    substitute equal literals (true)
                --friend, -f <N>  --seq, -q <N>  --random, -r <N>
                --timeout, -t <s>                          (infinity)
                --model <bool>        stop with a model found (true)
                --warn <bool>         warn when the main variable is
                                      unbound, no sat before  (true)
                --segment <i>, --segments <n>  probe only the vectors
                                      led by variable i, i+n, i+2n, ...
                                      (parallel gives each clone one)

    saturate probes: every vector of level + seq + friend + random
    unbound variables is propagated in all its assignments, and what
    every consistent assignment agrees on is kept (a value, or with
    --subst an equivalence Y=X). All assignments inconsistent means the
    formula is. One assignment that binds every variable is a model,
    reported at once and the run stops (--model false to just go on,
    for instance to enumerate all models with bt --max 0 after it).
    It warns when the main variable is unbound, since that is mostly
    a forgotten sat; --warn=false when the clauses alone are the point.
    It needs the main variable bound, so put sat (or
    unsat, prove) before it: with the message bits ordered first and a
    vector of one byte, the unknown byte of an md5 preimage is such a
    model:

        varp sat order --first=X saturate -k=1 -seq=7 \
             msg='hello *orld' digest=5eb63bbbe01eeed093cb22bb8f5acdc3 md5.varp

    reduction   --size, -n <N>|all                                 (0)
    rat         --type, -r both|min|pos|neg                      (min)

    cnf         --file, -f <name>     output file
                --type, -t cnf|snf                              (cnf)
                --symbols, -s <bool>  emit symbols as comments (false)
                --raw, -r <bool>|debug                        (false)

    satord      --size, -v <N>        selection vector size       (10)
                --iterations, -n <N>  samples per round         (1000)
                --rounds, -r <N>                                   (2)
                --mode, -m sat|unsat                             (sat)

Note that `satord` needs `iterations < 2^size` and enough unbound
variables, otherwise it will not terminate.

The language
------------

[`SYNTAX.md`](SYNTAX.md) is the reference; [`doc/CIRCUIT.md`](doc/CIRCUIT.md)
covers circuits, and [`doc/MODEL_CHECKING.md`](doc/MODEL_CHECKING.md)
transition systems (`system { state ... next ... reach ... }`, channels
and instances) for bounded model checking; `formulas/varp/fpga.varp` and
`fpga_adder.varp` compute lookup table configurations from a target
circuit, `md5.varp` is MD5 as a circuit (`varp sat bj md5.varp fox.txt`
prints the digest, the message file read by an input module),
circuit (bit m of the table is the target on the bits of m), and
`fpga_fabric.varp` programs a net of four cells with routing bits into a
2 bit adder. A taste:

    // n pigeons do not fit in n-1 holes
    ([A p=1..n] [E h=1..(n-1)] P(p,h)) and
    ([A h=1..(n-1)] [A p=1..n] [A q=1..n,p<q] not (P(p,h) and P(q,h)))

    // 15 = 3*5, found rather than computed
    declare X:4, Y:4;
    (X*Y == 15) && (X>1) && (Y>1) && (X<=Y)

    // a reusable half adder
    circuit half_adder(in y, z; return x; out co)
    {
        x  = y xor z;
        co = y and z;
    }
    S = half_adder(A, B, C);

Predicates spring into existence when used, so `P(1,2)` needs no
declaration. `--undeclared` warns when a name occurs once and looks
like a misspelling of one that does not:

    puzzle.varp:4: warning: 'Exampl' occurs once, did you mean 'Example'?

Input formats
-------------

Detected from the file, or from the `p` line for the DIMACS family:

| extension          | format                                 |
|--------------------|----------------------------------------|
| `.varp` and others | the varp language                      |
| `.cnf`, `.dimacs`  | DIMACS CNF                             |
| `.snf`             | symbolic normal form (named literals)  |

Several files on the command line are conjoined, as are repeated `-f`
options, so a library and the formula that uses it can be separate:

    varp sat bj lib/arith.varp puzzle.varp

With no file varp reads standard input.  A `.txt` or `.dat` file is
data for the input modules a formula declares (`input md5_io;`), line
`recno` of it, or with no file at all the bindings (`msg="hello"`);
see `src/varp_input.erl` for the module protocol.

GUI and packaging
-----------------

    varp --gui=true                # or priv/varp_gui.sh

The GUI runs the formula with Satisfy, Falsify or BMC; BMC takes the
bound from "k max", proves by k-induction when "Induction" is ticked,
and prints the verdict and the counterexample as a step table in the
model window (see doc/MODEL_CHECKING.md).

    make appimage                  # Linux AppImage (wx)
    make osxapp                    # macOS .app + .dmg
    make win32app                  # Windows

A terminal-only AppImage, and the starexec build:

    make appimage_nw
    erl -config default.config -config bj.config -s varp start0 \
        -s servator make_starexec varp

Packaging uses [servator](https://github.com/tonyrog/servator).

Tests
-----

    make test

462 eunit cases over the scanner, the grammar, formula building,
circuits, the SAT engine, the plugins, the input and output backends
and the command line. See [`test/README.md`](test/README.md); it also
explains the two xfail lists that track what the grammar does not
accept yet.

License
-------

GPL-3.0. Versions up to and including 0.9.48 were released under the
MIT license.
