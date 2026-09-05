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
                               false suppresses the summary line too
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

Encoding and search behaviour:

    --adder plain|fast                  style of adder            (plain)
    --assoc left|right|balanced|none    how all/any are built     (none)
    --carry, --borrow, --overflow       true|false|ignore         (ignore)
    --divz true|false|ignore            divide by zero            (false)
    --phase true|false|undefined        initial phase             (true)
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
                --restart-counter <N>                              (0)
                --restart-interval <s>                     (infinity)
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

    order       --sort <order>[,<order>]  identity|random|degree|rank|user,
                                          each with an optional +, - or =
                --first, -f "v1,..,vn"    literals sorted first
                --last, -l "v1,..,vn"     literals sorted last
                --display, -d <bool>

    saturate    --level, -k <N>       saturation level             (1)
                --laps, -l <N>                                     (0)
                --threshold <N>                                    (0)
                --subst, -s <bool>    substitute equal literals (true)
                --friend, -f <N>  --seq, -q <N>  --random, -r <N>
                --timeout, -t <s>                          (infinity)

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
covers circuits, and [`doc/MODEL_CHECKING.md`](doc/MODEL_CHECKING.md) is a
design note on bounded model checking. A taste:

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

With no file varp reads standard input.

GUI and packaging
-----------------

    varp --gui=true                # or priv/varp_gui.sh

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
