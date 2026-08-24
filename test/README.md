# varp test suite

EUnit suites for the parser, the formula builder, the SAT engine, the
plugins and the command line.

    make test        # from the top of the tree, builds src, c_src and test
    make test-gui    # the same, and also starts the gui window under Xvfb

To run a single suite:

    cd test && make
    erl -noshell -pa ../ebin -pa ebin \
        -eval 'eunit:test(varp_parse_tests,[verbose]), halt(0).'

## Layout

| module                 | covers                                                   |
|------------------------|----------------------------------------------------------|
| `varp_tc`              | helpers, not a test module                               |
| `varp_scan_tests`      | `varp_scan.xrl` / `varp_scani.xrl`, tokens and comments  |
| `varp_parse_tests`     | `varp_parse.yrl`, ASTs, precedence, sections, circuits, and the `formulas/varp` corpus |
| `varp_formula_tests`   | `varp_formula:build/2` - connectives, quantifiers, arithmetic, vectors, defines |
| `varp_circuit_tests`   | `varp_circuit:test/0` plus the `circuit` language construct |
| `varp_arith_tests`     | `varp_arith:test/0` and `varp_bitvec`/`varp_math`         |
| `varp_nif_tests`       | `varp_nif_test:all/0` plus direct nif checks             |
| `varp_sat_tests`       | satisfy/prove/falsify, backtrack vs backjump, timeouts, proof output, the other plugins |
| `varp_backend_tests`   | DIMACS and SNF in and out, the cnf writer, formatting     |
| `varp_cli_tests`       | `varp:main/1` in its own erl - options, exit codes, output |
| `varp_wx_tests`        | the gui plugin contract, its output callback and (opt in) the window |

## Helpers

`varp_tc` is the shared helper module.  The names it exports:

    varp_tc:parse_only(Text)      %% scan+parse only, no section handling
    varp_tc:parse(Text[,Opts])    %% full parse, {Sections,Assignments,Formula}
    varp_tc:formula(Text)         %% just the main formula
    varp_tc:sections(Text)        %% just the section map
    varp_tc:run(Text,Do[,Opts])   %% build and run a plugin chain
    varp_tc:models(Text[,Opts])   %% all models, normalised and sorted
    varp_tc:count(Text[,Opts])    %% number of models
    varp_tc:is_sat/is_unsat/is_tautology(Text[,Opts])
    varp_tc:cli(Args)             %% run varp:main/1, {ExitCode,Output}
    varp_tc:erl_eval(Expr)        %% run an expression in its own erl
    varp_tc:quiet(Fun)            %% run Fun with io thrown away

`Opts` is a map of global options, plus `meta` for the bindings a
formula needs, eg

    varp_tc:count(Formula, #{meta => #{<<"n">> => 4}})

## Known limitations

Constructs that `SYNTAX.md` describes but the grammar does not accept
today are listed twice, on purpose:

  * `varp_parse_tests:grammar_limitation_test_/0` asserts that each of
    them is *still* a syntax error, so fixing the grammar makes the
    test fail and reminds you to trim the list
  * `varp_parse_tests:?XFAIL` names the files under `formulas/varp`
    that do not parse, with the reason

`varp_backend_tests` has the same arrangement for `?CNF_XFAIL` and
`?SNF_XFAIL`.
