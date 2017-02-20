Efficient handlers
==================

An efficient implementation of handlers of algebraic effects

### Running benchmarks

To compile the benchmarks, first install [OPAM](https://opam.ocaml.org).
Then, using OPAM, install the `core_bench` package:

    opam install core, core_bench, delimcc

After everything is installed, you can go to `benchmarks` directory and compile the benchmark with

    ocamlbuild -use-ocamlfind benchmark.byte

and run it with

    ./benchmark.native -quota 1


### Interpreting results

We run the following benchmarks:

* finding a first solution of the n-queens problem using backtracking
* finding all solutions of the n-queens problem

We compare:

* a version of eff implemented directly in ocaml (`Eff directly in ocaml`)
* another version of eff implemented in ocaml (`Handlers in action`)
* the automatically generated code (marked with a `Generated - /variant/`)
