Efficient handlers
==================

An efficient implementation of handlers of algebraic effects

### Running benchmarks

To compile the benchmarks, first install [OPAM](https://opam.ocaml.org).
Then, using OPAM, install the `core_bench` package:

    opam install core_bench

After everything is installed, you can go to `benchmarks` directory and compile the benchmark with

    ocamlbuild -use-ocamlfind benchmark.native

and run it with

    ./benchmark.native -quota 1


### Interpreting results

We run the following benchmarks:

* a pure loop
* a loop with a latent effet that is never called
* a loop that increments a counter
* a loop that increments a reference
* finding a first solution of the n-queens problem using backtracking
* finding all solutions of the n-queens problem

We compare:

* the automatically generated code (marked with a `Generated - /variant/`)
* a hand-written solution that uses our library (marked with `Hand written`)
* a natural solution one would write without handlers (marked with `Native - /variant/`)
