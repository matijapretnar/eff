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

* a simple loop that could fail, though never does
* the same loop as before, though written with a tail call
* finding a first solution of the n-queens problem using backtracking
* finding all solutions of the n-queens problem

We compare:

* the automatically generated code using our library (marked with a `Handlers - /commit SHA/`)
* a hand-written solution that uses our library (marked with `Handlers - hand-written`)
* a natural solution one would write without handlers (marked with `Native - /technique used/`)

The compared commits:

* `ce4263d`: 2016-10-10 (when we started with systematic benchmarks)
* `7cc7606`: 2016-03-18 (from Dagstuhl the first generated code that uses the new library)
