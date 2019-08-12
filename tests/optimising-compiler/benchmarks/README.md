Optimising Compiler
==================

An efficient implementation of handlers of algebraic effects

### Running benchmarks

To compile the benchmarks, first install [OPAM](https://opam.ocaml.org).
Then, using OPAM, install the `core_bench` package:

    opam install core_bench

After everything is installed, you can go to `benchmarks` directory and compile the benchmark with

    ./benchmark.sh


### Interpreting results

We run the following benchmarks:

* a pure loop
* a loop with a latent effect that is never called
* a loop that increments a counter
* a loop that increments a reference
* finding a first solution of the n-queens problem using backtracking
* finding all solutions of the n-queens problem

We compare:

* a hand-written solution that uses our library (marked with `handwritten`)
* a natural solution one would write without handlers (marked with `native - /variant/`)
* the automatically generated code (marked with ``RESULT - Process time`)

Currently the benchmarks use different formats for the ones written in OCaml (handwritten, native) and the ones interpreted in Eff, because compilation to OCaml does not work.
The comparison between optimized and non-optimized Eff code is thus the most informative.
