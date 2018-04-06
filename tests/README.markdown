This directory contains scripts that test various aspects of Eff:

- The folder `regression` contains the basic regression tests that ensure that
  inferred types and computed values are what we expect. Any time a bug is
  found, one should add a new test that covers it.

- The folder `type-inference` contains benchmarks that compare the speed
  of type inference in Eff and OCaml. It's main purpose is to back findings of
  the paper "M. Pretnar: Inferring Algebraic Effects".
