Many of the examples in this directory are taken from the paper
"Programming with Algebraic Effects and Handlers" by Andrej Bauer and
Matija Pretnar. The paper is available [here](http://arxiv.org/abs/1203.1539).

# Using Eff's NoEff backend

**Limitations:** NoEff is an intermediary language in compilation from Eff to OCaml, that has
no native effects, and is introduced for optimising the performance of compiled OCaml programs. 
A compiler backend branch that implements NoEff is included in this implementation, 
yet excludes the following Eff features:
- polymorphism
- top-level LET and LET REC bindings

**Supported examples:** As such, the following subset of examples in this directory is supported by the
NoEff backend branch:
- `queens.eff` = a monomorphic implementation of n-queens without top-level bindings
- `loop.eff` = a recursive loop
- `dummy.eff` = a handler indirection chain
- `dummy_fun.eff` = a function indirection chain

**Usage:** The NoEff backend branch can be invoked by setting the `--explicit-subtyping`
and `--compile-plain-ocaml` options in using this compiler. 
