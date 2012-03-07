Eff
===

Eff is a functional programming language based on algebraic effects and their
handlers.

Algebraic effects provide an alternative to monads for adding computational
effects to a pure functional setting. The main idea is that the only way to
access an effect is through a fixed set of operations, for example `lookup` and
`update` for state, `read` and `write` for I/O, or `raise` for exceptions.

Handlers of algebraic effects are a generalization of exception handlers to
other algebraic effects. Examples of such handlers include transactional memory,
stream redirection, backtracking, delimited continuations, and many others.
Handlers provide a control mechanism that is typically cleaner and easier to
understand than monads or delimited continuations.

Eff is statically typed with parametric polymorphism and type inference.  Eff
supports first-class effects and handlers, allowing the programmer to define new
computational effects, combine existing ones, and handle them in novel ways.
With the exception of effects and handlers, the syntax of eff closely follows
OCaml.

The type system similarly follows OCaml in the sense that the types do not
capture any information about computational effects. An effect system that
provides a static analysis of computational effects is planned for the next
major release of eff.

For further information contact Andrej Bauer <Andrej.Bauer@andrej.com>
or Matija Pretnar <matija@pretnar.info>.

Obtaining eff
-------------

### Prerequisites

We have tested eff on Mac OS X and Linux, and it should work in other
Unix-like environments. In principle, nothing prevents eff from running
on Windows, we just have not tested it yet.

To install eff, you need a standard Unix-style build environment as well as

1. [OCaml](http://caml.inria.fr/ocaml/), version 3.12 or newer, and
2. [Menhir](http://cristal.inria.fr/~fpottier/menhir/) parser generator

### Compilation

To compile eff, first run

    ./configure

If it complains you will have to install missing prerequisites. The
configuration script takes standard GNU Autoconf arguments, such as
`--prefix` which determines where to install eff. Type `./configure --help` for
more information. Next, run

    make

If all goes well, you should be able to run eff in-place by typing either
`./eff.native` or `./eff.byte` if you do not have `ocamlopt` for some reason.

You can also run a battery of tests with

    make test

### Installation

To install the command `eff`, run

    sudo make install

If you have the `rlwrap` or `ledit` line-editing wrapper, `eff` will use them.
If you install any of the two after you have installed `eff`, simply rerun
`./configure` and `make install`.

Copyright and license
---------------------

Copyright (c) 2012, Andrej Bauer and Matija Pretnar

See `LICENSE.txt` for licensing information.
