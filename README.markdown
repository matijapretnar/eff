Eff
===

Eff is a functional programming language based on algebraic effects and
their handlers.

Algebraic effects are a way of adding computational effects to a pure
functional setting. In a technical sense they are subsumed by the monadic
approach to computational effects, but they offer new ways of programming
that are not easily achieved with monads. In particular, algebraic effects
are combined seamlessly, whereas monad transformers are needed in the
monadic style.

The main idea of eff is that computational effects are accessed through a
set of operations, for example `lookup` and `update` for state, `read` and
`write` for I/O, `raise` for exceptions, etc. The behavior of operations is
determined by handlers. Just like an exception handler determines what
happens when an exception is raised, a general handler describes the
actions taken when an operation is triggered. Examples of handlers include
state, transactions, non-determinism, stream redirection, backtracking,
delimited continuations, and many others.

Because eff supports first-class effects and handlers, programmers may
define new computational effects, combine existing ones, and handle effects
in novel ways. For instance, ML-style references are a defined concept in
eff.

Eff code looks and feels like that of Ocaml because eff uses Ocaml syntax
extended with constructs for effects and handlers. Furthermore, eff is a
statically typed language with parametric polymorphism and type inference.
The types are similar to those of OCaml and other variants of ML in the
sense that they do not express any information about computational effects.

For further information visit the [eff page](http://math.andrej.com/eff/)
or contact the authors Andrej Bauer <Andrej.Bauer@andrej.com> and Matija
Pretnar <matija@pretnar.info>,

Obtaining eff
-------------

### Prerequisites

We have tested eff on Mac OS X and Linux, and it should work in other
Unix-like environments. In principle, nothing prevents eff from running
on Windows, we just have not tested it yet.

To install eff, you need a standard Unix-style build environment as well as

1. [OCaml](http://caml.inria.fr/ocaml/), version 3.12 or newer, and
2. [Menhir](http://cristal.inria.fr/~fpottier/menhir/) parser generator

We do not require, but recommend a command-line editing wrapper such as
[rlwrap](http://utopia.knoware.nl/~hlub/rlwrap/#rlwrap) or
[ledit](http://cristal.inria.fr/~ddr/ledit/). Eff uses these automatically.
   

### Compilation

To compile eff, first run

    ./configure

If it complains you will have to install missing prerequisites. The
configuration script takes standard GNU Autoconf arguments, such as
`--prefix` which determines where to install eff. Type `./configure --help`
for more information. Next, run

    make

If all goes well, you should be able to run eff in-place by typing `./eff`.

You can also run a battery of tests with

    make test

### Installation

To install the command `eff`, run

    sudo make install

See the file `etc/README.txt` for editor support.

Copyright and license
---------------------

Copyright (c) 2012, Andrej Bauer and Matija Pretnar

Eff is distributed under the abbreviated BSD License, see `LICENSE.txt` for
licensing information.
