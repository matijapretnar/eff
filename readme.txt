To compile eff:

1) Run the make file using the command "make". This builds eff and generates a native excecutable.

2) To generate an ml file from an eff file run the following command :
     
     ./eff.native -n -V 4 --compile [filename]"

     * The command generates an ml file with the same name that runs on OCaml 2.0.2.

3) You can access the help through the command 

     ./eff.native -help


-------------------------------------------------------------------------------------------------------

Notes on the implementation:

* We use the word "effect" as a reference to "operations" from the paper.

* The part responsible of the term rewriting rules can be found in src/codegen/optimize.ml


--------------------------------------------------------------------------------------------------------

To Run the benchmarks :

1) The benchmarks can be found in the folder tests/code-generation/benchmarks.

2) To compile the benchmarks, first install [OPAM](https://opam.ocaml.org).
   Then, using OPAM, install the `core_bench` package:

     opam install core_bench

3) After everything is installed, you can go to `benchmarks` directory and compile the benchmark with

    ocamlbuild -use-ocamlfind benchmark.native

and run it with

    ./benchmark.native -quota 1 
