# To install the effects compiler (or any other experimental OCaml compiler)
# I recommend first installing Gabriel Scherer's `opam compiler-conf`:
git clone https://github.com/gasche/opam-compiler-conf
cd opam-compiler-conf
./opam-compiler.conf.sh
cd ..

# After that download and install the effects compiler:
git clone -b 4.02.2+effects https://github.com/ocamllabs/ocaml-effects.git
cd ocaml-effects
opam compiler-conf configure
make world.opt
opam compiler-conf install

# After installation is done, `opam' will ask you to update the environment, i.e. eval `opam config env`.
# In order to install Links you need the packages `deriving' and `lwt' from opam.
# However, the former depends on `ppx_tools' which is broken under the multicore/effects compiler.
# Fortunately, KC has patched version on his github. We can pin it directly in opam:
cd ..
opam pin add ppx_tools https://github.com/kayceesrk/ppx_tools/archive/v4.02.3-effects.zip
opam install lwt deriving

git clone -b effect-handlers-compilation https://github.com/links-lang/links links-effects
cd links-effects
make nc

# Now you can run links
./links -c programs/cointoss.links -o toss
./toss
