(lang dune 2.5)
(using menhir 2.1)
(generate_opam_files true)

(name eff)
(version dev)
(source (github matijapretnar/eff))
(homepage "http://www.eff-lang.org/")
(authors "Andrej Bauer" "Matija Pretnar")
(license BSD2)
(maintainers "matija@pretnar.info")

(package
 (name eff)
 (synopsis "A functional programming language based on algebraic effect handlers")
 (depends
  menhir
  js_of_ocaml
  js_of_ocaml-ppx
  (ocaml (>= 4.06))
  (ocamlformat (= 0.16.0))))
