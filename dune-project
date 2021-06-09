(lang dune 2.8)
(using menhir 2.1)
(generate_opam_files true)
(cram enable)

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
  js_of_ocaml
  js_of_ocaml-ppx
  menhir
  (ocaml (>= 4.08.1))
  (ocamlformat (= 0.16.0))))
