module Assoc = Assoc
module Config = Config
module Error = Error
module Graph = Graph
module List = List
module Location = Location
module Option = Option
module Print = Print
module Symbol = Symbol
module Symbols = Symbols

type 'a located = { it : 'a; at : Location.t }
type ('trm, 'ty) typed = { term : 'trm; ty : 'ty }
type variance = Contravariant | Invariant | Covariant

let inverse = function
  | Contravariant -> Covariant
  | Invariant -> Invariant
  | Covariant -> Contravariant

let print_variance ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | Covariant -> print "+"
  | Contravariant -> print "-"
  | Invariant -> print ""
