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
  | Invariant -> print "o"

let is_compatible declared detected =
  match declared with
  | Invariant -> detected = Invariant
  | Contravariant -> detected <> Covariant
  | Covariant -> detected <> Contravariant

module VarianceSet = Set.Make (struct
  type t = variance

  let compare = Stdlib.compare
end)

(** type parameters *)
module TyParam = struct
  include Symbol.Make (Symbol.Parameter (struct
    let ascii_symbol = "ty"

    let utf8_symbol = "\207\132"
  end))

  let print_old ?(poly = []) k ppf =
    let c = if List.mem k poly then "'" else "'_" in
    fold
      (fun _ k ->
        if 0 <= k && k <= 25 then
          Format.fprintf ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
        else Format.fprintf ppf "%sty%i" c (k - 25))
      k
end
