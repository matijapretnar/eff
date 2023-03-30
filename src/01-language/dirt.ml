open Utils

(** dirt parameters *)
module Param = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "drt"
  let utf8_symbol = "δ"
end))

module Row = struct
  type t = Param of Param.t | Empty
end

type t = { effect_set : Effect.Set.t; row : Row.t }

let print ?max_level drt ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match (drt.effect_set, drt.row) with
  | effect_set, Empty -> print "{%t}" (Effect.Set.print effect_set)
  | effect_set, Param p when Effect.Set.is_empty effect_set ->
      print "%t" (Param.print p)
  | effect_set, Param p ->
      print ~at_level:1 "{%t}∪%t" (Effect.Set.print effect_set) (Param.print p)

let closed effect_set = { effect_set; row = Row.Empty }
let no_effect param = { effect_set = Effect.Set.empty; row = Param param }
let fresh () = no_effect (Param.fresh ())
let empty = closed Effect.Set.empty
let is_empty drt = Effect.Set.is_empty drt.effect_set && drt.row = Empty

let add_effects effect_set drt =
  { drt with effect_set = Effect.Set.union drt.effect_set effect_set }
