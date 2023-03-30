open Utils
module TyParam = TyParam.TyParam

(** skeleton parameters *)
module Param = Symbol.Make (Symbol.Parameter (struct
  let ascii_symbol = "skl"
  let utf8_symbol = "ς"
end))

type t =
  | Param of Param.t
  | Basic of Const.ty
  | Arrow of t * t
  | Apply of { ty_name : TyName.t; skel_args : t TyParam.Map.t }
  | Handler of t * t
  | Tuple of t list

let rec print ?max_level skel ppf =
  let print_at ?at_level = Print.print ?max_level ?at_level ppf in
  match skel with
  | Param s -> Param.print s ppf
  | Basic b -> print_at "%t" (Const.print_ty b)
  | Arrow (skel1, skel2) -> print_at "%t → %t" (print skel1) (print skel2)
  | Apply { ty_name; skel_args } -> (
      match TyParam.Map.values skel_args with
      | [] -> print_at "%t" (TyName.print ty_name)
      | [ s ] ->
          print_at ~at_level:1 "%t %t" (print ~max_level:1 s)
            (TyName.print ty_name)
      | ts ->
          print_at ~at_level:1 "(%t) %t"
            (Print.sequence ", " print ts)
            (TyName.print ty_name))
  | Tuple [] -> print_at "𝟙"
  | Tuple skels ->
      print_at ~at_level:2 "%t" (Print.sequence "×" (print ~max_level:1) skels)
  | Handler (skel1, skel2) -> print_at "%t ⇛ %t" (print skel1) (print skel2)

let rec equal skel1 skel2 =
  match (skel1, skel2) with
  | Param s1, Param s2 -> s1 = s2
  | Arrow (ttya1, dirtya1), Arrow (ttyb1, dirtyb1) ->
      equal ttya1 ttyb1 && equal dirtya1 dirtyb1
  | Tuple tys1, Tuple tys2 ->
      List.length tys1 = List.length tys2 && List.for_all2 equal tys1 tys2
  | ( Apply { ty_name = ty_name1; skel_args = tys1 },
      Apply { ty_name = ty_name2; skel_args = tys2 } ) ->
      ty_name1 = ty_name2
      && TyParam.Map.equal (fun t1 t2 -> equal t1 t2) tys1 tys2
  | Handler (dirtya1, dirtya2), Handler (dirtyb1, dirtyb2) ->
      equal dirtya1 dirtyb1 && equal dirtya2 dirtyb2
  | Basic ptya, Basic ptyb -> ptya = ptyb
  | _, _ -> false
