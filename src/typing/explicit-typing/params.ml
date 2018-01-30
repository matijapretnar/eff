module ETy = Symbol.Make(Symbol.Parameter(struct
  let ascii_symbol = "ety"
  let utf8_symbol = "eτ"
end))

module Dirt = Symbol.Make(Symbol.Parameter(struct
  let ascii_symbol = "drt"
  let utf8_symbol = "δ"
end))

module Skel = Symbol.Make(Symbol.Parameter(struct
  let ascii_symbol = "skl"
  let utf8_symbol = "s"
end))

module TyCoercion = Symbol.Make(Symbol.Parameter(struct
  let ascii_symbol = "tycoer"
  let utf8_symbol = "τycoer"
end))

module DirtCoercion = Symbol.Make(Symbol.Parameter(struct
  let ascii_symbol = "dirtcoer"
  let utf8_symbol = "dirtcoer"
end))

module DirtyCoercion = Symbol.Make(Symbol.Parameter(struct
  let ascii_symbol = "dirtycoer"
  let utf8_symbol = "dirtycoer"
end))

type ty_param = int
type dirt_param = Dirt.t
type ty_coercion_param = TyCoercion.t
type dirt_coercion_param = DirtCoercion.t
type dirty_coercion_param = DirtyCoercion.t
type skel_param = Skel.t
type e_ty_param = ETy.t

let fresh_ty_param = OldUtils.fresh OldUtils.id
let fresh_dirt_param = Dirt.fresh
let fresh_ty_coercion_param = TyCoercion.fresh
let fresh_dirt_coercion_param = DirtCoercion.fresh
let fresh_dirty_coercion_param = DirtyCoercion.fresh
let fresh_skel_param = Skel.fresh
let fresh_e_ty_param = ETy.fresh

let beautifying_ty_subst () =
  OldUtils.fresh OldUtils.id

let print_ty_param t ppf = Symbols.ty_param t true ppf
let print_dirt_param = Dirt.print ~safe:false
let print_ty_coercion_param = TyCoercion.print ~safe:false
let print_dirt_coercion_param = DirtCoercion.print ~safe:false
let print_dirty_coercion_param = DirtyCoercion.print ~safe:false
let print_skel_param = Skel.print ~safe:false
let print_e_ty_param = ETy.print ~safe:false

let print_type_param t ppf = Format.fprintf ppf "'t%d" t
let print_old_ty_param ?(poly=[]) k ppf =
  let c = (if List.mem k poly then "'" else "'_") in
  if 0 <= k && k <= 25
  then Format.fprintf ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
  else Format.fprintf ppf "%sty%i" c (k - 25)
