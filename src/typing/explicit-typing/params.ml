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
let fresh_ty_param = OldUtils.fresh OldUtils.id
let beautifying_ty_subst () =
  OldUtils.fresh OldUtils.id
let print_ty_param t ppf = Symbols.ty_param t true ppf
let print_type_param t ppf = Format.fprintf ppf "'t%d" t
let print_old_ty_param ?(poly=[]) k ppf =
  let c = (if List.mem k poly then "'" else "'_") in
  if 0 <= k && k <= 25
  then Format.fprintf ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
  else Format.fprintf ppf "%sty%i" c (k - 25)
