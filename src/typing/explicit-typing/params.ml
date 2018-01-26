type ty_param = int
type dirt_param = int
type ty_coercion_param = int
type dirt_coercion_param = int
type dirty_coercion_param = int
type skel_param = int
type e_ty_param = int

let fresh_ty_param = OldUtils.fresh OldUtils.id
let fresh_dirt_param = OldUtils.fresh OldUtils.id
let fresh_ty_coercion_param = OldUtils.fresh OldUtils.id
let fresh_dirty_coercion_param = OldUtils.fresh OldUtils.id
let fresh_dirt_coercion_param = OldUtils.fresh OldUtils.id
let fresh_skel_param = OldUtils.fresh OldUtils.id
let fresh_e_ty_param = OldUtils.fresh OldUtils.id

let beautifying_ty_subst () =
  OldUtils.fresh OldUtils.id

let print_ty_param t ppf = Symbols.ty_param t true ppf
let print_ty_coercion_param t ppf = Symbols.ty_coercion_param t true ppf
let print_dirty_coercion_param t ppf = Symbols.dirty_coercion_param t true ppf
let print_dirt_coercion_param t ppf = Symbols.dirt_coercion_param t true ppf
let print_dirt_param d ppf = Symbols.dirt_param d true ppf
let print_skel_param t ppf = Symbols.skel_param t true ppf
let print_e_ty_param t ppf = Symbols.ty_param t true ppf

let print_type_param t ppf = Format.fprintf ppf "'t%d" t
let print_old_ty_param ?(poly=[]) k ppf =
  let c = (if List.mem k poly then "'" else "'_") in
  if 0 <= k && k <= 25
  then Format.fprintf ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
  else Format.fprintf ppf "%sty%i" c (k - 25)
