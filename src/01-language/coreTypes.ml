open Utils
(** Types shared by different modules *)

module Variable = Symbol.Make (Symbol.String)
(** variable symbols *)

module Effect = Symbol.Make (Symbol.String)
(** effect symbols *)

module Label = Symbol.Make (Symbol.String)
(** variant labels *)

(** Variants for the built-in list type *)
let nil_annot = "$0nil"

let nil = Label.fresh nil_annot

let cons_annot = "$1cons"

let cons = Label.fresh cons_annot

module Field = Symbol.Make (Symbol.String)
(** record fields *)

module TyName = Symbol.Make (Symbol.String)
(** type names *)

let bool_tyname = TyName.fresh "bool"

let int_tyname = TyName.fresh "int"

let unit_tyname = TyName.fresh "unit"

let string_tyname = TyName.fresh "string"

let float_tyname = TyName.fresh "float"

let list_tyname = TyName.fresh "list"

let empty_tyname = TyName.fresh "empty"

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
