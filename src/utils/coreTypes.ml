(** Types shared by different modules *)

(** variable symbols *)
module Variable = Symbol.Make (Symbol.String)

(** effect symbols *)
module Effect = Symbol.Make (Symbol.String)

(** variant labels *)
module Label = Symbol.Make (Symbol.String)
(** Variants for the built-in list type *)
let nil_annot = "$0nil"
let nil = Label.fresh nil_annot

let cons_annot = "$1cons"
let cons = Label.fresh cons_annot

(** record fields *)
module Field = Symbol.Make (Symbol.String)

(** type names *)
module TyName = Symbol.Make (Symbol.String)

let bool_tyname = TyName.fresh "bool"
let int_tyname = TyName.fresh "int"
let unit_tyname = TyName.fresh "unit"
let string_tyname = TyName.fresh "string"
let float_tyname = TyName.fresh "float"
let list_tyname = TyName.fresh "list"
let empty_tyname = TyName.fresh "empty"

(** type parameters *)
type typaram = string

(** dirt parameters *)
module DirtParam = Symbol.Make (Symbol.Int)