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
type tyname = string

(** type parameters *)
type typaram = string

(** dirt parameters *)
module DirtParam = Symbol.Make (Symbol.Int)