(** Types shared by different modules *)

(** variable symbols *)
module Variable = Symbol.Make (Symbol.String)

(** effect symbols *)
module Effect = Symbol.Make (Symbol.String)

(** variant labels *)
type label = string
(** Variants for the built-in list type *)
let cons : label = "$1cons"

let nil : label = "$0nil"

(** record fields *)
type field = string

(** type names *)
type tyname = string

(** type parameters *)
type typaram = string

(** dirt parameters *)
type dirtparam = int