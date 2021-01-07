type t = private
  | Integer of int
  | String of string
  | Boolean of bool
  | Float of float

type ty = IntegerTy | StringTy | BooleanTy | FloatTy

val of_integer : int -> t

val of_string : string -> t

val of_boolean : bool -> t

val of_float : float -> t

val of_true : t

val of_false : t

val print : t -> Format.formatter -> unit

val print_ty : ty -> Format.formatter -> unit

val infer_ty : t -> ty

val compare : t -> t -> CoreUtils.comparison

val equal : t -> t -> bool
