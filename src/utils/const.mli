type t = private
  | Integer of int
  | String of string
  | Boolean of bool
  | Float of float
  | In_channel of in_channel
  | Out_channel of out_channel

val of_in_channel : in_channel -> t
val of_out_channel : out_channel -> t

val of_integer : int -> t

val of_string : string -> t

val of_boolean : bool -> t

val of_float : float -> t

val of_true : t

val of_false : t

val print : t -> Format.formatter -> unit

val compare : t -> t -> OldUtils.comparison

val equal : t -> t -> bool
