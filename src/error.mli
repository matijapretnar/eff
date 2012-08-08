(** Errors raised by eff. *)

(** Each error has a position, a type (typing/runtime/...), and a message. *)
exception Error of (Common.position * string * string)

(** Shortcut functions for raising errors. In addition to an error position,
    the functions accept a message, which is a format string.
    This allows one, for example, to raise a typing error as
    [Error.typing "Unknown name %s." x]. *)
val fatal :
  pos:Common.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val syntax :
  pos:Common.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val typing :
  pos:Common.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val runtime :
  pos:Common.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
val exc :
  pos:Common.position -> ('a, Format.formatter, unit, 'b) format4 -> 'a
