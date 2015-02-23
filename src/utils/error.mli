(** Errors raised by Eff. *)

(** Each error has a locatio, a type (typing, runtime, ...), and a message. *)
exception Error of (Location.t option * string * string)

(** Shortcut functions for raising errors. In addition to an error location,
    the functions accept a message, which is a format string.
    This allows one, for example, to raise a typing error as
    [Error.typing "Unknown name %s." x]. *)

(** Fatal errors are errors over which Eff has no control, for example when
    a file cannot be opened. *)
val fatal : ('a, Format. formatter, unit, 'b) format4 -> 'a

(** Syntax errors occur during lexing, parsing, or desugaring into Eff's core
    language. *)
val syntax : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(** Typing errors can occur while defining types and during type inference. *)
val typing : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a

(** Runtime errors are usually prevented by type-checking. Otherwise, they occur
    when pattern match is not exhaustive, or when an externaly defined function
    has an incorrectly assigned type. *)
val runtime : ('a, Format.formatter, unit, 'b) format4 -> 'a
