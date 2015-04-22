(** Error reporting

    All internal errors are represented uniformly with a single exception that
    carries additional details such as error kind (syntax, typing, ...), message
    or location.

    Errors are raised through helper functions that take an optional location
    and a message in form of a format string. For example, a typing error can be
    raised by [Error.typing ~loc "Type %t is not a product." (print_ty t)]. *)

(** Type of error details. *)
type details

(** Print error details. *)
val print : details -> unit

(** Exception representing all possible Andromeda errors. *)
exception Error of details

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
