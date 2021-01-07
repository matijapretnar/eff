(** Error reporting

    All internal errors are represented uniformly with a single exception that
    carries additional details such as error kind (syntax, typing, ...), message
    or location.

    Errors are raised through helper functions that take an optional location
    and a message in form of a format string, for example:
    [Error.runtime ~loc "Unhandled effect %t" (Effect.print eff)]. *)

type t
(** Type of errors. *)

val print : t -> unit
(** Print an error. *)

exception Error of t
(** Exception representing all possible Eff errors. *)

val fatal : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Fatal errors are errors over which Eff has no control, for example when
    a file cannot be opened. *)

val syntax : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Syntax errors occur during lexing, parsing, or desugaring into Eff's core
    language. *)

val typing : loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Typing errors can occur while defining types and during type inference. *)

val runtime : ?loc:Location.t -> ('a, Format.formatter, unit, 'b) format4 -> 'a
(** Runtime errors are usually prevented by type-checking. Otherwise, they occur
    when pattern match is not exhaustive, or when an externally defined function
    has an incorrectly assigned type. *)
