(** Source code locations

    To show the user what piece of code is causing errors, we tag each construct
    with a corresponding location in the source. This consists of the name of
    the file and starting and ending position in the file (i.e. line and column
    number). *)

type t
(** Type of locations. *)

val print : t -> Format.formatter -> unit
(** Print a location. *)

val unknown : t
(** Unknown location. *)

val make : Lexing.position -> Lexing.position -> t
(** Make a location from two lexing positions. *)

val union : t list -> t
(** Computes the smallest location containing all known locations in the list. *)

val of_lexeme : Lexing.lexbuf -> t
(** Get the location of the current lexeme in a lexing buffer. *)
