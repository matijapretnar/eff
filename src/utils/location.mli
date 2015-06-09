(** Source code locations

    To show the user what piece of code is causing errors, we tag each construct
    with a corresponding location in the source. This consists of the name of
    the file and starting and ending position in the file (i.e. line and column
    number). *)

(** Type of locations. *)
type t

(** Print a location. *)
val print : t -> Format.formatter -> unit

(** Unknown location. *)
val unknown : t

(** Make a location from two lexing positions. *)
val make : Lexing.position -> Lexing.position -> t

(** Merge two locations into one. *)
val merge : t -> t -> t

(** Get the location of the current lexeme in a lexing buffer. *)
val of_lexeme : Lexing.lexbuf -> t
