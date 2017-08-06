type t

(** The empty graph. *)
val empty : t

(* Combine two constraint sets to a single set *)
val union : t -> t -> t
