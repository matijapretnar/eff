(** Pattern matching exhaustiveness checking as described by Maranget [1]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred.

   [1] http://pauillac.inria.fr/~maranget/papers/warn/index.html
*)

(** Check that a list of patterns is exhaustive, report a warning if it is not. *)
val check_patterns : ?pos:Common.position -> Pattern.t list -> unit

(** Check that a pattern is irrefutable, report a warning if it is refutable. *)
val is_irrefutable : Pattern.t -> unit

