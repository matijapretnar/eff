(** Pattern matching exhaustiveness checking as described by Maranget [1]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred.

   [1] http://pauillac.inria.fr/~maranget/papers/warn/index.html
*)

(** Check that a pattern is irrefutable. *)
val is_irrefutable : Syntax.pattern -> unit

(** Check for refutable patterns in let statements and non-exhaustive match statements. *)
val check_comp : Syntax.computation -> unit

