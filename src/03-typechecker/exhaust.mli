(** Pattern matching exhaustiveness checking as described by Maranget [1]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred.

   [1] http://pauillac.inria.fr/~maranget/papers/warn/index.html
*)

val is_irrefutable :
  TypeDefinitionContext.state -> Parser.UntypedSyntax.pattern -> unit
(** Check that a pattern is irrefutable. *)

val check_computation :
  TypeDefinitionContext.state -> Parser.UntypedSyntax.computation -> unit

val check_expression :
  TypeDefinitionContext.state -> Parser.UntypedSyntax.expression -> unit
(** Check for refutable patterns in let statements and non-exhaustive match statements. *)
