type state

val initial_state : state

val desugar_computation :
  state -> SugaredSyntax.term -> UntypedSyntax.computation

val desugar_def_effect :
  state -> SugaredSyntax.effect * (SugaredSyntax.ty * SugaredSyntax.ty)
  -> SugaredSyntax.effect * (Type.ty * Type.ty)

val desugar_external :
  state -> SugaredSyntax.variable * SugaredSyntax.ty * string
  -> state * (UntypedSyntax.variable * Type.ty * string)

val desugar_top_let :
  state -> (SugaredSyntax.pattern * SugaredSyntax.term) list
  -> state * (UntypedSyntax.pattern * UntypedSyntax.computation) list

val desugar_top_let_rec :
  state -> (SugaredSyntax.variable * SugaredSyntax.term) list
  -> state * (UntypedSyntax.variable * UntypedSyntax.abstraction) list

val desugar_tydefs :
  state -> (string, OldUtils.typaram list * SugaredSyntax.tydef) Assoc.t
  -> state * (string, Params.Ty.t list * Tctx.tydef) Assoc.t
