open Utils
open Language

type state

val initial_state : state

val load_primitive :
  state -> UntypedSyntax.variable -> Primitives.primitive -> state

val desugar_computation :
  state -> SugaredSyntax.term -> state * UntypedSyntax.computation

val desugar_def_effect :
  state ->
  SugaredSyntax.effekt * (SugaredSyntax.ty * SugaredSyntax.ty) ->
  state * (CoreTypes.Effect.t * (Type.ty * Type.ty))

val desugar_top_let :
  state ->
  (SugaredSyntax.pattern * SugaredSyntax.term) list ->
  state * (UntypedSyntax.pattern * UntypedSyntax.computation) list

val desugar_top_let_rec :
  state ->
  (SugaredSyntax.variable * SugaredSyntax.term) list ->
  state * (CoreTypes.Variable.t * UntypedSyntax.abstraction) list

val desugar_tydefs :
  state ->
  (string, SugaredSyntax.typaram list * SugaredSyntax.tydef) Assoc.t ->
  state * (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Type.tydef) Assoc.t
