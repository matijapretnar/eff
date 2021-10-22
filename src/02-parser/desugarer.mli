open Utils
open Language
module Type = SimpleType

type state

val initial_state : state

val load_primitive_value :
  state -> UntypedSyntax.variable -> Primitives.primitive_value -> state

val load_primitive_effect :
  state -> UntypedSyntax.variable -> Primitives.primitive_effect -> state

val desugar_computation :
  state -> SugaredSyntax.term -> state * UntypedSyntax.computation

val desugar_def_effect :
  state ->
  SugaredSyntax.effect * (SugaredSyntax.ty * SugaredSyntax.ty) ->
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
  state
  * (CoreTypes.TyName.t, CoreTypes.TyParam.t list * SimpleType.tydef) Assoc.t
