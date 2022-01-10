open Utils
open Language

type state

val initial_state : state

val load_primitive_value :
  state -> UntypedSyntax.variable -> Primitives.primitive_value -> state

val load_primitive_effect :
  state -> UntypedSyntax.variable -> Primitives.primitive_effect -> state

val desugar_computation :
  state -> SugaredSyntax.term -> state * UntypedSyntax.computation

val desugar_def_effect :
  loc:Location.t ->
  state ->
  SugaredSyntax.effect * (SugaredSyntax.ty * SugaredSyntax.ty) ->
  state * (Effect.t * (Type.ty * Type.ty))

val desugar_top_let :
  loc:Location.t ->
  state ->
  (SugaredSyntax.pattern * SugaredSyntax.term) list ->
  state * (UntypedSyntax.pattern * UntypedSyntax.computation) list

val desugar_top_let_rec :
  state ->
  (SugaredSyntax.variable * SugaredSyntax.term) list ->
  state * (Term.Variable.t * UntypedSyntax.abstraction) list

val desugar_tydefs :
  loc:Utils.Location.t ->
  state ->
  ( string,
    (SugaredSyntax.typaram * variance) list * SugaredSyntax.tydef )
  Assoc.t ->
  state * (TyName.t, Type.type_data) Assoc.t
