open Utils
module CoreSyntax = UntypedSyntax

module type ExplicitT = sig
  type state

  val initial_state : state

  val process_computation : state -> Term.computation -> state

  val process_type_of : state -> Term.computation -> state

  val process_def_effect : state -> Term.effect -> state

  val process_top_let :
    state -> (Term.variable, Type.parameters * Term.expression) Assoc.t -> state

  val process_top_let_rec : state -> Term.rec_definitions -> state

  val load_primitive_value :
    state -> Term.variable -> Primitives.primitive_value -> state

  val load_primitive_effect :
    state -> Term.effect -> Primitives.primitive_effect -> state

  val process_tydef :
    state ->
    (CoreTypes.TyName.t, CoreTypes.TyParam.t list * SimpleType.tydef) Assoc.t ->
    state

  val finalize : state -> unit
end

module type T = sig
  type state

  val initial_state : state

  val load_primitive_value :
    state -> CoreTypes.Variable.t -> Primitives.primitive_value -> state

  val load_primitive_effect :
    state -> CoreTypes.Variable.t -> Primitives.primitive_effect -> state

  val process_computation :
    state ->
    Term.computation ->
    CoreTypes.TyParam.t list * SimpleType.ty ->
    state

  val process_type_of :
    state ->
    Term.computation ->
    CoreTypes.TyParam.t list * SimpleType.ty ->
    state

  val process_def_effect :
    state -> CoreTypes.Effect.t * (Type.ty * Type.ty) -> state

  val process_top_let :
    state ->
    (Term.pattern * Term.computation) list ->
    (Term.variable * SimpleType.ty_scheme) list ->
    state

  val process_top_let_rec :
    state ->
    (Term.variable, Term.abstraction) Assoc.t ->
    (Term.variable * SimpleType.ty_scheme) list ->
    state

  val process_tydef :
    state ->
    (CoreTypes.TyName.t, CoreTypes.TyParam.t list * Type.tydef) Assoc.t ->
    state

  val finalize : state -> unit
end
