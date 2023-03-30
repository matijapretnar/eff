module type S = sig
  type state

  val initial_state : state

  val process_computation :
    state -> Type.Params.t * Term.computation * Constraints.t -> state

  val process_type_of :
    state -> Type.Params.t * Term.computation * Constraints.t -> state

  val process_def_effect : state -> Term.effect -> state

  val process_top_let :
    state ->
    (Term.pattern * Type.Params.t * Constraints.t * Term.computation) list ->
    state

  val process_top_let_rec : state -> Term.top_rec_definitions -> state

  val load_primitive_value :
    state -> Term.variable -> Primitives.primitive_value -> state

  val load_primitive_effect :
    state -> Term.effect -> Primitives.primitive_effect -> state

  val process_tydef : state -> (TyName.t, Type.type_data) Utils.Assoc.t -> state
  val finalize : state -> unit
end
