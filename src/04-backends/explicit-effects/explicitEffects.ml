(* Compilation to multicore ocaml *)
open Utils
module V = Value

type effect_system_state = {
  type_system_state : ExplicitInfer.state;
  typechecker_state : TypeChecker.state;
}

type simple_comp = {
  simple_term : Language.UntypedSyntax.computation;
  simple_type : Language.CoreTypes.TyParam.t list * Language.Type.ty;
}

type explicit_comp = {
  term : Typed.computation;
  explicit_type : Types.target_ty * Types.dirt;
}

module type ExplicitBackend = sig
  type state

  val initial_state : state

  val process_computation :
    state -> effect_system_state -> simple_comp -> explicit_comp -> state

  val process_type_of :
    state -> effect_system_state -> simple_comp -> explicit_comp -> state

  val process_def_effect :
    state ->
    effect_system_state ->
    Language.CoreTypes.Effect.t * (Language.Type.ty * Language.Type.ty) ->
    state

  (*
  val process_top_let :
    state ->
    (Language.UntypedSyntax.pattern * Language.UntypedSyntax.computation) list ->
    (Language.UntypedSyntax.variable * Language.Type.ty_scheme) list ->
    state
      *)
  val _process_top_let_rec :
    state ->
    ( Language.UntypedSyntax.variable,
      Language.UntypedSyntax.abstraction )
    Assoc.t ->
    (Language.UntypedSyntax.variable * Language.Type.ty_scheme) list ->
    ((Language.UntypedSyntax.variable
     * Types.target_ty
     * (Types.target_ty * Types.dirt)
     * (Typed.pattern * Typed.computation))
     list
    * Typed.computation)
    * Types.target_ty ->
    state

  val process_external :
    state ->
    effect_system_state ->
    Language.CoreTypes.Variable.t * Language.Type.ty * string ->
    state

  val process_tydef :
    state ->
    effect_system_state ->
    ( Language.CoreTypes.TyName.t,
      Language.CoreTypes.TyParam.t list * Language.Type.tydef )
    Assoc.t ->
    state

  val finalize : state -> effect_system_state -> unit
end

module Make (ExBackend : ExplicitBackend) : Language.BackendSignature.T = struct
  type state = {
    effect_system_state : effect_system_state;
    backend_state : ExBackend.state;
  }

  let initial_state =
    {
      effect_system_state =
        {
          type_system_state = ExplicitInfer.initial_state;
          typechecker_state = TypeChecker.initial_state;
        };
      backend_state = ExBackend.initial_state;
    }

  let process_computation state c tysch =
    let c', ty' =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state.type_system_state c
    in
    let backend_state' =
      ExBackend.process_computation state.backend_state
        state.effect_system_state
        { simple_term = c; simple_type = tysch }
        { term = c'; explicit_type = ty' }
    in
    { state with backend_state = backend_state' }

  let process_type_of state c tysch =
    let c', ty' =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state.type_system_state c
    in
    let backend_state' =
      ExBackend.process_type_of state.backend_state state.effect_system_state
        { simple_term = c; simple_type = tysch }
        { term = c'; explicit_type = ty' }
    in
    { state with backend_state = backend_state' }

  let process_def_effect state (eff, (ty1, ty2)) =
    let type_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2)
        state.effect_system_state.type_system_state
    in
    let effect_system_state' =
      { state.effect_system_state with type_system_state = type_system_state' }
    in

    let backend_state' =
      ExBackend.process_def_effect state.backend_state effect_system_state'
        (eff, (ty1, ty2))
    in
    {
      backend_state = backend_state';
      effect_system_state = effect_system_state';
    }

  let process_top_let _state _defs _vars =
    failwith "Top level bindings not supported"

  let process_top_let_rec _state _ _ =
    failwith "Top level bindings not supported"

  let process_external state (x, ty, name) =
    let type_system_state' =
      ExplicitInfer.addExternal state.effect_system_state.type_system_state x ty
    in
    let typechecker_state' =
      TypeChecker.addExternal state.effect_system_state.typechecker_state x
        (Types.source_to_target type_system_state'.tctx_st ty)
    in
    let effect_system_state' =
      {
        type_system_state = type_system_state';
        typechecker_state = typechecker_state';
      }
    in
    let backend_state' =
      ExBackend.process_external state.backend_state effect_system_state'
        (x, ty, name)
    in
    {
      backend_state = backend_state';
      effect_system_state = effect_system_state';
    }

  let process_tydef state tydefs =
    let type_system_state' =
      ExplicitInfer.add_type_definitions
        state.effect_system_state.type_system_state tydefs
    in
    let effect_system_state' =
      { state.effect_system_state with type_system_state = type_system_state' }
    in
    let backend_state' =
      ExBackend.process_tydef state.backend_state effect_system_state' tydefs
    in
    {
      backend_state = backend_state';
      effect_system_state = effect_system_state';
    }

  let finalize state =
    ExBackend.finalize state.backend_state state.effect_system_state
end

module Evaluate : Language.BackendSignature.T = Make (struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { evaluation_state : Eval.state }

  let initial_state = { evaluation_state = Eval.initial_state }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state _ _ { term = c'; explicit_type = ty' } =
    let v = Eval.run state.evaluation_state c' in
    Format.fprintf !Config.output_formatter "@[- : %t = %t@]@."
      (Types.print_target_dirty ty')
      (V.print_value v);
    state

  let process_type_of state _ _ { term = _; explicit_type = ty' } =
    Format.fprintf !Config.output_formatter "- : %t\n"
      (Types.print_target_dirty ty');

    state

  let process_def_effect state _ _ = state

  let _process_top_let state _defs _vars _ =
    Print.debug "ignoring top let binding";
    state

  let _process_top_let_rec state _defs _vars (defs, _ty) =
    let [ (v, _, _, a) ], cmp = defs in
    let state' =
      {
        evaluation_state =
          Eval.extend_let_rec state.evaluation_state (Assoc.of_list [ (v, a) ]);
      }
    in
    state'

  let process_external state _ (x, _ty, f) =
    let evaluation_state' =
      match Assoc.lookup f External.values with
      | Some v -> Eval.update x v state.evaluation_state
      | None -> Error.runtime "unknown external symbol %s." f
    in
    { evaluation_state = evaluation_state' }

  let process_tydef state _ _ = state

  let finalize _state _ = ()
end)

module CompileToPlainOCaml : Language.BackendSignature.T = Make (struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { prog : SyntaxOcaml.cmd list }

  let initial_state = { prog = [] }

  let process_type effect_system_state ty =
    TranslateNoEff2Ocaml.elab_type
      (snd
         (TranslateExEff2NoEff.type_elab effect_system_state.type_system_state
            effect_system_state.typechecker_state
            (Types.source_to_target
               effect_system_state.type_system_state.tctx_st ty)))

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state { type_system_state; typechecker_state } _
      { term = c'; _ } =
    let c'' =
      if !Config.enable_optimization then
        Optimizer.optimize_main_comp typechecker_state c'
      else c'
    in
    let _, c''' =
      TranslateExEff2NoEff.comp_elab type_system_state typechecker_state c''
    in
    let c'''' = TranslateNoEff2Ocaml.elab_term c''' in
    { prog = SyntaxOcaml.Term c'''' :: state.prog }

  let process_type_of state _ _ _ =
    Print.warning "[#typeof] commands are ignored when compiling to OCaml.";
    state

  let process_def_effect state effect_system_state (eff, (ty1, ty2)) =
    {
      prog =
        SyntaxOcaml.DefEffect
          ( eff,
            process_type effect_system_state ty1,
            process_type effect_system_state ty2 )
        :: state.prog;
    }

  let _process_top_let _state _defs _vars _ =
    failwith "Top level bindings not supported"

  let _process_top_let_rec _state _ _ _ =
    failwith "Top level bindings not supported"

  let process_external state effect_system_state (x, ty, name) =
    {
      prog =
        SyntaxOcaml.External (x, process_type effect_system_state ty, name)
        :: state.prog;
    }

  let process_tydef state _ tydefs =
    let converter (ty_params, tydef) =
      ( ty_params,
        TranslateNoEff2Ocaml.elab_tydef (TranslateExEff2NoEff.elab_tydef tydef)
      )
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    { prog = SyntaxOcaml.TyDef tydefs' :: state.prog }

  let finalize state _ =
    if !Config.include_header then
      Format.fprintf !Config.output_formatter "%s" OcamlHeader_ml.source;
    List.iter
      (fun cmd ->
        Format.fprintf !Config.output_formatter "%t\n"
          (SyntaxOcaml.print_command cmd))
      (List.rev state.prog)
end)
