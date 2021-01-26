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
  term : Term.computation;
  explicit_type : Type.target_ty * Type.dirt;
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

  val process_top_let :
    state ->
    effect_system_state ->
    Term.variable * Term.expression * Type.target_ty ->
    state

  val process_top_let_rec :
    state ->
    effect_system_state ->
    Language.UntypedSyntax.variable
    * Term.abstraction_with_ty
    * (Type.target_ty * Type.target_dirty) ->
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
      ExplicitInfer.top_level_computation
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
      ExplicitInfer.top_level_computation
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

  let process_top_let state defs _vars =
    match defs with
    | [] -> assert false
    | [
     ( { it = Language.UntypedSyntax.PVar x; _ },
       { it = Language.UntypedSyntax.Value v; _ } );
    ] ->
        let e', ty' =
          ExplicitInfer.top_level_expression
            state.effect_system_state.type_system_state v
        in
        let type_system_state' =
          ExplicitInfer.add_type state.effect_system_state.type_system_state x
            ty'
        and typechecker_state' =
          TypeChecker.add_external state.effect_system_state.typechecker_state x
            ty'
        in

        let effect_system_state' =
          {
            type_system_state = type_system_state';
            typechecker_state = typechecker_state';
          }
        in
        let backend_state' =
          ExBackend.process_top_let state.backend_state effect_system_state'
            (x, e', ty')
        in
        {
          effect_system_state = effect_system_state';
          backend_state = backend_state';
        }
    | _ -> failwith __LOC__

  let process_top_let_rec state defs _vars =
    match Assoc.to_list defs with
    | [] -> assert false
    | [ (f, a) ] ->
        let a', a_ty' =
          ExplicitInfer.top_level_rec_abstraction
            state.effect_system_state.type_system_state f a
        in
        let ty_in, drty_out = a_ty' in
        let fun_ty = Type.Arrow (ty_in, drty_out) in
        let type_system_state' =
          ExplicitInfer.add_type state.effect_system_state.type_system_state f
            fun_ty
        and typechecker_state' =
          TypeChecker.add_external state.effect_system_state.typechecker_state f
            fun_ty
        in

        let effect_system_state' =
          {
            type_system_state = type_system_state';
            typechecker_state = typechecker_state';
          }
        in
        let backend_state' =
          ExBackend.process_top_let_rec state.backend_state effect_system_state'
            (f, a', a_ty')
        in
        {
          effect_system_state = effect_system_state';
          backend_state = backend_state';
        }
    | _ -> failwith __LOC__

  (* process_top_let state lst
     match Assoc.to_list lst with
     | [ (v, (p, c)) ] ->
         let (((typed_abs, _c), _ty) as l_rec) =
           ExplicitInfer.tcTopLetRec state.effect_system_state.type_system_state
             v p c
         in
         let backend_state' =
           ExBackend.process_top_let_rec state.backend_state
             state.effect_system_state lst tys l_rec
         in
         let type_system_state =
           List.fold_left
             (fun st (v, p, c, _) ->
               ExplicitInfer.add_gbl_def st v (Type.Arrow (p, c)))
             state.effect_system_state.type_system_state typed_abs
         in
         let effect_system_state =
           { state.effect_system_state with type_system_state }
         in
         { backend_state = backend_state'; effect_system_state }
     | _ -> failwith __LOC__ *)

  let process_external state (x, ty, name) =
    let type_system_state' =
      ExplicitInfer.addExternal state.effect_system_state.type_system_state x ty
    in
    let typechecker_state' =
      TypeChecker.add_external state.effect_system_state.typechecker_state x
        (Type.source_to_target type_system_state'.tctx_st ty)
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
      (Type.print_target_dirty ty')
      (V.print_value v);
    state

  let process_type_of state _ _ { term = _; explicit_type = ty' } =
    Format.fprintf !Config.output_formatter "- : %t\n"
      (Type.print_target_dirty ty');
    state

  let process_def_effect state _ _ = state

  let process_top_let _state _defs _vars = failwith __LOC__

  let process_top_let_rec _state _defs _vars = failwith __LOC__

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

  type state = { prog : SyntaxNoEff.cmd list }

  let initial_state = { prog = [] }

  let process_type effect_system_state ty =
    snd
      (TranslateExEff2NoEff.elab_ty effect_system_state.typechecker_state
         (Type.source_to_target effect_system_state.type_system_state.tctx_st ty))

  let translate_expression state { type_system_state; typechecker_state } e =
    let e' =
      if !Config.enable_optimization then
        Optimizer.optimize_main_expr typechecker_state e
      else e
    in
    let _, trm = TranslateExEff2NoEff.elab_expression typechecker_state e' in
    (state, { type_system_state; typechecker_state }, trm)

  let translate_computation state { type_system_state; typechecker_state } c' =
    let c'' =
      if !Config.enable_optimization then
        Optimizer.optimize_main_comp typechecker_state c'
      else c'
    in
    let _, c''' = TranslateExEff2NoEff.elab_computation typechecker_state c'' in
    (state, { type_system_state; typechecker_state }, c''')

  let translate_abstraction state { type_system_state; typechecker_state }
      (p, ty, c') =
    let c'' =
      if !Config.enable_optimization then
        Optimizer.optimize_main_comp typechecker_state c'
      else c'
    in
    let a''', _ =
      TranslateExEff2NoEff.elab_abstraction typechecker_state (p, ty, c'')
    in
    (state, { type_system_state; typechecker_state }, a''')

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)

  let process_computation state { type_system_state; typechecker_state } _
      { term = c'; _ } =
    let state, _, c'''' =
      translate_computation state { type_system_state; typechecker_state } c'
    in
    { prog = SyntaxNoEff.Term c'''' :: state.prog }

  let process_type_of state _ _ _ =
    Print.warning "[#typeof] commands are ignored when compiling to OCaml.";
    state

  let process_def_effect state effect_system_state (eff, (ty1, ty2)) =
    {
      prog =
        SyntaxNoEff.DefEffect
          ( eff,
            ( process_type effect_system_state ty1,
              process_type effect_system_state ty2 ) )
        :: state.prog;
    }

  let process_top_let state { type_system_state; typechecker_state } (x, e, _ty)
      =
    let state, _, trm =
      translate_expression state { type_system_state; typechecker_state } e
    in
    { prog = SyntaxNoEff.TopLet (x, trm) :: state.prog }

  let process_top_let_rec state { type_system_state; typechecker_state }
      (x, a, (_ty_in, _ty_out)) =
    let state, _, a =
      translate_abstraction state { type_system_state; typechecker_state } a
    in
    { prog = SyntaxNoEff.TopLetRec (x, a) :: state.prog }

  let process_external state effect_system_state (x, ty, name) =
    {
      prog =
        SyntaxNoEff.External (x, process_type effect_system_state ty, name)
        :: state.prog;
    }

  let process_tydef state _ tydefs =
    let converter (ty_params, tydef) =
      (ty_params, TranslateExEff2NoEff.elab_tydef tydef)
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    { prog = SyntaxNoEff.TyDef tydefs' :: state.prog }

  let finalize state _ =
    if !Config.include_header then
      Format.fprintf !Config.output_formatter "%s;;" OcamlHeader_ml.source;
    List.iter
      (fun cmd ->
        Format.fprintf !Config.output_formatter "%t\n"
          (TranslateNoEff2Ocaml.pp_cmd cmd))
      (List.rev state.prog)
end)
