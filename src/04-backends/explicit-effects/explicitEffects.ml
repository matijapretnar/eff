(* Compilation to multicore ocaml *)
open Utils
module V = Value

module type ExplicitBackend = sig
  type state

  val initial_state : state

  val process_computation : state -> Term.computation -> state

  val process_type_of : state -> Term.computation -> state

  val process_def_effect : state -> Term.effect -> state

  val process_top_let : state -> Term.variable * Term.expression -> state

  val process_top_let_rec : state -> Term.variable * Term.abstraction -> state

  val process_external : state -> Term.variable * Type.ty * string -> state

  val process_tydef :
    state ->
    ( Language.CoreTypes.TyName.t,
      Language.CoreTypes.TyParam.t list * Language.Type.tydef )
    Assoc.t ->
    state

  val finalize : state -> unit
end

module Make (ExBackend : ExplicitBackend) : Language.BackendSignature.T = struct
  type state = {
    type_system_state : ExplicitInfer.state;
    backend_state : ExBackend.state;
    optimizer_state : Optimizer.state;
  }

  let initial_state =
    {
      type_system_state = ExplicitInfer.initial_state;
      backend_state = ExBackend.initial_state;
      optimizer_state = Optimizer.initial_state;
    }

  let process_computation state c _ =
    let c' = ExplicitInfer.top_level_computation state.type_system_state c in
    let c'' =
      if !Config.enable_optimization then
        Optimizer.optimize_computation state.optimizer_state c'
      else c'
    in
    let backend_state' =
      ExBackend.process_computation state.backend_state c''
    in
    { state with backend_state = backend_state' }

  let process_type_of state c _ =
    let c' = ExplicitInfer.top_level_computation state.type_system_state c in
    let c'' =
      if !Config.enable_optimization then
        Optimizer.optimize_computation state.optimizer_state c'
      else c'
    in
    let backend_state' = ExBackend.process_type_of state.backend_state c'' in
    { state with backend_state = backend_state' }

  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1 = Type.source_to_target state.type_system_state.tctx_st ty1 in
    let ty2 = Type.source_to_target state.type_system_state.tctx_st ty2 in
    let type_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2) state.type_system_state
    in
    let backend_state' =
      ExBackend.process_def_effect state.backend_state (eff, (ty1, ty2))
    in
    {
      state with
      type_system_state = type_system_state';
      backend_state = backend_state';
    }

  let process_top_let state defs _vars =
    match defs with
    | [] -> assert false
    | [
     ( { it = Language.UntypedSyntax.PVar x; _ },
       { it = Language.UntypedSyntax.Value v; _ } );
    ] ->
        let e' = ExplicitInfer.top_level_expression state.type_system_state v in
        let type_system_state' =
          ExplicitInfer.add_type state.type_system_state x e'.ty
        in
        let backend_state' =
          ExBackend.process_top_let state.backend_state (x, e')
        in
        {
          state with
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | _ -> failwith __LOC__

  let process_top_let_rec state defs _vars =
    match Assoc.to_list defs with
    | [] -> assert false
    | [ (f, a) ] ->
        let a' =
          ExplicitInfer.top_level_rec_abstraction state.type_system_state f a
        in
        let ty_in, drty_out = a'.ty in
        let fun_ty = Type.Arrow (ty_in, drty_out) in
        let type_system_state' =
          ExplicitInfer.add_type state.type_system_state f fun_ty
        in

        let backend_state' =
          ExBackend.process_top_let_rec state.backend_state a'
        in
        {
          state with
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | _ -> failwith __LOC__

  (* process_top_let state lst
     match Assoc.to_list lst with
     | [ (v, (p, c)) ] ->
         let (((typed_abs, _c), _ty) as l_rec) =
           ExplicitInfer.tcTopLetRec state.type_system_state
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
             state.type_system_state typed_abs
         in
         let effect_system_state =
           { state.effect_system_state with type_system_state }
         in
         { backend_state = backend_state'; effect_system_state }
     | _ -> failwith __LOC__ *)

  let process_external state (x, ty, name) =
    let ty = Type.source_to_target state.type_system_state.tctx_st ty in
    let type_system_state' =
      ExplicitInfer.addExternal state.type_system_state x ty
    in
    let backend_state' =
      ExBackend.process_external state.backend_state (x, ty, name)
    in
    {
      state with
      type_system_state = type_system_state';
      backend_state = backend_state';
    }

  let process_tydef state tydefs =
    let type_system_state' =
      ExplicitInfer.add_type_definitions state.type_system_state tydefs
    in
    let backend_state' = ExBackend.process_tydef state.backend_state tydefs in
    {
      state with
      type_system_state = type_system_state';
      backend_state = backend_state';
    }

  let finalize state = ExBackend.finalize state.backend_state
end

module Evaluate : Language.BackendSignature.T = Make (struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { evaluation_state : Eval.state }

  let initial_state = { evaluation_state = Eval.initial_state }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c =
    let v = Eval.run state.evaluation_state c in
    Format.fprintf !Config.output_formatter "@[- : %t = %t@]@."
      (Type.print_dirty c.ty) (V.print_value v);
    state

  let process_type_of state c =
    Format.fprintf !Config.output_formatter "- : %t\n" (Type.print_dirty c.ty);
    state

  let process_def_effect state _ = state

  let process_top_let _state _ = failwith __LOC__

  let process_top_let_rec _state _ = failwith __LOC__

  let process_external state (x, _ty, f) =
    let evaluation_state' =
      match Assoc.lookup f External.values with
      | Some v -> Eval.update x v state.evaluation_state
      | None -> Error.runtime "unknown external symbol %s." f
    in
    { evaluation_state = evaluation_state' }

  let process_tydef state _ = state

  let finalize _state = ()
end)

module CompileToPlainOCaml : Language.BackendSignature.T = Make (struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = { prog : SyntaxNoEff.cmd list }

  let initial_state = { prog = [] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)

  let process_computation state c =
    let c' = TranslateExEff2NoEff.elab_computation c in
    { prog = SyntaxNoEff.Term c' :: state.prog }

  let process_type_of state _ =
    Print.warning "[#typeof] commands are ignored when compiling to OCaml.";
    state

  let process_def_effect state eff =
    {
      prog =
        SyntaxNoEff.DefEffect (TranslateExEff2NoEff.elab_effect eff)
        :: state.prog;
    }

  let process_top_let state (x, e) =
    {
      prog =
        SyntaxNoEff.TopLet (x, TranslateExEff2NoEff.elab_expression e)
        :: state.prog;
    }

  let process_top_let_rec state (x, a) =
    {
      prog =
        SyntaxNoEff.TopLetRec (x, TranslateExEff2NoEff.elab_abstraction a)
        :: state.prog;
    }

  let process_external state (x, ty, name) =
    {
      prog =
        SyntaxNoEff.External (x, TranslateExEff2NoEff.elab_ty ty, name)
        :: state.prog;
    }

  let process_tydef state tydefs =
    let converter (ty_params, tydef) =
      (ty_params, TranslateExEff2NoEff.elab_tydef tydef)
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    { prog = SyntaxNoEff.TyDef tydefs' :: state.prog }

  let finalize state =
    if !Config.include_header then
      Format.fprintf !Config.output_formatter "%s;;" OcamlHeader_ml.source;
    List.iter
      (fun cmd ->
        Format.fprintf !Config.output_formatter "%t\n"
          (TranslateNoEff2Ocaml.pp_cmd cmd))
      (List.rev state.prog)
end)
