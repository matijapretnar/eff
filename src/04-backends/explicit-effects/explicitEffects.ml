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
    let ty1 = Type.source_to_target state.type_system_state.tydefs ty1 in
    let ty2 = Type.source_to_target state.type_system_state.tydefs ty2 in
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
        let e'' =
          if !Config.enable_optimization then
            Optimizer.optimize_expression state.optimizer_state e'
          else e'
        in
        let type_system_state' =
          ExplicitInfer.extend_var state.type_system_state x e''.ty
        in
        let backend_state' =
          ExBackend.process_top_let state.backend_state (x, e'')
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
        let a'' =
          if !Config.enable_optimization then
            Optimizer.optimize_abstraction state.optimizer_state a'
          else a'
        in
        let ty_in, drty_out = a''.ty in
        let fun_ty = Type.Arrow (ty_in, drty_out) in
        let type_system_state' =
          ExplicitInfer.extend_var state.type_system_state f fun_ty
        in

        let backend_state' =
          ExBackend.process_top_let_rec state.backend_state (f, a'')
        in
        {
          state with
          type_system_state = type_system_state';
          backend_state = backend_state';
        }
    | _ -> failwith __LOC__

  let process_external state (x, ty, name) =
    let ty = Type.source_to_target state.type_system_state.tydefs ty in
    let type_system_state' =
      ExplicitInfer.extend_var state.type_system_state x ty
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

  let process_top_let state (x, exp) =
    let v = Eval.eval_expression state.evaluation_state exp in
    Format.fprintf !Config.output_formatter "@[%t : %t = %t@]@."
      (Language.CoreTypes.Variable.print x)
      (Type.print_ty exp.ty) (V.print_value v);
    { evaluation_state = Eval.update x v state.evaluation_state }

  let process_top_let_rec state (f, abs) =
    {
      evaluation_state =
        Eval.extend_let_rec state.evaluation_state (Assoc.of_list [ (f, abs) ]);
    }

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

  type state = {
    prog : SyntaxNoEff.cmd list;
    no_eff_optimizer_state : NoEffOptimizer.state;
  }

  let initial_state =
    { prog = []; no_eff_optimizer_state = NoEffOptimizer.initial_state }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)

  let optimize_term state term =
    let t' =
      if !Config.enable_optimization then
        NoEffOptimizer.optimize_term state.no_eff_optimizer_state term
      else term
    in
    t'

  let optimize_abstraction state abstraction =
    let t' =
      if !Config.enable_optimization then
        NoEffOptimizer.optimize_abstraction state.no_eff_optimizer_state
          abstraction
      else abstraction
    in
    t'

  let process_computation state c =
    let c' = optimize_term state @@ TranslateExEff2NoEff.elab_computation c in
    { state with prog = SyntaxNoEff.Term c' :: state.prog }

  let process_type_of state _ =
    (* Print.warning "[#typeof] commands are ignored when compiling to OCaml."; *)
    state

  let process_def_effect state eff =
    {
      state with
      prog =
        SyntaxNoEff.DefEffect (TranslateExEff2NoEff.elab_effect eff)
        :: state.prog;
    }

  let process_top_let state (x, e) =
    let t = optimize_term state @@ TranslateExEff2NoEff.elab_expression e in
    { state with prog = SyntaxNoEff.TopLet (x, t) :: state.prog }

  let process_top_let_rec state (x, a) =
    let t =
      optimize_abstraction state @@ TranslateExEff2NoEff.elab_abstraction a
    in
    { state with prog = SyntaxNoEff.TopLetRec (x, t) :: state.prog }

  let process_external state (x, ty, name) =
    {
      state with
      prog =
        SyntaxNoEff.External (x, TranslateExEff2NoEff.elab_ty ty, name)
        :: state.prog;
    }

  let process_tydef state tydefs =
    let converter (ty_params, tydef) =
      (ty_params, TranslateExEff2NoEff.elab_tydef tydef)
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    { state with prog = SyntaxNoEff.TyDef tydefs' :: state.prog }

  let finalize state =
    if !Config.include_header_open then
      Format.fprintf !Config.output_formatter "open OcamlHeader;;";
    List.iter
      (fun cmd ->
        Format.fprintf !Config.output_formatter "%t\n"
          (TranslateNoEff2Ocaml.pp_cmd cmd))
      (List.rev state.prog)
end)
