(* Compilation to multicore ocaml *)
open Utils
module V = Value

module type ExplicitBackend = sig
  type state

  val initial_state : state

  val process_computation : state -> Term.computation -> state

  val process_type_of : state -> Term.computation -> state

  val process_def_effect : state -> Term.effekt -> state

  val process_top_let :
    state -> (Term.variable, Term.expression) Assoc.t -> state

  val process_top_let_rec : state -> Term.rec_definitions -> state

  val load_primitive :
    state -> Term.variable -> Language.Primitives.primitive -> state

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
    let c' = ExplicitInfer.process_computation state.type_system_state c in
    let c'' = Optimizer.process_computation state.optimizer_state c' in
    let backend_state' =
      ExBackend.process_computation state.backend_state c''
    in
    { state with backend_state = backend_state' }

  let process_type_of state c _ =
    let c' = ExplicitInfer.process_computation state.type_system_state c in
    let c'' = Optimizer.process_computation state.optimizer_state c' in
    let backend_state' = ExBackend.process_type_of state.backend_state c'' in
    { state with backend_state = backend_state' }

  let process_def_effect state (eff, (ty1, ty2)) =
    let type_system_state', (ty1, ty2) =
      ExplicitInfer.process_def_effect eff (ty1, ty2) state.type_system_state
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
    let type_system_state', defs' =
      ExplicitInfer.process_top_let state.type_system_state defs
    in
    let optimizer_state', defs'' =
      Optimizer.process_top_let state.optimizer_state defs'
    in
    let backend_state' = ExBackend.process_top_let state.backend_state defs'' in
    {
      type_system_state = type_system_state';
      optimizer_state = optimizer_state';
      backend_state = backend_state';
    }

  let process_top_let_rec state defs _vars =
    let type_system_state', defs' =
      ExplicitInfer.process_top_let_rec state.type_system_state defs
    in
    let optimizer_state', defs'' =
      Optimizer.process_top_let_rec state.optimizer_state defs'
    in
    let backend_state' =
      ExBackend.process_top_let_rec state.backend_state defs''
    in
    {
      type_system_state = type_system_state';
      optimizer_state = optimizer_state';
      backend_state = backend_state';
    }

  let load_primitive state x prim =
    let ty = Primitives.primitive_type_scheme prim in
    let type_system_state' =
      ExplicitInfer.extend_var state.type_system_state x ty
    in
    let backend_state' =
      ExBackend.load_primitive state.backend_state (Term.variable x ty) prim
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

  let process_top_let state defs =
    match Assoc.to_list defs with
    | [] -> state
    | [ (x, exp) ] ->
        let v = Eval.eval_expression state.evaluation_state exp in
        Format.fprintf !Config.output_formatter "@[%t : %t = %t@]@."
          (Language.CoreTypes.Variable.print x.term)
          (Type.print_ty exp.ty) (V.print_value v);
        { evaluation_state = Eval.update x v state.evaluation_state }
    | _ -> failwith __LOC__

  let process_top_let_rec state defs =
    Assoc.iter
      (fun (f, abs) ->
        Format.fprintf !Config.output_formatter "@[%t : %t = <fun>@]@."
          (Language.CoreTypes.Variable.print f.term)
          (Type.print_ty (Type.Arrow abs.ty)))
      defs;
    { evaluation_state = Eval.extend_let_rec state.evaluation_state defs }

  let load_primitive _state _x _prim = failwith "Not implemented"

  let process_tydef state _ = state

  let finalize _state = ()
end)

module CompileToPlainOCaml : Language.BackendSignature.T = Make (struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = {
    prog : SyntaxNoEff.cmd list;
    no_eff_optimizer_state : NoEffOptimizer.state;
    primitives :
      (Language.CoreTypes.Variable.t, Language.Primitives.primitive) Assoc.t;
  }

  let initial_state =
    {
      prog = [];
      no_eff_optimizer_state = NoEffOptimizer.initial_state;
      primitives = Assoc.empty;
    }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)

  let optimize_term state term =
    let t' =
      if !Config.enable_optimization then
        NoEffOptimizer.optimize_term state.no_eff_optimizer_state term
      else term
    in
    t'

  let optimize_rec_definitions state defs =
    let defs' =
      if !Config.enable_optimization then
        NoEffOptimizer.optimize_rec_definitions state.no_eff_optimizer_state
          defs
      else defs
    in
    defs'

  let process_computation state c =
    Print.debug "%t" (Term.print_computation c);
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

  let process_top_let state defs =
    let defs' =
      Assoc.kmap
        (fun (x, e) ->
          Print.debug "%t" (Term.print_expression e);
          (x.term, optimize_term state @@ TranslateExEff2NoEff.elab_expression e))
        defs
    in
    { state with prog = SyntaxNoEff.TopLet defs' :: state.prog }

  let process_top_let_rec state defs =
    let defs' =
      optimize_rec_definitions state
      @@ TranslateExEff2NoEff.elab_rec_definitions defs
    in
    { state with prog = SyntaxNoEff.TopLetRec defs' :: state.prog }

  let load_primitive state x prim =
    { state with primitives = Assoc.update x.term prim state.primitives }

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
          (TranslateNoEff2Ocaml.pp_cmd
             (TranslateNoEff2Ocaml.add_primitives
                TranslateNoEff2Ocaml.initial_state state.primitives)
             cmd))
      (List.rev state.prog)
end)
