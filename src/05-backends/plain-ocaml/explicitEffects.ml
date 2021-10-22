(* Compilation to multicore ocaml *)
open Utils
module V = Value
module Term = Language.Term
module Type = Language.Type

module Make (ExBackend : Language.BackendSignature.ExplicitT) :
  Language.BackendSignature.T = struct
  type state = {
    type_system_state : Typechecker.ExplicitInfer.state;
    backend_state : ExBackend.state;
    optimizer_state : Optimizer.state;
  }

  let initial_state =
    {
      type_system_state = Typechecker.ExplicitInfer.initial_state;
      backend_state = ExBackend.initial_state;
      optimizer_state =
        Optimizer.initial_state
          {
            specialize_functions =
              !Config.optimizator_config.specialize_functions;
            eliminate_coercions = !Config.optimizator_config.eliminate_coercions;
            push_coercions = !Config.optimizator_config.push_coercions;
            handler_reductions = !Config.optimizator_config.handler_reductions;
            purity_aware_translation =
              !Config.optimizator_config.purity_aware_translation;
          };
    }

  let process_computation state c _ =
    let c' =
      Typechecker.ExplicitInfer.process_computation state.type_system_state c
    in
    let c'' = Optimizer.process_computation state.optimizer_state c' in
    let backend_state' =
      ExBackend.process_computation state.backend_state c''
    in
    { state with backend_state = backend_state' }

  let process_type_of state c _ =
    let c' =
      Typechecker.ExplicitInfer.process_computation state.type_system_state c
    in
    let c'' = Optimizer.process_computation state.optimizer_state c' in
    let backend_state' = ExBackend.process_type_of state.backend_state c'' in
    { state with backend_state = backend_state' }

  let process_def_effect state (eff, (ty1, ty2)) =
    let type_system_state', (ty1, ty2) =
      Typechecker.ExplicitInfer.process_def_effect eff (ty1, ty2)
        state.type_system_state
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
      Typechecker.ExplicitInfer.process_top_let state.type_system_state defs
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
      Typechecker.ExplicitInfer.process_top_let_rec state.type_system_state defs
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

  let load_primitive_value state x prim =
    let ty = Typechecker.Primitives.primitive_value_type_scheme prim in
    let type_system_state' =
      Typechecker.ExplicitInfer.extend_var state.type_system_state x ty
    in
    let backend_state' =
      ExBackend.load_primitive_value state.backend_state x prim
    in
    {
      state with
      type_system_state = type_system_state';
      backend_state = backend_state';
    }

  let load_primitive_effect state eff prim =
    let ty1, ty2 =
      Typechecker.SimplePrimitives.primitive_effect_signature prim
    in
    let type_system_state', (ty1', ty2') =
      Typechecker.ExplicitInfer.process_def_effect eff (ty1, ty2)
        state.type_system_state
    in
    let backend_state' =
      ExBackend.load_primitive_effect state.backend_state
        (eff, (ty1', ty2'))
        prim
    in
    {
      state with
      type_system_state = type_system_state';
      backend_state = backend_state';
    }

  let process_tydef state tydefs =
    let type_system_state' =
      Typechecker.ExplicitInfer.add_type_definitions state.type_system_state
        tydefs
    in
    let backend_state' = ExBackend.process_tydef state.backend_state tydefs in
    {
      state with
      type_system_state = type_system_state';
      backend_state = backend_state';
    }

  let finalize state = ExBackend.finalize state.backend_state
end

module Evaluate : Language.BackendSignature.ExplicitT = struct
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
    | [ (x, (_ws, exp)) ] ->
        let v = Eval.eval_expression state.evaluation_state exp in
        Format.fprintf !Config.output_formatter "@[%t : %t = %t@]@."
          (Language.CoreTypes.Variable.print x)
          (Type.print_ty exp.ty) (V.print_value v);
        { evaluation_state = Eval.update x v state.evaluation_state }
    | _ -> failwith __LOC__

  let process_top_let_rec state defs =
    Assoc.iter
      (fun (f, (_ws, abs)) ->
        Format.fprintf !Config.output_formatter "@[%t : %t = <fun>@]@."
          (Language.CoreTypes.Variable.print f)
          (Type.print_ty (Type.arrow abs.ty)))
      defs;
    { evaluation_state = Eval.extend_let_rec state.evaluation_state defs }

  let load_primitive_value _state _x _prim = failwith "Not implemented"

  let load_primitive_effect _state _x _prim = failwith "Not implemented"

  let process_tydef state _ = state

  let finalize _state = ()
end

module CompileToPlainOCaml : Language.BackendSignature.ExplicitT = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  let translate_exeff_config =
    TranslateExEff2NoEff.initial_state
      {
        purity_aware_translation =
          !Config.optimizator_config.purity_aware_translation;
      }

  let translate_noeff_config =
    TranslateNoEff2Ocaml.initial_state
      {
        purity_aware_translation =
          !Config.optimizator_config.purity_aware_translation;
      }

  type state = {
    prog : SyntaxNoEff.cmd list;
    no_eff_optimizer_state : NoEffOptimizer.state;
    primitive_values :
      ( Language.CoreTypes.Variable.t,
        Language.Primitives.primitive_value )
      Assoc.t;
    primitive_effects : Term.effect list;
  }

  let initial_state =
    {
      prog = [];
      no_eff_optimizer_state =
        NoEffOptimizer.initial_state
          {
            eliminate_coercions = !Config.optimizator_config.eliminate_coercions;
            purity_aware_translation =
              !Config.optimizator_config.purity_aware_translation;
          };
      primitive_values = Assoc.empty;
      primitive_effects = [];
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
    let c' =
      optimize_term state
      @@ TranslateExEff2NoEff.elab_computation translate_exeff_config c
    in
    { state with prog = SyntaxNoEff.Term c' :: state.prog }

  let process_type_of state _ =
    (* Print.warning "[#typeof] commands are ignored when compiling to OCaml."; *)
    state

  let process_def_effect state eff =
    {
      state with
      prog =
        SyntaxNoEff.DefEffect
          (TranslateExEff2NoEff.elab_effect translate_exeff_config eff)
        :: state.prog;
    }

  let process_top_let state defs =
    let defs' =
      Assoc.kmap
        (fun (x, (ws, e)) ->
          ( x,
            ( List.map fst ws.Type.ty_constraints,
              optimize_term state
              @@ TranslateExEff2NoEff.elab_expression translate_exeff_config e
            ) ))
        defs
    in
    { state with prog = SyntaxNoEff.TopLet defs' :: state.prog }

  let process_top_let_rec state defs =
    let defs' =
      optimize_rec_definitions state
      @@ TranslateExEff2NoEff.elab_rec_definitions translate_exeff_config defs
    in
    { state with prog = SyntaxNoEff.TopLetRec defs' :: state.prog }

  let load_primitive_value state x prim =
    { state with primitive_values = Assoc.update x prim state.primitive_values }

  let load_primitive_effect state eff _prim =
    { state with primitive_effects = eff :: state.primitive_effects }

  let process_tydef state tydefs =
    let converter (ty_params, tydef) =
      (ty_params, TranslateExEff2NoEff.elab_tydef tydef)
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    { state with prog = SyntaxNoEff.TyDef tydefs' :: state.prog }

  let finalize state =
    let pp_state =
      TranslateNoEff2Ocaml.add_primitive_values translate_noeff_config
        state.primitive_values
    in
    if !Config.include_header_open then
      Format.fprintf !Config.output_formatter "open OcamlHeader;;";
    List.iter
      (fun eff ->
        let eff' = TranslateExEff2NoEff.elab_effect state eff in
        Format.fprintf !Config.output_formatter "%t (* primitive effect *)\n"
          (TranslateNoEff2Ocaml.pp_def_effect eff'))
      (List.rev state.primitive_effects);
    List.iter
      (fun cmd ->
        Format.fprintf !Config.output_formatter "%t\n"
          (TranslateNoEff2Ocaml.pp_cmd pp_state cmd))
      (List.rev state.prog)
end
