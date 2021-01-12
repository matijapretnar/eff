(* Compilation to multicore ocaml *)
open Utils
module V = Value

module Evaluate : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = {
    effect_system_state : ExplicitInfer.state;
    evaluation_state : Eval.state;
  }

  let initial_state =
    {
      effect_system_state = ExplicitInfer.initial_state;
      evaluation_state = Eval.initial_state;
    }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c _tysch =
    let c', ty' =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    let v = Eval.run state.evaluation_state c' in
    Format.fprintf !Config.output_formatter "@[- : %t = %t@]@."
      (Types.print_target_dirty ty')
      (V.print_value v);
    state

  let process_type_of state c _tysch =
    let _, ty =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    Format.fprintf Format.str_formatter "- : %t\n" (Types.print_target_dirty ty);
    (* { state with prog = Format.flush_str_formatter () :: state.prog } *)
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let effect_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
    in
    { state with effect_system_state = effect_system_state' }

  let process_top_let state _defs _vars =
    Print.debug "ignoring top let binding";
    state

  let process_top_let_rec state _ _ =
    Print.debug "ignoring top let rec binding";
    state

  let process_external state (x, ty, _name) =
    let effect_system_state' =
      ExplicitInfer.addExternal state.effect_system_state x ty
    in
    { state with effect_system_state = effect_system_state' }

  let process_tydef state tydefs =
    let effect_system_state' =
      ExplicitInfer.add_type_definitions state.effect_system_state tydefs
    in
    { state with effect_system_state = effect_system_state' }

  let finalize state =
    (* List.iter
       (fun x -> Format.fprintf !Config.output_formatter "%s\n" x)
       (List.rev state.prog) *)
    ()
end

module CompileToPlainOCaml : Language.BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type state = {
    effect_system_state : ExplicitInfer.state;
    typechecker_state : TypeChecker.state;
    prog : SyntaxOcaml.cmd list;
  }

  let initial_state =
    {
      effect_system_state = ExplicitInfer.initial_state;
      typechecker_state = TypeChecker.initial_state;
      prog = [];
    }

  let process_type state ty =
    TranslateNoEff2Ocaml.elab_type
      (snd
         (TranslateExEff2NoEff.type_elab state.effect_system_state
            state.typechecker_state
            (Types.source_to_target state.effect_system_state.tctx_st ty)))

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c _tysch =
    let c', _ty' =
      ExplicitInfer.tcTopLevelMono ~loc:Location.unknown
        state.effect_system_state c
    in
    let c'' =
      if !Config.disable_optimization then c'
      else Optimizer.optimize_main_comp state.typechecker_state c'
    in
    let _, c''' =
      TranslateExEff2NoEff.comp_elab state.effect_system_state
        state.typechecker_state c''
    in
    let c'''' = TranslateNoEff2Ocaml.elab_term c''' in
    { state with prog = SyntaxOcaml.Term c'''' :: state.prog }

  let process_type_of state c _tysch =
    Print.warning "[#typeof] commands are ignored when compiling to OCaml.";
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let effect_system_state' =
      ExplicitInfer.add_effect eff (ty1, ty2) state.effect_system_state
    in
    {
      state with
      effect_system_state = effect_system_state';
      prog =
        SyntaxOcaml.DefEffect
          (eff, process_type state ty1, process_type state ty2)
        :: state.prog;
    }

  let process_top_let state _defs _vars =
    failwith "Top level bindings not supported"

  let process_top_let_rec state _ _ =
    failwith "Top level bindings not supported"

  let process_external state (x, ty, name) =
    let effect_system_state' =
      ExplicitInfer.addExternal state.effect_system_state x ty
    in
    {
      state with
      effect_system_state = effect_system_state';
      prog = SyntaxOcaml.External (x, process_type state ty, name) :: state.prog;
    }

  let process_tydef state tydefs =
    let effect_system_state' =
      ExplicitInfer.add_type_definitions state.effect_system_state tydefs
    in
    let converter (ty_params, tydef) =
      ( ty_params,
        TranslateNoEff2Ocaml.elab_tydef (TranslateExEff2NoEff.elab_tydef tydef)
      )
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    {
      state with
      effect_system_state = effect_system_state';
      prog = SyntaxOcaml.TyDef tydefs' :: state.prog;
    }

  let finalize state =
    Format.fprintf !Config.output_formatter "%s" OcamlHeader_ml.source;
    List.iter
      (fun cmd ->
        Format.fprintf !Config.output_formatter "%t\n"
          (SyntaxOcaml.print_command cmd))
      (List.rev state.prog)
end
