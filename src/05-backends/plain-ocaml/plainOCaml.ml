(* Compilation to multicore ocaml *)
open Utils
module Term = Language.Term
module Type = Language.Type

module Backend : Language.Backend.S = struct
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
    prog : (SyntaxNoEff.cmd * Language.Constraints.t list) list;
    no_eff_optimizer_state : NoEffOptimizer.state;
    primitive_values :
      (Language.Term.Variable.t, Language.Primitives.primitive_value) Assoc.t;
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

  let optimize_top_rec_definitions state defs =
    let defs' =
      if !Config.enable_optimization then
        NoEffOptimizer.optimize_top_rec_definitions state.no_eff_optimizer_state
          defs
      else defs
    in
    defs'

  let process_computation state (_, c, cnstrs) =
    let c' =
      optimize_term state
      @@ TranslateExEff2NoEff.elab_computation translate_exeff_config c
    in
    {
      state with
      prog =
        (SyntaxNoEff.Term (TranslateExEff2NoEff.elab_constraints cnstrs, c'), [])
        :: state.prog;
    }

  let process_type_of state _ =
    (* Print.warning "[#typeof] commands are ignored when compiling to OCaml."; *)
    state

  let process_def_effect state eff =
    {
      state with
      prog =
        (SyntaxNoEff.DefEffect (TranslateExEff2NoEff.elab_effect eff), [])
        :: state.prog;
    }

  let process_top_let state defs =
    let constraints, defs' =
      List.fold_map
        (fun constraints (pat, _params, cnstrs, comp) ->
          ( cnstrs :: constraints,
            ( TranslateExEff2NoEff.elab_pattern translate_exeff_config pat,
              TranslateExEff2NoEff.elab_constraints cnstrs,
              optimize_term state
              @@ TranslateExEff2NoEff.elab_computation translate_exeff_config
                   comp ) ))
        [] defs
    in
    { state with prog = (SyntaxNoEff.TopLet defs', constraints) :: state.prog }

  let process_top_let_rec state defs =
    let constraints =
      defs |> Assoc.values_of |> List.map (fun (_, c, _) -> c)
    in
    let defs' =
      optimize_top_rec_definitions state
      @@ TranslateExEff2NoEff.elab_top_rec_definitions translate_exeff_config
           defs
    in
    {
      state with
      prog = (SyntaxNoEff.TopLetRec defs', constraints) :: state.prog;
    }

  let load_primitive_value state x prim =
    { state with primitive_values = Assoc.update x prim state.primitive_values }

  let load_primitive_effect state eff _prim =
    { state with primitive_effects = eff :: state.primitive_effects }

  let process_tydef state tydefs =
    let converter Type.{ params; type_def } =
      ( Type.TyParam.Map.bindings params.type_params |> List.map fst,
        TranslateExEff2NoEff.elab_tydef type_def )
    in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    { state with prog = (SyntaxNoEff.TyDef tydefs', []) :: state.prog }

  let finalize state =
    let pp_state =
      TranslateNoEff2Ocaml.add_primitive_values translate_noeff_config
        state.primitive_values
    in
    if !Config.include_header_open then
      Format.fprintf !Config.output_formatter "open OcamlHeader;;";
    List.iter
      (fun eff ->
        let eff' = TranslateExEff2NoEff.elab_effect eff in
        Format.fprintf !Config.output_formatter "(* primitive effect *) %t\n"
          (TranslateNoEff2Ocaml.pp_def_effect eff'))
      (List.rev state.primitive_effects);
    List.iter
      (fun (cmd, constraints) ->
        Format.fprintf !Config.output_formatter "%t\n"
          (TranslateNoEff2Ocaml.pp_cmd pp_state cmd);
        match constraints with
        | _ when !Config.print_graph ->
            List.iter
              (fun c ->
                Format.fprintf !Config.output_formatter
                  "(* Constraints graph:\n %t \n*)"
                  (Language.Constraints.print_dot c))
              constraints
        | _ -> ())
      (List.rev state.prog)
end
