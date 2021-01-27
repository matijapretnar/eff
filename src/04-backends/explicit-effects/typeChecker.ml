type state = TranslateExEff2NoEff.state

let initial_state = TranslateExEff2NoEff.initial_state

let check_expression st c = fst @@ TranslateExEff2NoEff.elab_expression st c

let check_computation st c = fst @@ TranslateExEff2NoEff.elab_computation st c

let check_dirt_coercion st omega =
  TranslateExEff2NoEff.elab_dirt_coercion st omega

let check_ty_coercion st omega =
  fst @@ TranslateExEff2NoEff.elab_ty_coercion st omega

let check_dirty_coercion st omega =
  fst @@ TranslateExEff2NoEff.elab_dirty_coercion st omega

let check_abstraction st a = fst @@ TranslateExEff2NoEff.elab_abstraction st a

let check_handler st h =
  match check_expression st (Term.Handler h) with
  | Type.Handler (drty_in, drty_out) -> (drty_in, drty_out)
  | _ -> assert false

let add_external = TranslateExEff2NoEff.extend_var_types

let extend_var_types = add_external

let extend_pattern_type = TranslateExEff2NoEff.extend_pattern_type

let extend_ty_params = TranslateExEff2NoEff.extend_ty_params

let extend_dirt_params = TranslateExEff2NoEff.extend_dirt_params

let extend_skel_params = TranslateExEff2NoEff.extend_skel_params

let extend_ty_coer_types = TranslateExEff2NoEff.extend_ty_coer_types

let extend_dirt_coer_types = TranslateExEff2NoEff.extend_dirt_coer_types

let extend_ty_param_skeletons = TranslateExEff2NoEff.extend_ty_param_skeletons
