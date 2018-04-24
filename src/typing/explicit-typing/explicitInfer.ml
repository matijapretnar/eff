module Untyped = CoreSyntax
open Typed

(* INFERENCE STATE *)

type state =
  { context: TypingEnv.t
  ; effects: (Types.target_ty * Types.target_ty) Untyped.EffectMap.t }

let empty = {context= TypingEnv.empty; effects= CoreSyntax.EffectMap.empty}

let add_def env x ty_sch =
  {env with context= TypingEnv.update env.context x ty_sch}


let apply_sub_to_env env sub =
  {env with context= TypingEnv.apply_sub env.context sub}


let extend_env vars env =
  List.fold_right
    (fun (x, ty_sch) env ->
      {env with context= TypingEnv.update env.context x ty_sch} )
    vars env


let print_env env =
  List.map
    (fun (x, ty_sch) ->
      Print.debug "%t : %t" (Typed.print_variable x)
        (Types.print_target_ty ty_sch) )
    env


let add_effect eff (ty1, ty2) st =
  let ty1 = Types.source_to_target ty1 in
  let ty2 = Types.source_to_target ty2 in
  {st with effects= EffectMap.add eff (ty1, ty2) st.effects}


(* INFERENCE *)

let rec type_pattern p = type_plain_pattern p.Untyped.term

and type_plain_pattern = function
  | Untyped.PVar x -> Typed.PVar x
  | Untyped.PAs (p, x) -> Typed.PAs (type_pattern p, x)
  | Untyped.PNonbinding -> Typed.PNonbinding
  | Untyped.PConst const -> Typed.PConst const
  | Untyped.PTuple ps -> Typed.PTuple (List.map type_pattern ps)
  | Untyped.PRecord [] -> assert false
  | Untyped.PRecord ((fld, _) :: _ as lst) -> failwith __LOC__
  | Untyped.PVariant (lbl, p) -> failwith __LOC__


(*

     ===========================
     Q; Γ ⊢ p : A ~> p' ⊣ Γ'; Q' 
     ===========================

  ---------------------------------
  Q; Γ ⊢ x : A ~> x ⊣ Γ,x:α; Q

  ---------------------------------
  Q; Γ ⊢ _ : A ~> _ ⊣ Γ; Q

  ⊢ c : B
  ------------------------------------ [we don't use ω, we just force the types to be equal]
  Q; Γ ⊢ c : A ~> c ⊣ Γ; Q, ω : B <: A

 *)
let rec type_typed_pattern in_cons st pat ty =
  type_plain_typed_pattern in_cons st pat.Untyped.term ty


and type_plain_typed_pattern in_cons st pat ty =
  match pat with
  | Untyped.PVar x ->
      let st' = add_def st x ty in
      (Typed.PVar x, st', in_cons)
  | Untyped.PNonbinding -> (Typed.PNonbinding, st, in_cons)
  | Untyped.PAs (p, v) -> failwith __LOC__
  | Untyped.PTuple l -> failwith __LOC__
  | Untyped.PRecord r -> failwith __LOC__
  | Untyped.PVariant (lbl, p) -> (
      let ty_in, ty_out = Types.constructor_signature lbl in
      let _omega, q = Typed.fresh_ty_coer (ty_out, ty) in
      let cons' = q :: in_cons in
      match p with
      | None -> (Typed.PVariant (lbl, Typed.PTuple []), st, cons')
      | Some p ->
          let p', st', cons'' = type_typed_pattern cons' st p ty_in in
          (Typed.PVariant (lbl, p'), st', cons') )
  | Untyped.PConst c ->
      let _omega, q = Typed.fresh_ty_coer (Types.type_const c, ty) in
      (Typed.PConst c, st, q :: in_cons)


(* ... *)

let rec state_free_ty_vars st =
  List.fold_right
    (fun (_, ty) acc -> Types.TyParamSet.union (Types.free_ty_vars_ty ty) acc)
    st Types.TyParamSet.empty


let rec state_free_dirt_vars st =
  List.fold_right
    (fun (_, ty) acc ->
      Types.DirtParamSet.union (Types.free_dirt_vars_ty ty) acc )
    st Types.DirtParamSet.empty


let splitter st constraints simple_ty =
  let skel_list = OldUtils.uniq (get_skel_vars_from_constraints constraints) in
  let global_ty_vars = state_free_ty_vars st in
  let global_dirt_vars = state_free_dirt_vars st in
  let local_constraints =
    List.filter
      (fun cons ->
        let cons_freevars_ty = constraint_free_ty_vars cons in
        let cons_freevars_dirt = constraint_free_dirt_vars cons in
        let is_sub_ty =
          Types.TyParamSet.subset cons_freevars_ty global_ty_vars
        in
        let is_sub_dirt =
          Types.DirtParamSet.subset cons_freevars_dirt global_dirt_vars
        in
        not (is_sub_ty && is_sub_dirt) )
      constraints
  in
  let free_ty_params =
    let simple_ty_freevars_ty = Types.free_ty_vars_ty simple_ty
    and constraints_freevars_ty =
      List.fold_right
        (fun cons acc ->
          Types.TyParamSet.union (constraint_free_ty_vars cons) acc )
        constraints Types.TyParamSet.empty
    in
    Types.TyParamSet.diff
      (Types.TyParamSet.union constraints_freevars_ty simple_ty_freevars_ty)
      global_ty_vars
  in
  let free_dirt_params =
    let simple_ty_freevars_dirt = Types.free_dirt_vars_ty simple_ty
    and constraints_freevars_dirt =
      List.fold_right
        (fun cons acc ->
          Types.DirtParamSet.union (constraint_free_dirt_vars cons) acc )
        constraints Types.DirtParamSet.empty
    in
    Types.DirtParamSet.diff
      (Types.DirtParamSet.union constraints_freevars_dirt
         simple_ty_freevars_dirt)
      global_dirt_vars
  in
  let global_constraints =
    List.filter
      (function
          | Typed.TyParamHasSkel (tyvar, skvar) ->
              not (Types.TyParamSet.mem tyvar free_ty_params)
          | cons -> not (List.mem cons local_constraints))
      constraints
  in
  let result =
    ( skel_list
    , Types.TyParamSet.elements free_ty_params
    , Types.DirtParamSet.elements free_dirt_params
    , local_constraints
    , global_constraints )
  in
  Print.debug "Splitter Input Constraints: " ;
  Unification.print_c_list constraints ;
  Print.debug "Splitter Input Ty: %t" (Types.print_target_ty simple_ty) ;
  Print.debug "Splitter Env :" ;
  print_env st ;
  Print.debug "Simple type free vars: " ;
  Types.TyParamSet.iter
    (fun x -> Print.debug "%t" (Params.Ty.print x))
    (Types.free_ty_vars_ty simple_ty) ;
  Print.debug "state free vars: " ;
  Types.TyParamSet.iter
    (fun x -> Print.debug "%t" (Params.Ty.print x))
    (state_free_ty_vars st) ;
  Print.debug "Splitter output free_ty_vars: " ;
  Types.TyParamSet.iter
    (fun x -> Print.debug "%t" (Params.Ty.print x))
    free_ty_params ;
  Print.debug "Splitter output free_dirt_vars: " ;
  Types.DirtParamSet.iter
    (fun x -> Print.debug "%t" (Params.Dirt.print x))
    free_dirt_params ;
  Print.debug "Splitter global constraints list :" ;
  Unification.print_c_list local_constraints ;
  Print.debug "Splitter global constraints list :" ;
  Unification.print_c_list global_constraints ;
  result


let generalize_type st constraints simple_ty ty =
  let free_skel_vars, free_ty_vars, free_dirt_vars, split_cons1, split_cons2 =
    splitter st constraints simple_ty
  in
  let qual_ty =
    List.fold_right
      (fun cons acc ->
        match cons with
        | Typed.TyOmega (_, t) -> Types.QualTy (t, acc)
        | Typed.DirtOmega (_, t) -> Types.QualDirt (t, acc) )
      split_cons1 ty
  in
  let ty_sc_dirt =
    List.fold_right
      (fun cons acc -> Types.TySchemeDirt (cons, acc))
      free_dirt_vars qual_ty
  in
  let ty_sc_ty =
    List.fold_right
      (fun cons acc ->
        Types.TySchemeTy
          (cons, Unification.get_skel_of_tyvar cons constraints, acc) )
      free_ty_vars ty_sc_dirt
  in
  let ty_sc_skel =
    List.fold_right
      (fun cons acc -> Types.TySchemeSkel (cons, acc))
      free_skel_vars ty_sc_ty
  in
  ty_sc_skel


let rec get_sub_of_ty ty_sch =
  match ty_sch with
  | Types.TySchemeSkel (s, t) ->
      let new_s = Params.Skel.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      ((s, new_s) :: skels, tys, dirts, tycos, dcos)
  | Types.TySchemeTy (p, _, t) ->
      let new_p = Params.Ty.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, (p, new_p) :: tys, dirts, tycos, dcos)
  | Types.TySchemeDirt (p, t) ->
      let new_p = Params.Dirt.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, tys, (p, new_p) :: dirts, tycos, dcos)
  | Types.QualTy ((p, ct), t) ->
      let new_p = Params.TyCoercion.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, tys, dirts, (p, new_p) :: tycos, dcos)
  | Types.QualDirt ((p, ct), t) ->
      let new_p = Params.DirtCoercion.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, tys, dirts, tycos, (p, new_p) :: dcos)
  | _ -> ([], [], [], [], [])


let rec get_basic_type ty_sch =
  match ty_sch with
  | Types.TySchemeSkel (_, t) -> get_basic_type t
  | Types.TySchemeTy (typ, sk, t) ->
      let a, b = get_basic_type t in
      ((typ, sk) :: a, b)
  | Types.TySchemeDirt (_, t) -> get_basic_type t
  | Types.QualTy (_, t) -> get_basic_type t
  | Types.QualDirt (_, t) -> get_basic_type t
  | t -> ([], t)


let rec get_applied_cons_from_ty ty_subs dirt_subs ty =
  match ty with
  | Types.TySchemeSkel (_, t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.TySchemeTy (_, _, t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.TySchemeDirt (_, t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.QualTy (cons, t) ->
      let c1, c2 = get_applied_cons_from_ty ty_subs dirt_subs t in
      let ty1, ty2 = cons in
      let newty1, newty2 =
        ( apply_sub_to_type ty_subs dirt_subs ty1
        , apply_sub_to_type ty_subs dirt_subs ty2 )
      in
      let new_omega = Params.TyCoercion.fresh () in
      let new_cons = Typed.TyOmega (new_omega, (newty1, newty2)) in
      (new_cons :: c1, c2)
  | Types.QualDirt (cons, t) ->
      let c1, c2 = get_applied_cons_from_ty ty_subs dirt_subs t in
      let ty1, ty2 = cons in
      let newty1, newty2 =
        (apply_sub_to_dirt dirt_subs ty1, apply_sub_to_dirt dirt_subs ty2)
      in
      let new_omega = Params.DirtCoercion.fresh () in
      let new_cons = Typed.DirtOmega (new_omega, (newty1, newty2)) in
      (c1, new_cons :: c2)
  | _ -> ([], [])


let rec get_skel_constraints alphas_has_skels ty_subs skel_subs =
  match alphas_has_skels with
  | (tvar, skel) :: ss ->
      let new_skel = Unification.apply_substitution_skel skel_subs skel in
      let Some new_tyvar = OldUtils.lookup tvar ty_subs in
      Typed.TyParamHasSkel (new_tyvar, new_skel)
      :: get_skel_constraints ss ty_subs skel_subs
  | [] -> []


let apply_types alphas_has_skels skel_subs ty_subs dirt_subs var ty_sch =
  let new_skel_subs =
    List.map
      (fun (a, b) -> Unification.SkelParamToSkel (a, Types.SkelParam b))
      skel_subs
  in
  let skel_constraints =
    get_skel_constraints alphas_has_skels ty_subs new_skel_subs
  in
  let skel_apps =
    List.fold_left
      (fun a (_, b) -> Typed.ApplySkelExp (a, Types.SkelParam b))
      (Typed.Var var) skel_subs
  in
  let ty_apps =
    List.fold_left
      (fun a (_, b) -> Typed.ApplyTyExp (a, Types.TyParam b))
      skel_apps ty_subs
  in
  let dirt_apps =
    List.fold_left
      (fun a (_, b) -> Typed.ApplyDirtExp (a, Types.no_effect_dirt b))
      ty_apps dirt_subs
  in
  let ty_cons, dirt_cons = get_applied_cons_from_ty ty_subs dirt_subs ty_sch in
  let ty_cons_apps =
    List.fold_left
      (fun a (Typed.TyOmega (omega, _)) ->
        Typed.ApplyTyCoercion (a, Typed.TyCoercionVar omega) )
      dirt_apps ty_cons
  in
  let dirt_cons_apps =
    List.fold_left
      (fun a (Typed.DirtOmega (omega, _)) ->
        Typed.ApplyDirtCoercion (a, Typed.DirtCoercionVar omega) )
      ty_cons_apps dirt_cons
  in
  (dirt_cons_apps, skel_constraints @ ty_cons @ dirt_cons)


let apply_polymorphic_variable x ty_schi =
  let ( bind_skelvar_sub
      , bind_tyvar_sub
      , bind_dirtvar_sub
      , bind_tyco_sub
      , bind_dco_sub ) =
    get_sub_of_ty ty_schi
  in
  let alphas_has_skels, basic_type = get_basic_type ty_schi in
  let applied_basic_type =
    apply_sub_to_type bind_tyvar_sub bind_dirtvar_sub basic_type
  in
  let returned_x, returned_cons =
    apply_types alphas_has_skels bind_skelvar_sub bind_tyvar_sub
      bind_dirtvar_sub x ty_schi
  in
  Print.debug "returned: %t" (Typed.print_expression returned_x) ;
  Print.debug "original_type: %t" (Types.print_target_ty ty_schi) ;
  Print.debug "returned_type: %t" (Types.print_target_ty applied_basic_type) ;
  (returned_x, applied_basic_type, returned_cons)


let rec type_expression in_cons st ({Untyped.term= expr} as e) =
  Print.debug "type_expression: %t" (CoreSyntax.print_expression e) ;
  Print.debug "### Constraints Before ###" ;
  Unification.print_c_list in_cons ;
  Print.debug "##########################" ;
  let e, ttype, constraints, sub_list =
    type_plain_expression in_cons st expr
  in
  Print.debug "### Constraints After ####" ;
  Unification.print_c_list constraints ;
  Print.debug "##########################" ;
  (e, ttype, constraints, sub_list)


and type_plain_expression in_cons st = function
  | Untyped.Var x -> (
    match TypingEnv.lookup st.context x with
    | Some ty_schi ->
        let returned_x, applied_basic_type, returned_cons =
          apply_polymorphic_variable x ty_schi
        in
        (returned_x, applied_basic_type, returned_cons @ in_cons, [])
    | None ->
        Print.debug "Variable not found: %t" (Typed.print_variable x) ;
        assert false )
  | Untyped.Const const ->
      (Typed.Const const, Types.type_const const, in_cons, [])
  | Untyped.Tuple es ->
      let target_list = List.map (type_expression in_cons st) es in
      let target_terms =
        Typed.Tuple
          (List.fold_right (fun (x, _, _, _) xs -> x :: xs) target_list [])
      in
      let target_types =
        Types.Tuple
          (List.fold_right (fun (_, x, _, _) xs -> x :: xs) target_list [])
      in
      let target_cons =
        List.fold_right
          (fun (_, _, x, _) xs -> List.append x xs)
          target_list []
      in
      let target_sub =
        List.fold_right
          (fun (_, _, _, x) xs -> List.append x xs)
          target_list []
      in
      (target_terms, target_types, in_cons @ target_cons, target_sub)
  | Untyped.Record lst -> failwith __LOC__
  | Untyped.Variant (lbl, e) -> (
      let ty_in, ty_out = Types.constructor_signature lbl in
      match e with
      | None -> (Typed.Variant (lbl, Typed.Tuple []), ty_out, in_cons, [])
      | Some e ->
          let e', u', cons', subs = type_expression in_cons st e in
          let e'', cast_cons = cast_expression e' u' ty_in in
          (Typed.Variant (lbl, e''), ty_out, cast_cons :: cons', subs) )
  | Untyped.Lambda a ->
      Print.debug "in infer lambda" ;
      let in_ty, in_ty_skel = Typed.fresh_ty_with_fresh_skel () in
      let (p, c), (ty, dty), cons, sub =
        type_abstraction (in_ty_skel :: in_cons) st a in_ty
      in
      let target_ty = Types.Arrow (ty, dty) in
      let target_lambda =
        Typed.Lambda
          (abstraction_with_ty p
             (Unification.apply_substitution_ty sub in_ty)
             c)
      in
      Unification.print_c_list cons ;
      Print.debug "lambda ty: %t" (Types.print_target_ty target_ty) ;
      (target_lambda, target_ty, cons, sub)
  | Untyped.Effect eff ->
      let in_ty, out_ty = Untyped.EffectMap.find eff st.effects in
      let s = Types.EffectSet.singleton eff in
      ( Typed.Effect (eff, (in_ty, out_ty))
      , Types.Arrow (in_ty, (out_ty, Types.closed_dirt s))
      , in_cons
      , [] )
  | Untyped.Handler h ->
      let out_dirt_var = Params.Dirt.fresh () in
      let in_dirt = Types.fresh_dirt ()
      and out_dirt = Types.no_effect_dirt out_dirt_var
      and in_ty, skel_cons_in = Typed.fresh_ty_with_fresh_skel ()
      and out_ty, skel_cons_out = Typed.fresh_ty_with_fresh_skel () in
      let target_type = Types.Handler ((in_ty, in_dirt), (out_ty, out_dirt)) in
      let r_ty, r_ty_skel_cons = Typed.fresh_ty_with_fresh_skel () in
      let r_cons = r_ty_skel_cons :: in_cons in
      let pr, cr = h.value_clause in
      let Untyped.PVar x = pr.Untyped.term in
      let r_st = add_def st x r_ty in
      let ( target_cr_term
          , (target_cr_ty, target_cr_dirt)
          , target_cr_cons
          , target_cr_sub ) =
        type_computation r_cons r_st cr
      in
      let r_subbed_st = apply_sub_to_env st target_cr_sub in
      let folder 
          (*
          (acc_terms, acc_tys, acc_st, acc_cons, acc_subs, acc_alpha_delta_i)
          (eff, abs2) =
   *)
          (eff, abs2)
          (acc_terms, acc_tys, acc_st, acc_cons, acc_subs, acc_alpha_delta_i) =
        let ( typed_c_op
            , typed_co_op_ty
            , s_st
            , co_op_cons
            , c_op_sub
            , (alpha_i, delta_i) ) =
          Print.debug "type_effect_clause: %t" (CoreSyntax.abstraction2 abs2) ;
          type_effect_clause eff abs2 acc_st acc_cons acc_subs
        in
        ( typed_c_op :: acc_terms
        , typed_co_op_ty :: acc_tys
        , s_st
        , co_op_cons (* @ acc_cons *)
        , c_op_sub @ acc_subs
        , (alpha_i, delta_i) :: acc_alpha_delta_i )
      in
      (*
      let folder_function =
        List.fold_left folder ([], [], r_subbed_st, target_cr_cons, [], [])
          h.effect_clauses
      in
*)
      let folder_function =
        List.fold_right folder h.effect_clauses
          ([], [], r_subbed_st, target_cr_cons, [], [])
      in
      let typed_op_terms, typed_op_terms_ty, _, cons_n, subs_n, alpha_delta_i_s =
        folder_function
      in
      let cons_1 =
        ( Unification.apply_substitution_ty (target_cr_sub @ subs_n)
            target_cr_ty
        , out_ty )
      in
      let cons_2 =
        (Unification.apply_substitution_dirt subs_n target_cr_dirt, out_dirt)
      in
      let omega_1, omega_cons_1 = Typed.fresh_ty_coer cons_1
      and omega_2, omega_cons_2 = Typed.fresh_dirt_coer cons_2 in
      let y_var_name = Typed.Variable.fresh "fresh_var" in
      let y = Typed.PVar y_var_name in
      let annot_y = y in
      let exp_y = Typed.Var y_var_name in
      let coerced_y, omega_cons_6 =
        Typed.cast_expression exp_y in_ty
          (Unification.apply_substitution_ty (target_cr_sub @ subs_n) r_ty)
      in
      let substituted_c_r =
        Typed.subst_comp [(x, coerced_y)]
          (Unification.apply_substitution subs_n target_cr_term)
      in
      let coerced_substiuted_c_r =
        Typed.CastComp (substituted_c_r, Typed.BangCoercion (omega_1, omega_2))
      in
      let mapper (op_term, (op_term_ty, op_term_dirt), (alpha_i, delta_i))
          (eff, abs2) =
        let in_op_ty, out_op_ty = Untyped.EffectMap.find eff st.effects in
        let x, k, c_op = abs2 in
        let Untyped.PVar k_var = k.Untyped.term in
        let cons_3 =
          (Unification.apply_substitution_ty subs_n op_term_ty, out_ty)
        in
        let cons_4 =
          (Unification.apply_substitution_dirt subs_n op_term_dirt, out_dirt)
        in
        let cons_5a = Types.Arrow (out_op_ty, (out_ty, out_dirt)) in
        let cons_5b =
          Types.Arrow
            ( out_op_ty
            , ( Unification.apply_substitution_ty subs_n alpha_i
              , Unification.apply_substitution_dirt subs_n delta_i ) )
        in
        let omega_3, omega_cons_3 = Typed.fresh_ty_coer cons_3 in
        let omega_4, omega_cons_4 = Typed.fresh_dirt_coer cons_4 in
        let l_var_name = Typed.Variable.fresh "fresh_var" in
        let l = Typed.PVar l_var_name in
        let annot_l = l in
        let exp_l = Typed.Var l_var_name in
        let coerced_l, omega_cons_5 =
          Typed.cast_expression exp_l cons_5a cons_5b
        in
        let substituted_c_op =
          Typed.subst_comp [(k_var, coerced_l)]
            (Unification.apply_substitution subs_n op_term)
        in
        Print.debug "substituted_c_op [%t/%t]: %t"
          (CoreSyntax.Variable.print ~safe:true l_var_name)
          (CoreSyntax.Variable.print ~safe:true k_var)
          (Typed.print_computation substituted_c_op) ;
        let coerced_substiuted_c_op =
          Typed.CastComp
            (substituted_c_op, Typed.BangCoercion (omega_3, omega_4))
        in
        let target_effect = (eff, (in_op_ty, out_op_ty)) in
        ( ( target_effect
          , Typed.abstraction2 (type_pattern x) annot_l coerced_substiuted_c_op
          )
        , [omega_cons_3; omega_cons_4; omega_cons_5] )
      in
      let mapper_input_a =
        List.map2 (fun a b -> (a, b)) typed_op_terms typed_op_terms_ty
      in
      let mapper_input =
        List.map2 (fun (a, b) c -> (a, b, c)) mapper_input_a alpha_delta_i_s
      in
      let new_op_clauses_with_cons =
        List.map2 mapper mapper_input h.effect_clauses
      in
      let new_op_clauses =
        List.map (fun (x, y) -> x) new_op_clauses_with_cons
      in
      let ops_cons =
        OldUtils.flatten_map (fun (x, y) -> y) new_op_clauses_with_cons
      in
      let y_type =
        Unification.apply_substitution_ty (target_cr_sub @ subs_n) r_ty
      in
      let typed_value_clause =
        Typed.abstraction_with_ty annot_y y_type coerced_substiuted_c_r
      in
      let target_handler =
        {Typed.effect_clauses= new_op_clauses; value_clause= typed_value_clause}
      in
      let typed_handler = Typed.Handler target_handler in
      let for_set_handlers_ops =
        List.map (fun ((eff, (_, _)), _) -> eff) new_op_clauses
      in
      let ops_set = Types.EffectSet.of_list for_set_handlers_ops in
      let handlers_ops =
        Types.{effect_set= ops_set; row= ParamRow out_dirt_var}
      in
      let cons_7 = (in_dirt, handlers_ops) in
      let omega_7, omega_cons_7 = Typed.fresh_dirt_coer cons_7 in
      let handler_in_bang = Typed.BangCoercion (Typed.ReflTy in_ty, omega_7) in
      let handler_out_bang =
        Typed.BangCoercion (Typed.ReflTy out_ty, Typed.ReflDirt out_dirt)
      in
      let handler_coercion =
        Typed.HandlerCoercion (handler_in_bang, handler_out_bang)
      in
      let coerced_handler = Typed.CastExp (typed_handler, handler_coercion) in
      let all_cons =
        [ skel_cons_in
        ; skel_cons_out
        ; omega_cons_1
        ; omega_cons_2
        ; omega_cons_6
        ; omega_cons_7 ]
        @ ops_cons @ r_cons @ cons_n
      in
      Print.debug "### Handler r_cons             ###" ;
      Unification.print_c_list r_cons ;
      Print.debug "### Handler cons_n             ###" ;
      Unification.print_c_list cons_n ;
      Print.debug "### Constraints before Handler ###" ;
      Unification.print_c_list in_cons ;
      Print.debug "#################################" ;
      Print.debug "### Constraints after Handler ###" ;
      Unification.print_c_list all_cons ;
      Print.debug "#################################" ;
      (coerced_handler, target_type, all_cons, subs_n @ target_cr_sub)


and type_computation in_cons st {Untyped.term= comp} =
  let c, ttype, constraints, sub_list =
    type_plain_computation in_cons st comp
  in
  (c, ttype, constraints, sub_list)


and type_plain_computation in_cons st = function
  | Untyped.Value e ->
      let typed_e, tt, constraints, subs_e = type_expression in_cons st e in
      let new_d_ty = (tt, Types.empty_dirt) in
      (Typed.Value typed_e, new_d_ty, constraints, subs_e)
  | Untyped.Match (e, cases) ->
      (*
           α,δ,ωi fresh

           Q;Γ ⊢ e : A | Q₀; σ₀ ~> e'

           forall i in 1..n:

             Qi₋₁;σi₋₁(Γ) ⊢ casei : A -> Bi ! Δi | Qi ; σi ~> casei'
 
             ωi : σ^n(Bi ! Δi) <:  (α ! δ)          
 
           -----------------------------------------------------------------
           Q;Γ ⊢ Match (e, cases) : σ^n(α ! δ) | σ^n(Q,Q₀,...,Qn) ~> Match (e', cases' |> ωi) 
      *)
      (* TODO: ignoring the substitutions for now *)
      let e', ty_A, cons0, sigma0 = type_expression in_cons st e in
      let ty_alpha, q_alpha = Typed.fresh_ty_with_fresh_skel () in
      let dirt_delta = Types.fresh_dirt () in
      let cases', cons1, sigma1 =
        type_cases (q_alpha :: cons0) st cases ty_A (ty_alpha, dirt_delta)
      in
      (Typed.Match (e', cases'), (ty_alpha, dirt_delta), cons1, sigma0 @ sigma1)
  | Untyped.Apply (e1, e2) ->
      Print.debug "in infer apply" ;
      let typed_e1, tt_1, constraints_1, subs_e1 =
        type_expression in_cons st e1
      in
      let st_subbed = apply_sub_to_env st subs_e1 in
      let typed_e2, tt_2, constraints_2, subs_e2 =
        type_expression constraints_1 st_subbed e2
      in
      Print.debug "e1 apply type : %t" (Types.print_target_ty tt_1) ;
      Print.debug "e2 apply type : %t" (Types.print_target_ty tt_2) ;
      let new_ty_var, cons1 = Typed.fresh_ty_with_fresh_skel () in
      let fresh_dirty_ty = Types.make_dirty new_ty_var in
      let e1_coerced, omega_cons_1 =
        Typed.cast_expression
          (Unification.apply_substitution_exp subs_e2 typed_e1)
          (Unification.apply_substitution_ty subs_e2 tt_1)
          (Types.Arrow (tt_2, fresh_dirty_ty))
      in
      ( Typed.Apply (e1_coerced, typed_e2)
      , fresh_dirty_ty
      , [cons1; omega_cons_1] @ constraints_2
      , subs_e2 @ subs_e1 )
  | Untyped.Handle (e, c) ->
      let dirty_1, cons_skel_1 = Typed.fresh_dirty_with_fresh_skel () in
      let dirty_2, cons_skel_2 = Typed.fresh_dirty_with_fresh_skel () in
      let typed_exp, exp_type, exp_constraints, sub_exp =
        type_expression in_cons st e
      in
      let st_subbed = apply_sub_to_env st sub_exp in
      let typed_comp, comp_dirty_type, comp_constraints, sub_comp =
        type_computation exp_constraints st_subbed c
      in
      let coer_exp, omega_cons_1 =
        Typed.cast_expression typed_exp
          (Unification.apply_substitution_ty sub_comp exp_type)
          (Types.Handler (dirty_1, dirty_2))
      in
      let coer_comp, cons_comp =
        Typed.cast_computation typed_comp comp_dirty_type dirty_1
      in
      let constraints =
        [cons_skel_1; cons_skel_2; omega_cons_1; cons_comp] @ comp_constraints
      in
      ( Typed.Handle (coer_exp, coer_comp)
      , dirty_2
      , constraints
      , sub_comp @ sub_exp )
  | Untyped.Let (defs, c_2) -> (
      let [(p_def, c_1)] = defs in
      match c_1.term with
      | Untyped.Value e_1 ->
          let typed_e1, type_e1, cons_e1, sub_e1 =
            type_expression in_cons st e_1
          in
          let sub_e1', cons_e1' = Unification.unify ([], [], cons_e1) in
          let typed_e1 = Unification.apply_substitution_exp sub_e1' typed_e1 in
          let st_subbed = apply_sub_to_env st (sub_e1' @ sub_e1) in
          let ( free_skel_vars
              , free_ty_vars
              , free_dirt_vars
              , split_cons1
              , global_constraints ) =
            splitter
              (TypingEnv.return_context st_subbed.context)
              cons_e1'
              (Unification.apply_substitution_ty sub_e1' type_e1)
          in
          let ty_sc_skel =
            generalize_type
              (TypingEnv.return_context st_subbed.context)
              cons_e1'
              (Unification.apply_substitution_ty sub_e1' type_e1)
              (Unification.apply_substitution_ty sub_e1' type_e1)
          in
          let Untyped.PVar x = p_def.Untyped.term in
          let new_st = add_def st_subbed x ty_sc_skel in
          let typed_c2, type_c2, cons_c2, subs_c2 =
            type_computation global_constraints new_st c_2
          in
          let var_exp =
            List.fold_right
              (fun cons acc ->
                match cons with
                | Typed.TyOmega (om, t) -> Typed.LambdaTyCoerVar (om, t, acc)
                | Typed.DirtOmega (om, t) ->
                    Typed.LambdaDirtCoerVar (om, t, acc) )
              split_cons1 typed_e1
          in
          let var_exp_dirt_lamda =
            List.fold_right
              (fun cons acc -> Typed.BigLambdaDirt (cons, acc))
              free_dirt_vars var_exp
          in
          let var_exp_ty_lambda =
            List.fold_right
              (fun cons acc ->
                Typed.BigLambdaTy
                  (cons, Unification.get_skel_of_tyvar cons cons_e1', acc) )
              free_ty_vars var_exp_dirt_lamda
          in
          let var_exp_skel_lamda =
            List.fold_right
              (fun cons acc -> Typed.BigLambdaSkel (cons, acc))
              free_skel_vars var_exp_ty_lambda
          in
          let return_term =
            Typed.LetVal
              ( var_exp_skel_lamda
              , Typed.abstraction_with_ty (Typed.PVar x) ty_sc_skel typed_c2 )
          in
          (return_term, type_c2, cons_c2, subs_c2 @ sub_e1' @ sub_e1)
      | _ ->
          let typed_c1, (type_c1, dirt_c1), cons_c1, subs_c1 =
            type_computation in_cons st c_1
          in
          let typed_pattern, new_st, cons_c1 =
            type_typed_pattern cons_c1
              (apply_sub_to_env st subs_c1)
              p_def type_c1
          in
          let typed_c2, (type_c2, dirt_c2), cons_c2, subs_c2 =
            type_computation cons_c1 new_st c_2
          in
          let new_dirt_var = Types.fresh_dirt () in
          let ty_c1 = Unification.apply_substitution_ty subs_c2 type_c1 in
          let coer_c1, omega_cons_1 =
            Typed.cast_computation
              (Unification.apply_substitution subs_c2 typed_c1)
              (ty_c1, Unification.apply_substitution_dirt subs_c1 dirt_c1)
              (ty_c1, new_dirt_var)
          in
          let coer_c2, omega_cons_2 =
            Typed.cast_computation typed_c2 (type_c2, dirt_c2)
              (type_c2, new_dirt_var)
          in
          let abstraction = (typed_pattern, coer_c2) in
          let constraints = [omega_cons_1; omega_cons_2] @ cons_c2 in
          ( Typed.Bind (coer_c1, abstraction)
          , (type_c2, new_dirt_var)
          , constraints
          , subs_c2 @ subs_c1 ) )
  | Untyped.LetRec ([(var, abs)], c2)
    when not (Untyped.contains_variable_abs var abs) ->
      failwith __LOC__
  | Untyped.LetRec ([(var, abs)], c2) ->
      (*

         α, β, δ, ς₁, ς₂ fresh
         Q₁,α:ς₁,β:ς₂ ; Γ, (f : α -> β ! δ), (x : α) |- c₁ : A₁ ! Δ₁ | Q₂; σ₁ ~> c₁'

         (σ₂,Q₃) = solve(●;●;Q₂,ω₁:A₁<=β,ω₂:Δ₁<=δ)
         (ςs,αs:τs,δѕ,ωs:πs,Q₅) = split(σ₂(σ₁(Γ)), Q₃, σ₂(A₁))
         c1'' = σ₂(σ₁([f ςs αs δѕ ωs |> <α> -> ω₁ ! ω₂ / f]c1'))
         Q₅; σ₂(σ₁(Γ)), (f : ∀ςs.∀(αs:τs).∀δѕ.πs=>σ₂(σ₁(α))->σ₂(A₁!Δ₁) |- c₂: A₂ ! Δ₂ | Q₆; σ₃ ~> c₂'
         -------------------------------------------------------------------------------------------
         Q₁; Γ |- let rec f x = c₁ in c₂ : A₂ ! Δ₂ | Q₆; σ₃.σ₂.σ₁
           ~> let rec f = σ₃(Λςs.Λ(αs:τs).Λδѕ.λ(ωs:πs).fun x : σ₃(σ₂(σ₁(α))) -> c₁'') in c₂'

       *)
      let ty_a, q_a = fresh_ty_with_fresh_skel () in
      let ty_b, q_b = fresh_ty_with_fresh_skel () in
      let dirt_d = Types.fresh_dirt () in
      let st1 = add_def st var (Types.Arrow (ty_a, (ty_b, dirt_d))) in
      let cons1 = q_a :: q_b :: in_cons in
      let (pat', c1'), (ty_a', (ty_A1, dirt_D1)), cons2, sub_s1 =
        type_abstraction cons1 st1 abs ty_a
      in
      let tyco1, q_ty = fresh_ty_coer (ty_A1, ty_b) in
      let dco2, q_d = Typed.fresh_dirt_coer (dirt_D1, dirt_d) in
      let sub_s2, cons3 = Unification.unify ([], [], q_ty :: q_d :: cons2) in
      let st2 = apply_sub_to_env st (sub_s1 @ sub_s2) in
      let ty_A1' = Unification.apply_substitution_ty sub_s2 ty_A1 in
      let arrow_type = Types.Arrow (ty_a', (ty_A1', dirt_D1)) in
      let skvars, tyvars, dirtvars, cons4, cons5 =
        splitter (TypingEnv.return_context st2.context) cons3 ty_A1'
      in
      let ty_f =
        generalize_type
          (TypingEnv.return_context st2.context)
          cons3 ty_A1'
          (Unification.apply_substitution_ty sub_s2 arrow_type)
      in
      let st3 = add_def st2 var ty_f in
      let c2', dty2, cons6, sub_s3 = type_computation cons5 st3 c2 in
      let ty_f' = Unification.apply_substitution_ty sub_s3 ty_f in
      let e_rec =
        (* f ςs αs δѕ ωs |> <α> -> ω₁ ! ω₂ *)
        Typed.CastExp
          ( List.fold_left
              (fun e q ->
                match q with
                | Typed.TyOmega (tycovar, ct) ->
                    Typed.ApplyTyCoercion (e, TyCoercionVar tycovar)
                | Typed.DirtOmega (dcovar, ct) ->
                    Typed.ApplyDirtCoercion (e, DirtCoercionVar dcovar) )
              (List.fold_left
                 (fun e dv -> Typed.ApplyDirtExp (e, Types.no_effect_dirt dv))
                 (List.fold_left
                    (fun e tv -> Typed.ApplyTyExp (e, Types.TyParam tv))
                    (List.fold_left
                       (fun e skv ->
                         Typed.ApplySkelExp (e, Types.SkelParam skv) )
                       (Typed.Var var) skvars)
                    tyvars)
                 dirtvars)
              cons4
          , ArrowCoercion
              ( ReflTy (Unification.apply_substitution_ty sub_s2 ty_a')
              , BangCoercion (tyco1, dco2) ) )
      in
      let c1'' =
        (* c1'' = σ₂(σ₁([e_rec / f]c1')) *)
        Unification.apply_substitution (sub_s1 @ sub_s2)
          (Typed.subst_comp [(var, e_rec)] c1')
      in
      let e_f =
        (* σ₃(Λςs.Λ(αs:τs).Λδѕ.λ(ωs:πs).fun x : σ₃(σ₂(σ₁(α))) -> c₁'') *)
        Unification.apply_substitution_exp sub_s3
          (List.fold_right
             (fun skvar e -> Typed.BigLambdaSkel (skvar, e))
             skvars
             (List.fold_right
                (fun tyvar e ->
                  Typed.BigLambdaTy
                    (tyvar, Unification.get_skel_of_tyvar tyvar cons3, e) )
                tyvars
                (List.fold_right
                   (fun dirtvar e -> Typed.BigLambdaDirt (dirtvar, e))
                   dirtvars
                   (List.fold_right
                      (fun q e ->
                        match q with
                        | Typed.TyOmega (tycovar, ct) ->
                            Typed.LambdaTyCoerVar (tycovar, ct, e)
                        | Typed.DirtOmega (dcovar, ct) ->
                            Typed.LambdaDirtCoerVar (dcovar, ct, e) )
                      cons4
                      (Typed.Lambda
                         (Typed.abstraction_with_ty pat'
                            (Unification.apply_substitution_ty sub_s2 ty_a')
                            c1''))))))
      in
      ( Typed.LetRec ([(var, ty_f', e_f)], c2')
      , dty2
      , cons6
      , sub_s1 @ sub_s2 @ sub_s3 )


and type_abstraction in_cons st (pat, comp) ty_in =
  let pat', st', cons1 = type_typed_pattern in_cons st pat ty_in in
  let comp', dty, out_cons, sub_list = type_computation cons1 st' comp in
  ( (pat', comp')
  , (Unification.apply_substitution_ty sub_list ty_in, dty)
  , out_cons
  , sub_list )


and type_effect_clause eff abs2 in_st in_cons in_sub =
  let in_op_ty, out_op_ty = Untyped.EffectMap.find eff in_st.effects in
  let x, k, c_op = abs2 in
  let st_subbed = apply_sub_to_env in_st in_sub in
  let alpha_i, alpha_cons = Typed.fresh_ty_with_fresh_skel () in
  let alpha_dirty = Types.make_dirty alpha_i in
  let x', st', cons' = type_typed_pattern in_cons st_subbed x in_op_ty in
  let k', st'', cons'' =
    type_typed_pattern cons' st' k (Types.Arrow (out_op_ty, alpha_dirty))
  in
  let cons = alpha_cons :: cons'' in
  let typed_c_op, typed_co_op_ty, co_op_cons, c_op_sub =
    type_computation cons st'' c_op
  in
  (typed_c_op, typed_co_op_ty, st_subbed, co_op_cons, c_op_sub, alpha_dirty)


and type_cases in_cons st cases ty_in dty_out =
  match cases with
  | [] -> ([], in_cons, [])
  | case :: cases ->
      let case', cons1, sub1 = type_case in_cons st case ty_in dty_out in
      let cases', cons2, sub2 = type_cases cons1 st cases ty_in dty_out in
      (case' :: cases', cons2, sub1 @ sub2)


and type_case in_cons st case ty_in (ty_out, dirt_out) =
  let p, c = case in
  let p', st', cons1 = type_typed_pattern in_cons st p ty_in in
  let c', (ty_c, dirt_c), cons2, sublist = type_computation cons1 st' c in
  let c'', q = Typed.cast_computation c' (ty_c, dirt_c) (ty_out, dirt_out) in
  ((p', c''), q :: cons2, sublist)


(* Finalize a list of constraints, setting all dirt variables to the empty set. *)

let finalize_constraint sub = function
  | Typed.TyOmega (tcp, ctty) ->
      Error.typing ~loc:Location.unknown
        "Unsolved type inequality in top-level computation: %t"
        (Typed.print_omega_ct (Typed.TyOmega (tcp, ctty)))
  | Typed.DirtOmega
      ( dcp
      , ( {Types.effect_set= s1; Types.row= row1}
        , {Types.effect_set= s2; Types.row= row2} ) ) ->
      assert (Types.EffectSet.subset s1 s2) ;
      let effect_subst =
        Unification.CoerDirtVartoDirtCoercion
          ( dcp
          , Typed.UnionDirt
              (s1, Typed.Empty (Types.closed_dirt (Types.EffectSet.diff s2 s1)))
          )
      and row_substs =
        match (row1, row2) with
        | Types.EmptyRow, Types.ParamRow dv2 ->
            [Unification.DirtVarToDirt (dv2, Types.empty_dirt)]
        | Types.ParamRow dv1, Types.EmptyRow ->
            [Unification.DirtVarToDirt (dv1, Types.empty_dirt)]
        | Types.ParamRow dv1, Types.ParamRow dv2 ->
            [ Unification.DirtVarToDirt (dv1, Types.empty_dirt)
            ; Unification.DirtVarToDirt (dv2, Types.empty_dirt) ]
        | Types.EmptyRow, Types.EmptyRow -> []
      in
      effect_subst :: row_substs @ sub
  | Typed.SkelEq (sk1, sk2) -> failwith __LOC__
  | Typed.TyParamHasSkel (tp, sk) -> failwith __LOC__


let finalize_constraints c_list = List.fold_left finalize_constraint [] c_list

(* Typing top-level 

     Assumes it concerns a top-level computation.
*)

let type_toplevel ~loc st c =
  let c' = c.Untyped.term in
  match c'
  with
  (* | Untyped.Value e -> failwith __LOC__
     let et, ttype,constraints, sub_list = type_expression [] st e in
    Print.debug "Expression : %t" (Typed.print_expression et);
    Print.debug "Expression type : %t " (Types.print_target_ty ttype);
    Print.debug "Starting Set of Constraints ";
    Unification.print_c_list constraints;
    let (sub,final) = Unification.unify ([],[],constraints) in
    let et' = Unification.apply_substitution_exp sub et in
    let ttype' = Unification.apply_substitution_ty sub ttype in
    let (free_ty_vars, free_dirt_vars, split_cons1, split_cons2)= splitter (TypingEnv.return_context st.context) final ttype' in 
    let qual_ty = List.fold_right (fun cons acc -> 
                                          begin match cons with 
                                          | Typed.TyOmega(_,t) -> Types.QualTy (t,acc)
                                          | Typed.DirtOmega(_,t) -> Types.QualDirt(t,acc) 
                                          end 
                                      ) split_cons1 ttype' in 
    let ty_sc_dirt = List.fold_right (fun cons acc -> Types.TySchemeDirt (cons,acc)) free_dirt_vars qual_ty in
    let ty_sc_ty = List.fold_right  (fun cons acc -> Types.TySchemeTy (cons,Types.PrimSkel Types.IntTy,acc)) free_ty_vars ty_sc_dirt in  
    let var_exp = List.fold_right(fun cons acc -> 
                                          begin match cons with 
                                          | Typed.TyOmega(om,t) ->  (Typed.LambdaTyCoerVar (om,t,acc)) 
                                          | Typed.DirtOmega(om,t) -> (Typed.LambdaDirtCoerVar(om,t,acc)) 
                                          end 
                                      ) split_cons1 et' in 
    let var_exp_dirt_lamda = 
      List.fold_right (fun cons acc ->  ( Typed.BigLambdaDirt (cons,acc) )  )  free_dirt_vars var_exp in
    let var_exp_ty_lambda = 
      List.fold_right (fun cons acc ->  (Typed.BigLambdaTy (cons,acc) ) ) free_ty_vars var_exp_dirt_lamda in
    Print.debug "New Expr : %t" (Typed.print_expression var_exp_ty_lambda);
    Print.debug "New Expr ty : %t" (Types.print_target_ty ty_sc_ty);
    let tch_ty = TypeChecker.type_check_exp (TypeChecker.new_checker_state) var_exp_ty_lambda.term in
    Print.debug "Type from Type Checker : %t" (Types.print_target_ty tch_ty);
    ( (Typed.Value var_exp_ty_lambda) ), st *)
  | _
  ->
    let ct, (ttype, dirt), constraints, sub_list = type_computation [] st c in
    (* let x::xs = constraints in 
    Print.debug "Single constraint : %t" (Typed.print_omega_ct x); *)
    Print.debug "Computation : %t" (Typed.print_computation ct) ;
    Print.debug "Computation type : %t ! {%t}"
      (Types.print_target_ty ttype)
      (Types.print_target_dirt dirt) ;
    Print.debug "Starting Set of Constraints " ;
    Unification.print_c_list constraints ;
    let sub, final = Unification.unify ([], [], constraints) in
    Print.debug "Final Constraints:" ;
    Unification.print_c_list final ;
    let ct' = Unification.apply_substitution sub ct in
    Print.debug "New Computation : %t" (Typed.print_computation ct') ;
    let sub2 =
      List.map
        (fun dp -> Unification.DirtVarToDirt (dp, Types.empty_dirt))
        (Types.DirtParamSet.elements (free_dirt_vars_computation ct'))
    in
    let ct2 = Unification.apply_substitution sub2 ct' in
    let sub3 = finalize_constraints (Unification.apply_sub sub2 final) in
    let ct3 = Unification.apply_substitution sub3 ct2 in
    Print.debug "New Computation : %t" (Typed.print_computation ct3) ;
    (* Print.debug "Remaining dirt variables "; *)
    (* List.iter (fun dp -> Print.debug "%t" (Params.Dirt.print dp)) (List.sort_uniq compare (free_dirt_vars_computation ct')); *)
    (*     let tch_ty, tch_dirt =
      TypeChecker.type_check_comp TypeChecker.new_checker_state ct3.term
    in
    Print.debug "Type from Type Checker : %t ! %t"
      (Types.print_target_ty tch_ty)
      (Types.print_target_dirt tch_dirt) ;
 *)
    (ct3, st)
