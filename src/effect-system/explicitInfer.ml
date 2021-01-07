open CoreUtils
module Untyped = UntypedSyntax
open Typed

(* INFERENCE STATE *)

type state = {
  context : Types.target_ty Typed.VariableMap.t;
  effects : (Types.target_ty * Types.target_ty) Typed.EffectMap.t;
  substitutions : Substitution.t;
  constraints : Typed.omega_ct list;
}

let merge_substitutions subs state =
  { state with substitutions = Substitution.merge state.substitutions subs }

let general_update_substitution updater k v st =
  { st with substitutions = updater k v st.substitutions }

let add_param_coercion =
  general_update_substitution Substitution.add_type_coercion

let add_type_sub =
  general_update_substitution Substitution.add_type_substitution

let add_var_coercion =
  general_update_substitution Substitution.add_dirt_var_coercion

let add_var_dirt_sub =
  general_update_substitution Substitution.add_dirt_substitution

let add_skel_sub =
  general_update_substitution Substitution.add_skel_param_substitution

let add_constraint cons st = { st with constraints = cons :: st.constraints }

let add_constraints const st =
  List.fold_left (fun st' x -> add_constraint x st') st const

type computation_typing_result = {
  computation : Typed.computation;
  dtype : Types.target_dirty;
}

type expression_typing_result = {
  expression : Typed.expression;
  ttype : Types.target_ty;
}

let empty =
  {
    context = Typed.VariableMap.empty;
    effects = Typed.EffectMap.empty;
    constraints = [];
    substitutions = Substitution.empty;
  }

let initial_state = empty

let add_def env x ty_sch =
  { env with context = Typed.VariableMap.add x ty_sch env.context }

let print_env env =
  List.iter
    (fun (x, ty_sch) ->
      Print.debug "%t : %t" (Typed.print_variable x)
        (Types.print_target_ty ty_sch))
    env

let add_effect eff (ty1, ty2) st =
  let ty1 = Types.source_to_target ty1 in
  let ty2 = Types.source_to_target ty2 in
  { st with effects = EffectMap.add eff (ty1, ty2) st.effects }

(* INFERENCE *)

let rec type_pattern p = type_plain_pattern p.it

and type_plain_pattern = function
  | Untyped.PVar x -> Typed.PVar x
  | Untyped.PAs (p, x) -> Typed.PAs (type_pattern p, x)
  | Untyped.PNonbinding -> Typed.PNonbinding
  | Untyped.PConst const -> Typed.PConst const
  | Untyped.PTuple ps -> Typed.PTuple (List.map type_pattern ps)
  | Untyped.PRecord flds -> (
      match Assoc.pop flds with
      | None -> assert false
      | Some ((fld, _), _) -> failwith __LOC__)
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
let rec type_typed_pattern st pat ty = type_plain_typed_pattern st pat.it ty

and type_plain_typed_pattern st pat ty =
  match pat with
  | Untyped.PVar x ->
      let st' = add_def st x ty in
      (Typed.PVar x, st')
  | Untyped.PNonbinding -> (Typed.PNonbinding, st)
  | Untyped.PAs (p, v) -> failwith __LOC__
  | Untyped.PTuple l ->
      let tl', pats, st'' =
        List.fold_right
          (fun pat (tl, pats, st') ->
            let tvar, cons = Typed.fresh_ty_with_fresh_skel () in
            let tpat, st''' =
              type_typed_pattern (add_constraint cons st') pat tvar
            in
            (tvar :: tl, tpat :: pats, st'''))
          l ([], [], st)
      in
      let _, coer = Typed.fresh_ty_coer (Types.Tuple tl', ty) in
      let st''' = add_constraint coer st'' in
      (* subtype constraint for general type *)
      (Typed.PTuple pats, st''')
  | Untyped.PRecord r -> failwith __LOC__
  | Untyped.PVariant (lbl, p) -> (
      let ty_in, ty_out = Types.constructor_signature lbl in
      let _omega, q = Typed.fresh_ty_coer (ty_out, ty) in
      let st' = add_constraint q st in
      match p with
      | None -> (Typed.PVariant (lbl, Typed.PTuple []), st)
      | Some p ->
          let p', st'' = type_typed_pattern st' p ty_in in
          (Typed.PVariant (lbl, p'), st''))
  | Untyped.PConst c ->
      let _omega, q = Typed.fresh_ty_coer (Types.type_const c, ty) in
      let st' = add_constraint q st in
      (Typed.PConst c, st')
  | Untyped.PAnnotated _ -> failwith __LOC__

(* ... *)

let rec free_ty_vars_in_context context =
  Typed.VariableMap.fold
    (fun _ ty vars -> Types.TyParamSet.union (Types.free_ty_vars_ty ty) vars)
    context Types.TyParamSet.empty

let rec free_dirt_vars_in_context context =
  Typed.VariableMap.fold
    (fun _ ty vars ->
      Types.DirtParamSet.union (Types.free_dirt_vars_ty ty) vars)
    context Types.DirtParamSet.empty

let splitter context constraints ty =
  let shared_ty_vars = free_ty_vars_in_context context
  and shared_dirt_vars = free_dirt_vars_in_context context in
  let local_ty_vars =
    Types.TyParamSet.(
      let vars_in_ty = Types.free_ty_vars_ty ty
      and vars_in_constraints =
        List.fold_right
          (fun cons vars -> union (constraint_free_ty_vars cons) vars)
          constraints empty
      in
      diff (union vars_in_constraints vars_in_ty) shared_ty_vars)
  and local_dirt_vars =
    Types.DirtParamSet.(
      let vars_in_ty = Types.free_dirt_vars_ty ty
      and vars_in_constraints =
        List.fold_right
          (fun cons vars -> union (constraint_free_dirt_vars cons) vars)
          constraints empty
      in
      diff (union vars_in_constraints vars_in_ty) shared_dirt_vars)
  in
  let local_constraint = function
    | Typed.TyParamHasSkel (tyvar, skvar) ->
        Types.TyParamSet.mem tyvar local_ty_vars
    | cons ->
        let ty_vars = constraint_free_ty_vars cons in
        let dirt_vars = constraint_free_dirt_vars cons in
        let is_sub_ty = Types.TyParamSet.subset ty_vars shared_ty_vars in
        let is_sub_dirt =
          Types.DirtParamSet.subset dirt_vars shared_dirt_vars
        in
        not (is_sub_ty && is_sub_dirt)
  in
  let local_constraints, global_constraints =
    List.partition local_constraint constraints
  in
  let free_skeleton_vars =
    Types.SkelParamSet.diff
      (get_skel_vars_from_constraints local_constraints)
      (get_skel_vars_from_constraints global_constraints)
  in
  let add_skeleton ty_var =
    (ty_var, Unification.get_skel_of_tyvar ty_var constraints)
  in
  ( Types.SkelParamSet.elements free_skeleton_vars,
    Types.TyParamSet.elements local_ty_vars |> List.map add_skeleton,
    Types.DirtParamSet.elements local_dirt_vars,
    local_constraints,
    global_constraints )

let generalize_type free_skel_vars free_ty_vars free_dirt_vars constraints ty =
  ty
  |> List.fold_right
       (fun cons ty ->
         match cons with
         | Typed.TyOmega (_, t) -> Types.QualTy (t, ty)
         | Typed.DirtOmega (_, t) -> Types.QualDirt (t, ty))
       constraints
  |> List.fold_right
       (fun dirt_var ty -> Types.TySchemeDirt (dirt_var, ty))
       free_dirt_vars
  |> List.fold_right
       (fun (ty_var, skel) ty -> Types.TySchemeTy (ty_var, skel, ty))
       free_ty_vars
  |> List.fold_right
       (fun skel_var ty -> Types.TySchemeSkel (skel_var, ty))
       free_skel_vars

let generalize_expr free_skel_vars free_ty_vars free_dirt_vars constraints expr
    =
  expr
  |> List.fold_right
       (fun cons expr ->
         match cons with
         | Typed.TyOmega (om, t) -> Typed.LambdaTyCoerVar (om, t, expr)
         | Typed.DirtOmega (om, t) -> Typed.LambdaDirtCoerVar (om, t, expr))
       constraints
  |> List.fold_right
       (fun dirt_var expr -> Typed.BigLambdaDirt (dirt_var, expr))
       free_dirt_vars
  |> List.fold_right
       (fun (ty_var, skel) expr -> Typed.BigLambdaTy (ty_var, skel, expr))
       free_ty_vars
  |> List.fold_right
       (fun skel_var expr -> Typed.BigLambdaSkel (skel_var, expr))
       free_skel_vars

let rec get_sub_of_ty ty_sch =
  match ty_sch with
  | Types.TySchemeSkel (s, t) ->
      let new_s = CoreTypes.SkelParam.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (Assoc.update s new_s skels, tys, dirts, tycos, dcos)
  | Types.TySchemeTy (p, _, t) ->
      let new_p = CoreTypes.TyParam.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, Assoc.update p new_p tys, dirts, tycos, dcos)
  | Types.TySchemeDirt (p, t) ->
      let new_p = CoreTypes.DirtParam.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, tys, Assoc.update p new_p dirts, tycos, dcos)
  | Types.QualTy ((p, ct), t) ->
      let new_p = CoreTypes.TyCoercionParam.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, tys, dirts, Assoc.update p new_p tycos, dcos)
  | Types.QualDirt ((p, ct), t) ->
      let new_p = CoreTypes.DirtCoercionParam.fresh () in
      let skels, tys, dirts, tycos, dcos = get_sub_of_ty t in
      (skels, tys, dirts, tycos, Assoc.update p new_p dcos)
  | _ -> (Assoc.empty, Assoc.empty, Assoc.empty, Assoc.empty, Assoc.empty)

let rec get_basic_type ty_sch =
  match ty_sch with
  | Types.TySchemeSkel (_, t) -> get_basic_type t
  | Types.TySchemeTy (typ, sk, t) ->
      let a, b = get_basic_type t in
      (Assoc.update typ sk a, b)
  | Types.TySchemeDirt (_, t) -> get_basic_type t
  | Types.QualTy (_, t) -> get_basic_type t
  | Types.QualDirt (_, t) -> get_basic_type t
  | t -> (Assoc.empty, t)

let rec get_applied_cons_from_ty ty_subs dirt_subs ty =
  match ty with
  | Types.TySchemeSkel (_, t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.TySchemeTy (_, _, t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.TySchemeDirt (_, t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.QualTy (cons, t) ->
      let c1, c2 = get_applied_cons_from_ty ty_subs dirt_subs t in
      let ty1, ty2 = cons in
      let newty1, newty2 =
        ( apply_sub_to_type ty_subs dirt_subs ty1,
          apply_sub_to_type ty_subs dirt_subs ty2 )
      in
      let new_omega = CoreTypes.TyCoercionParam.fresh () in
      let new_cons = Typed.TyOmega (new_omega, (newty1, newty2)) in
      (new_cons :: c1, c2)
  | Types.QualDirt (cons, t) ->
      let c1, c2 = get_applied_cons_from_ty ty_subs dirt_subs t in
      let ty1, ty2 = cons in
      let newty1, newty2 =
        (apply_sub_to_dirt dirt_subs ty1, apply_sub_to_dirt dirt_subs ty2)
      in
      let new_omega = CoreTypes.DirtCoercionParam.fresh () in
      let new_cons = Typed.DirtOmega (new_omega, (newty1, newty2)) in
      (c1, new_cons :: c2)
  | _ -> ([], [])

let rec get_skel_constraints alphas_has_skels ty_subs skel_subs =
  match alphas_has_skels with
  | (tvar, skel) :: ss ->
      let new_skel =
        Substitution.apply_substitutions_to_skeleton skel_subs skel
      in
      let (Some new_tyvar) = Assoc.lookup tvar ty_subs in
      Typed.TyParamHasSkel (new_tyvar, new_skel)
      :: get_skel_constraints ss ty_subs skel_subs
  | [] -> []

let get_skel_constraints' alphas_has_skels ty_subs skel_subs =
  get_skel_constraints (Assoc.to_list alphas_has_skels) ty_subs skel_subs

let apply_types alphas_has_skels skel_subs ty_subs dirt_subs var ty_sch =
  let new_skel_subs =
    List.fold_left
      (fun old_subs (a, b) ->
        Substitution.add_skel_param_substitution a (Types.SkelParam b) old_subs)
      Substitution.empty (Assoc.to_list skel_subs)
  in
  let skel_constraints =
    get_skel_constraints' alphas_has_skels ty_subs new_skel_subs
  in
  let skel_apps =
    Assoc.fold_left
      (fun a (_, b) -> Typed.ApplySkelExp (a, Types.SkelParam b))
      (Typed.Var var) skel_subs
  in
  let ty_apps =
    Assoc.fold_left
      (fun a (_, b) -> Typed.ApplyTyExp (a, Types.TyParam b))
      skel_apps ty_subs
  in
  let dirt_apps =
    Assoc.fold_left
      (fun a (_, b) -> Typed.ApplyDirtExp (a, Types.no_effect_dirt b))
      ty_apps dirt_subs
  in
  let ty_cons, dirt_cons = get_applied_cons_from_ty ty_subs dirt_subs ty_sch in
  let ty_cons_apps =
    List.fold_left
      (fun a (Typed.TyOmega (omega, _)) ->
        Typed.ApplyTyCoercion (a, Typed.TyCoercionVar omega))
      dirt_apps ty_cons
  in
  let dirt_cons_apps =
    List.fold_left
      (fun a (Typed.DirtOmega (omega, _)) ->
        Typed.ApplyDirtCoercion (a, Typed.DirtCoercionVar omega))
      ty_cons_apps dirt_cons
  in
  (dirt_cons_apps, skel_constraints @ ty_cons @ dirt_cons)

let apply_polymorphic_variable x ty_schi =
  let ( bind_skelvar_sub,
        bind_tyvar_sub,
        bind_dirtvar_sub,
        bind_tyco_sub,
        bind_dco_sub ) =
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
  Print.debug "returned: %t" (Typed.print_expression returned_x);
  Print.debug "original_type: %t" (Types.print_target_ty ty_schi);
  Print.debug "returned_type: %t" (Types.print_target_ty applied_basic_type);
  (returned_x, applied_basic_type, returned_cons)

let rec type_expression st ({ it = expr } as e) =
  Print.debug "type_expression: %t" (Untyped.print_expression e);
  Print.debug "### Constraints Before ###";
  Unification.print_c_list st.constraints;
  Print.debug "##########################";
  let st', { expression; ttype } = type_plain_expression st expr in
  Print.debug "### Constraints After ####";
  Unification.print_c_list st'.constraints;
  Print.debug "##########################";
  (st', { expression; ttype })

and type_plain_expression (st : state) :
    Untyped.plain_expression -> state * expression_typing_result = function
  | Untyped.Var x -> (
      match Typed.VariableMap.find_opt x st.context with
      | Some ty_schi ->
          let returned_x, applied_basic_type, returned_cons =
            apply_polymorphic_variable x ty_schi
          in
          ( add_constraints returned_cons st,
            { expression = returned_x; ttype = applied_basic_type } )
      | None ->
          Print.debug "Variable not found: %t" (Typed.print_variable x);
          assert false)
  | Untyped.Const const ->
      (st, { expression = Typed.Const const; ttype = Types.type_const const })
  | Untyped.Tuple es ->
      let folder (st', terms, types) ex =
        let st_, { expression; ttype } = type_expression st' ex in
        (st_, expression :: terms, ttype :: types)
      in
      let st'', terms_r, types_r =
        List.fold_left folder (st, [], []) es
        (* FOLD LEFT VS FOLD RIGHT????*)
      in
      ( st'',
        {
          expression = Typed.Tuple (List.rev terms_r);
          ttype = Types.Tuple (List.rev types_r);
        } )
  | Untyped.Record lst -> failwith __LOC__
  | Untyped.Variant (lbl, e) -> (
      let ty_in, ty_out = Types.constructor_signature lbl in
      match e with
      | None ->
          ( st,
            { expression = Typed.Variant (lbl, Typed.Tuple []); ttype = ty_out }
          )
      | Some e ->
          let st', { expression = e'; ttype = u' } = type_expression st e in
          let e'', cast_cons = cast_expression e' u' ty_in in
          (* !! TODO: CHECK ORDER OF CONSTRAINT ADDING !!*)
          let st'' = add_constraint cast_cons st' in
          (st'', { expression = Typed.Variant (lbl, e''); ttype = ty_out }))
  | Untyped.Lambda a ->
      Print.debug "in infer lambda";
      let in_ty, in_ty_skel = Typed.fresh_ty_with_fresh_skel () in
      let st' = add_constraint in_ty_skel st in
      let (p, c), (ty, dty), st'' = type_abstraction st' a in_ty in
      let target_ty = Types.Arrow (ty, dty) in
      let target_lambda =
        Typed.Lambda
          (abstraction_with_ty p
             (Substitution.apply_substitutions_to_type st''.substitutions in_ty)
             c)
      in
      Unification.print_c_list st''.constraints;
      Print.debug "lambda ty: %t" (Types.print_target_ty target_ty);
      (st'', { expression = target_lambda; ttype = target_ty })
  | Untyped.Effect eff ->
      let in_ty, out_ty = Typed.EffectMap.find eff st.effects in
      let s = Types.EffectSet.singleton eff in
      ( st,
        {
          expression = Typed.Effect (eff, (in_ty, out_ty));
          ttype = Types.Arrow (in_ty, (out_ty, Types.closed_dirt s));
        } )
  | Untyped.Handler h ->
      let out_dirt_var = CoreTypes.DirtParam.fresh () in
      let in_dirt = Types.fresh_dirt ()
      and out_dirt = Types.no_effect_dirt out_dirt_var
      and in_ty, skel_cons_in = Typed.fresh_ty_with_fresh_skel ()
      and out_ty, skel_cons_out = Typed.fresh_ty_with_fresh_skel () in
      let target_type = Types.Handler ((in_ty, in_dirt), (out_ty, out_dirt)) in
      let r_ty, r_ty_skel_cons = Typed.fresh_ty_with_fresh_skel () in
      let r_cons = r_ty_skel_cons :: st.constraints in
      let pr, cr = h.value_clause in
      (*
      let Untyped.PVar x = pr.it in
      let r_st = add_def st x r_ty in
      let st' = add_constraints r_cons r_st in
      *)
      let r_st =
        match pr.it with
        | Untyped.PVar x -> add_def st x r_ty
        | _ -> failwith __LOC__
      in
      let st' = add_constraints r_cons r_st in
      (* Note to self: Should this also be added?, check article *)
      (* let st' = add_constraint skel_cons_in st' |> add_constraint skel_cons_out in *)
      let ( st'',
            {
              computation = target_cr_term;
              dtype = target_cr_ty, target_cr_dirt;
            } ) =
        type_computation st' cr
      in
      let r_subbed_st = st'' in
      let folder
          (*
          (acc_terms, acc_tys, acc_st, acc_cons, acc_subs, acc_alpha_delta_i)
          (eff, abs2) =
          *)
            (eff, abs2) (acc_terms, acc_tys, acc_st, acc_alpha_delta_i) =
        let typed_c_op, typed_co_op_ty, s_st, (alpha_i, delta_i) =
          (* Print.debug "type_effect_clause: %t" (Untyped.abstraction2 abs2) ; *)
          type_effect_clause eff abs2 acc_st
        in
        ( typed_c_op :: acc_terms,
          typed_co_op_ty :: acc_tys,
          s_st,
          (alpha_i, delta_i) :: acc_alpha_delta_i )
      in
      (*
      let folder_function =
        List.fold_left folder ([], [], r_subbed_st, target_cr_cons, [], [])
          h.effect_clauses
      in
      *)
      let folder_function =
        List.fold_right folder
          (Assoc.to_list h.effect_clauses)
          ([], [], r_subbed_st, [])
      in
      let typed_op_terms, typed_op_terms_ty, st''', alpha_delta_i_s =
        folder_function
      in
      let cons_1 = (target_cr_ty, out_ty) in
      let cons_2 = (target_cr_dirt, out_dirt) in
      let omega_1, omega_cons_1 = Typed.fresh_ty_coer cons_1
      and omega_2, omega_cons_2 = Typed.fresh_dirt_coer cons_2 in
      let y_var_name = CoreTypes.Variable.fresh "fresh_var" in
      let y = Typed.PVar y_var_name in
      let annot_y = y in
      let exp_y = Typed.Var y_var_name in
      let coerced_y, omega_cons_6 = Typed.cast_expression exp_y in_ty r_ty in
      Print.debug "In infer handler (%t)" (Untyped.print_pattern pr);
      let substituted_c_r =
        match pr.it with
        | Untyped.PVar x ->
            Typed.subst_comp (Assoc.of_list [ (x, coerced_y) ]) target_cr_term
        | _ -> target_cr_term
      in
      let coerced_substiuted_c_r =
        Typed.CastComp (substituted_c_r, Typed.BangCoercion (omega_1, omega_2))
      in
      let mapper (op_term, (op_term_ty, op_term_dirt), (alpha_i, delta_i))
          (eff, abs2) =
        let in_op_ty, out_op_ty = Typed.EffectMap.find eff st.effects in
        let x, k, c_op = abs2 in
        let cons_3 = (op_term_ty, out_ty) in
        let cons_4 = (op_term_dirt, out_dirt) in
        let cons_5a = Types.Arrow (out_op_ty, (out_ty, out_dirt)) in
        let cons_5b = Types.Arrow (out_op_ty, (alpha_i, delta_i)) in
        let omega_3, omega_cons_3 = Typed.fresh_ty_coer cons_3 in
        let omega_4, omega_cons_4 = Typed.fresh_dirt_coer cons_4 in
        let l_var_name = CoreTypes.Variable.fresh "fresh_var" in
        let l = Typed.PVar l_var_name in
        let annot_l = l in
        let exp_l = Typed.Var l_var_name in
        let coerced_l, omega_cons_5 =
          Typed.cast_expression exp_l cons_5a cons_5b
        in
        let substituted_c_op =
          match k.it with
          | Untyped.PVar k_var ->
              let s_c_op =
                Typed.subst_comp (Assoc.of_list [ (k_var, coerced_l) ]) op_term
              in
              Print.debug "substituted_c_op [%t/%t]: %t"
                (CoreTypes.Variable.print ~safe:true l_var_name)
                (CoreTypes.Variable.print ~safe:true k_var)
                (Typed.print_computation s_c_op);
              s_c_op
          | Untyped.PNonbinding -> op_term
          | _ -> failwith __LOC__
        in
        let coerced_substiuted_c_op =
          Typed.CastComp
            (substituted_c_op, Typed.BangCoercion (omega_3, omega_4))
        in
        let target_effect = (eff, (in_op_ty, out_op_ty)) in
        ( ( target_effect,
            Typed.abstraction2 (type_pattern x) annot_l coerced_substiuted_c_op
          ),
          [ omega_cons_3; omega_cons_4; omega_cons_5 ] )
      in
      let mapper_input_a =
        List.map2 (fun a b -> (a, b)) typed_op_terms typed_op_terms_ty
      in
      let mapper_input =
        List.map2 (fun (a, b) c -> (a, b, c)) mapper_input_a alpha_delta_i_s
      in
      let new_op_clauses_with_cons =
        List.map2 mapper mapper_input (Assoc.to_list h.effect_clauses)
      in
      let new_op_clauses =
        List.map (fun (x, y) -> x) new_op_clauses_with_cons
      in
      let ops_cons = concat_map (fun (x, y) -> y) new_op_clauses_with_cons in
      let typed_value_clause =
        Typed.abstraction_with_ty annot_y r_ty coerced_substiuted_c_r
      in
      let target_handler =
        {
          Typed.effect_clauses = Assoc.of_list new_op_clauses;
          value_clause = typed_value_clause;
        }
      in
      let typed_handler = Typed.Handler target_handler in
      let for_set_handlers_ops =
        List.map (fun ((eff, (_, _)), _) -> eff) new_op_clauses
      in
      let ops_set = Types.EffectSet.of_list for_set_handlers_ops in
      let handlers_ops =
        Types.{ effect_set = ops_set; row = ParamRow out_dirt_var }
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
        [
          skel_cons_in;
          skel_cons_out;
          omega_cons_1;
          omega_cons_2;
          omega_cons_6;
          omega_cons_7;
        ]
        @ ops_cons @ r_cons
      in
      Print.debug "### Handler r_cons             ###";
      Unification.print_c_list r_cons;
      Print.debug "### Handler cons_n             ###";
      Print.debug "-> Unavailable <-";
      (*Unification.print_c_list cons_n ; *)
      Print.debug "### Constraints before Handler ###";
      Unification.print_c_list st.constraints;
      Print.debug "#################################";
      Print.debug "### Constraints after Handler ###";
      Unification.print_c_list all_cons;
      Print.debug "#################################";
      ( add_constraints all_cons st''',
        { expression = coerced_handler; ttype = target_type } )
  | _ -> failwith __LOC__

and type_computation (st : state) { it = comp } =
  let st', { computation = c; dtype = ttype } =
    type_plain_computation st comp
  in
  (st', { computation = c; dtype = ttype })

and type_plain_computation (st : state) = function
  | Untyped.Value e ->
      let st', { expression = typed_e; ttype = tt } = type_expression st e in
      let new_d_ty = (tt, Types.empty_dirt) in
      (st', { computation = Typed.Value typed_e; dtype = new_d_ty })
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
      let st', { expression = e'; ttype = ty_A } = type_expression st e in
      let ty_alpha, q_alpha = Typed.fresh_ty_with_fresh_skel () in
      let dirt_delta = Types.fresh_dirt () in
      let cases', st'' =
        (* Much larger list than before*)
        type_cases (add_constraint q_alpha st') cases ty_A (ty_alpha, dirt_delta)
      in
      ( st'',
        {
          computation = Typed.Match (e', cases');
          dtype = (ty_alpha, dirt_delta);
        } )
  | Untyped.Apply (e1, e2) ->
      Print.debug "in infer apply";
      let st', { expression = typed_e1; ttype = tt_1 } =
        type_expression st e1
      in
      let st'', { expression = typed_e2; ttype = tt_2 } =
        type_expression st' e2
      in
      Print.debug "e1 apply type : %t" (Types.print_target_ty tt_1);
      Print.debug "e2 apply type : %t" (Types.print_target_ty tt_2);
      let new_ty_var, cons1 = Typed.fresh_ty_with_fresh_skel () in
      let fresh_dirty_ty = Types.make_dirty new_ty_var in
      let e1_coerced, omega_cons_1 =
        Typed.cast_expression
          (Substitution.apply_substitutions_to_expression st''.substitutions
             typed_e1)
          (Substitution.apply_substitutions_to_type st''.substitutions tt_1)
          (Types.Arrow (tt_2, fresh_dirty_ty))
      in
      let st_const = add_constraint cons1 st'' in
      ( add_constraint omega_cons_1 st_const,
        {
          computation = Typed.Apply (e1_coerced, typed_e2);
          dtype = fresh_dirty_ty;
        } )
  | Untyped.Handle (e, c) ->
      let dirty_1, cons_skel_1 = Typed.fresh_dirty_with_fresh_skel () in
      let dirty_2, cons_skel_2 = Typed.fresh_dirty_with_fresh_skel () in
      let st', { expression = typed_exp; ttype = exp_type } =
        type_expression st e
      in
      let st_subbed = st' in
      let st'', { computation = typed_comp; dtype = comp_dirty_type } =
        type_computation st_subbed c
      in
      let coer_exp, omega_cons_1 =
        Typed.cast_expression typed_exp
          (Substitution.apply_substitutions_to_type st''.substitutions exp_type)
          (Types.Handler (dirty_1, dirty_2))
      in
      let coer_comp, cons_comp =
        Typed.cast_computation typed_comp comp_dirty_type dirty_1
      in
      let st_cons =
        add_constraint cons_skel_1 st''
        |> add_constraint cons_skel_2
        |> add_constraint omega_cons_1
        |> add_constraint cons_comp
      in
      ( st_cons,
        { computation = Typed.Handle (coer_exp, coer_comp); dtype = dirty_2 } )
  | Untyped.Let (defs, c_2) -> (
      let [ (p_def, c_1) ] = defs in
      match c_1.it with
      | Untyped.Value e1 ->
          let st', { expression = typed_e1; ttype = type_e1 } =
            type_expression st e1
          in
          let sub_e1', cons_e1' =
            Unification.unify (st'.substitutions, [], st'.constraints)
          in
          let st'' =
            st' |> add_constraints cons_e1' |> merge_substitutions sub_e1'
          in
          let type_e1 =
            Substitution.apply_substitutions_to_type sub_e1' type_e1
          in
          let typed_e1 =
            Substitution.apply_substitutions_to_expression sub_e1' typed_e1
          in
          let ( free_skel_vars,
                free_ty_vars,
                free_dirt_vars,
                split_cons1,
                global_constraints ) =
            splitter st''.context cons_e1' type_e1
          in
          let ty_sc_skel =
            generalize_type free_skel_vars free_ty_vars free_dirt_vars
              split_cons1 type_e1
          in
          let st'' = { st'' with constraints = global_constraints } in
          let typed_pat, new_st = type_typed_pattern st'' p_def ty_sc_skel in
          let new_st', { computation = typed_c2; dtype = type_c2 } =
            type_computation new_st c_2
          in
          let var_exp =
            generalize_expr free_skel_vars free_ty_vars free_dirt_vars
              split_cons1 typed_e1
          in
          let return_term =
            Typed.LetVal
              (var_exp, Typed.abstraction_with_ty typed_pat ty_sc_skel typed_c2)
          in
          (new_st', { computation = return_term; dtype = type_c2 })
      | _ ->
          let st', { computation = typed_c1; dtype = type_c1, dirt_c1 } =
            type_computation st c_1
          in
          let typed_pattern, new_st = type_typed_pattern st' p_def type_c1 in
          let st'', { computation = typed_c2; dtype = type_c2, dirt_c2 } =
            type_computation new_st c_2
          in
          let new_dirt_var = Types.fresh_dirt () in
          let ty_c1 = type_c1 in
          let coer_c1, omega_cons_1 =
            Typed.cast_computation typed_c1 (ty_c1, dirt_c1)
              (ty_c1, new_dirt_var)
          in
          let coer_c2, omega_cons_2 =
            Typed.cast_computation typed_c2 (type_c2, dirt_c2)
              (type_c2, new_dirt_var)
          in
          let abstraction = (typed_pattern, coer_c2) in
          ( add_constraint omega_cons_1 st'' |> add_constraint omega_cons_2,
            {
              computation = Typed.Bind (coer_c1, abstraction);
              dtype = (type_c2, new_dirt_var);
            } ))
  | Untyped.LetRec ([ (var, abs) ], c2)
  (*when not (Untyped.contains_variable_abs var abs) *) ->
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
      Print.debug "Here: Pattern %t" (Untyped.print_pattern (fst abs));
      Print.debug "Here: Computation: %t" (Untyped.print_computation (snd abs));
      (* Type abstraction *)
      let ty_a, q_a = fresh_ty_with_fresh_skel () in
      let ty_b, q_b = fresh_ty_with_fresh_skel () in
      let dirt_d = Types.fresh_dirt () in
      let df = Types.Arrow (ty_a, (ty_b, dirt_d)) in
      let st1 = add_def st var df |> add_constraint q_a |> add_constraint q_b in
      let (pat', c1'), (ty_a', (ty_A1, dirt_D1)), st' =
        type_abstraction st1 abs ty_a
      in
      let tyco1, q_ty = fresh_ty_coer (ty_A1, ty_b) in
      let dco2, q_d = Typed.fresh_dirt_coer (dirt_D1, dirt_d) in
      let st1' = st' |> add_constraint q_ty |> add_constraint q_d in
      let sub_s', cons_s' =
        Unification.unify (Substitution.empty, [], st1'.constraints)
      in
      let st = merge_substitutions sub_s' st in
      let st2 = add_constraints cons_s' st in
      let ty_A1' = Substitution.apply_substitutions_to_type sub_s' ty_A1 in
      let dirt_D1' = Substitution.apply_substitutions_to_dirt sub_s' dirt_D1 in
      (* Do we also need to substitute dirt? *)
      let ty_a_s' = Substitution.apply_substitutions_to_type sub_s' ty_a' in
      let arrow_type = Types.Arrow (ty_a_s', (ty_A1', dirt_D1')) in
      let skvars, tyvars, dirtvars, cons4, cons5 =
        splitter st2.context st2.constraints ty_A1'
      in
      let ty_f =
        generalize_type skvars tyvars dirtvars cons4
          (Substitution.apply_substitutions_to_type st2.substitutions arrow_type)
      in
      let st3 =
        add_def st2 var ty_f |> add_constraints cons5 |> add_constraints cons4
      in
      Print.debug "Calculating computation";
      let st3', { computation = c2'; dtype = dty2 } = type_computation st3 c2 in
      let ty_f' =
        Substitution.apply_substitutions_to_type st3'.substitutions ty_f
      in
      Print.debug "Starting here";
      let e_rec =
        (* f ςs αs δѕ ωs |> <α> -> ω₁ ! ω₂ *)
        Typed.CastExp
          ( List.fold_left
              (fun e q ->
                match q with
                | Typed.TyOmega (tycovar, ct) ->
                    Typed.ApplyTyCoercion (e, TyCoercionVar tycovar)
                | Typed.DirtOmega (dcovar, ct) ->
                    Typed.ApplyDirtCoercion (e, DirtCoercionVar dcovar)
                | _ -> failwith __LOC__)
              (List.fold_left
                 (fun e dv -> Typed.ApplyDirtExp (e, Types.no_effect_dirt dv))
                 (List.fold_left
                    (fun e (tv, _) -> Typed.ApplyTyExp (e, Types.TyParam tv))
                    (List.fold_left
                       (fun e skv ->
                         Typed.ApplySkelExp (e, Types.SkelParam skv))
                       (Typed.Var var) skvars)
                    tyvars)
                 dirtvars)
              cons4,
            ArrowCoercion (ReflTy ty_a_s', BangCoercion (tyco1, dco2)) )
      in
      let c1'' =
        (* c1'' = σ₂(σ₁([e_rec / f]c1')) *)
        Substitution.apply_substitutions_to_computation st3'.substitutions
          (Typed.subst_comp (Assoc.of_list [ (var, e_rec) ]) c1')
      in
      let e_f =
        (* σ₃(Λςs.Λ(αs:τs).Λδѕ.λ(ωs:πs).fun x : σ₃(σ₂(σ₁(α))) -> c₁'') *)
        Substitution.apply_substitutions_to_expression st3'.substitutions
          (generalize_expr skvars tyvars dirtvars cons4
             (Typed.Lambda
                (Typed.abstraction_with_ty pat'
                   (Substitution.apply_substitutions_to_type st3'.substitutions
                      ty_a')
                   c1'')))
      in
      ( st3',
        {
          computation = Typed.LetRec ([ (var, ty_f', e_f) ], c2');
          dtype = dty2;
        } )
  | _ -> failwith __LOC__

and type_abstraction st (pat, comp) ty_in =
  let pat', st' = type_typed_pattern st pat ty_in in
  let st'', { computation = comp'; dtype = dty } = type_computation st' comp in
  ((pat', comp'), (ty_in, dty), st'')

and type_effect_clause eff abs2 st =
  let in_op_ty, out_op_ty = Typed.EffectMap.find eff st.effects in
  let x, k, c_op = abs2 in
  let alpha_i, alpha_cons = Typed.fresh_ty_with_fresh_skel () in
  let alpha_dirty = Types.make_dirty alpha_i in
  let x', st' = type_typed_pattern st x in_op_ty in
  let k', st'' =
    type_typed_pattern st' k (Types.Arrow (out_op_ty, alpha_dirty))
  in
  let st_final, { computation = typed_c_op; dtype = typed_co_op_ty } =
    type_computation (add_constraint alpha_cons st'') c_op
  in
  (typed_c_op, typed_co_op_ty, st_final, alpha_dirty)

and type_cases st cases ty_in dty_out =
  match cases with
  | [] -> ([], st)
  | case :: cases ->
      let case', st' = type_case st case ty_in dty_out in
      let cases', st'' = type_cases st' cases ty_in dty_out in
      (case' :: cases', st'')

and type_case st case ty_in (ty_out, dirt_out) =
  let p, c = case in
  let p', st' = type_typed_pattern st p ty_in in
  let st'', { computation = c'; dtype = ty_c, dirt_c } =
    type_computation st' c
  in
  let c'', q = Typed.cast_computation c' (ty_c, dirt_c) (ty_out, dirt_out) in
  ((p', c''), add_constraint q st'')

(* Finalize a list of constraints, setting all dirt variables to the empty set. *)

let finalize_constraint sub ct =
  match ct with
  | Typed.TyOmega (tcp, ctty) ->
      Error.typing ~loc:Location.unknown
        "Unsolved type inequality in top-level computation: %t"
        (Typed.print_omega_ct (Typed.TyOmega (tcp, ctty)))
  | Typed.DirtOmega
      ( dcp,
        ( { Types.effect_set = s1; Types.row = row1 },
          { Types.effect_set = s2; Types.row = row2 } ) ) ->
      assert (Types.EffectSet.subset s1 s2);
      let sub' =
        Substitution.add_dirt_var_coercion dcp
          (Typed.UnionDirt
             (s1, Typed.Empty (Types.closed_dirt (Types.EffectSet.diff s2 s1))))
          sub
      in
      let subs'' =
        match (row1, row2) with
        | Types.EmptyRow, Types.ParamRow dv2 ->
            Substitution.add_dirt_substitution dv2 Types.empty_dirt sub'
        | Types.ParamRow dv1, Types.EmptyRow ->
            Substitution.add_dirt_substitution dv1 Types.empty_dirt sub'
        | Types.ParamRow dv1, Types.ParamRow dv2 ->
            Substitution.add_dirt_substitution dv1 Types.empty_dirt sub'
            |> Substitution.add_dirt_substitution dv2 Types.empty_dirt
        | Types.EmptyRow, Types.EmptyRow -> sub'
      in
      subs''
  | Typed.SkelEq (sk1, sk2) -> failwith __LOC__
  | Typed.TyParamHasSkel (tp, sk) -> failwith __LOC__

let finalize_constraints c_list =
  List.fold_left
    (fun subs ct -> finalize_constraint subs ct)
    Substitution.empty c_list

(* Typing top-level

     Assumes it concerns a top-level computation.
*)

let type_toplevel ~loc st c =
  let c' = c.it in
  match c' with
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
  | _ ->
      let fresh_st = { st with substitutions = Substitution.empty } in
      let st', { computation = ct; dtype = ttype, dirt } =
        type_computation fresh_st c
      in
      (* let x::xs = constraints in
         Print.debug "Single constraint : %t" (Typed.print_omega_ct x); *)
      Print.debug "Computation : %t" (Typed.print_computation ct);
      Print.debug "Computation type : %t ! {%t}"
        (Types.print_target_ty ttype)
        (Types.print_target_dirt dirt);
      Print.debug "Starting Set of Constraints ";
      Unification.print_c_list st'.constraints;
      let sub, final =
        Unification.unify (Substitution.empty, [], st'.constraints)
      in
      Print.debug "Final Constraints:";
      Unification.print_c_list final;
      let ct' = Substitution.apply_substitutions_to_computation sub ct in
      Print.debug "New Computation : %t" (Typed.print_computation ct');
      let sub2 =
        List.fold_left
          (fun subs dp ->
            Substitution.add_dirt_substitution dp Types.empty_dirt subs)
          Substitution.empty
          (Types.DirtParamSet.elements (free_dirt_vars_computation ct'))
      in
      let ct2 = Substitution.apply_substitutions_to_computation sub2 ct' in
      let sub3 =
        finalize_constraints
          (Substitution.apply_substitutions_to_constraints sub2 final)
      in
      let ct3 = Substitution.apply_substitutions_to_computation sub3 ct2 in
      Print.debug "New Computation : %t" (Typed.print_computation ct3);
      (* Print.debug "Remaining dirt variables "; *)
      (* List.iter (fun dp -> Print.debug "%t" (CoreTypes.DirtParam.print dp)) (List.sort_uniq compare (free_dirt_vars_computation ct')); *)
      (* let tch_ty, tch_dirt =
           TypeChecker.type_check_comp TypeChecker.new_checker_state ct3.term
         in
         Print.debug "Type from Type Checker : %t ! %t"
           (Types.print_target_ty tch_ty)
           (Types.print_target_dirt tch_dirt) ;
      *)
      (ct3, st)

let add_external ctx x ty =
  { ctx with context = Typed.VariableMap.add x ty ctx.context }
