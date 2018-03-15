open Typed
open Types
open Unification

type state =
  { var_types: (Typed.variable, Types.target_ty) OldUtils.assoc
  ; ty_params: Params.Ty.t list
  ; dirt_params: Params.Dirt.t list
  ; skel_params: Params.Skel.t list
  ; ty_param_skeletons: (Params.Ty.t, Types.skeleton) OldUtils.assoc
  ; ty_coer_types: (Params.TyCoercion.t, Types.ct_ty) OldUtils.assoc
  ; dirt_coer_types: (Params.DirtCoercion.t, Types.ct_dirt) OldUtils.assoc }

let extend_ty_params st ty_var = {st with ty_params= ty_var :: st.ty_params}

let extend_var_types st t_var tty =
  {st with var_types= (t_var, tty) :: st.var_types}


let extend_dirt_params st dirt_var =
  {st with dirt_params= dirt_var :: st.dirt_params}


let extend_skel_params st sk_var =
  {st with skel_params= sk_var :: st.skel_params}


let extend_ty_coer_types st tcp ctty =
  {st with ty_coer_types= (tcp, ctty) :: st.ty_coer_types}


let extend_dirt_coer_types st tcp ctdrt =
  {st with dirt_coer_types= (tcp, ctdrt) :: st.dirt_coer_types}


let extend_ty_param_skeletons st tv sk =
  {st with ty_param_skeletons= (tv, sk) :: st.ty_param_skeletons}


let initial_state =
  { var_types= []
  ; ty_params= []
  ; dirt_params= []
  ; skel_params= []
  ; ty_param_skeletons= []
  ; ty_coer_types= []
  ; dirt_coer_types= [] }


let rec check_well_formed_skeleton st = function
  | SkelParam skel_param -> assert (List.mem skel_param st.skel_params)
  | PrimSkel p -> ()
  | SkelArrow (sk1, sk2) ->
      check_well_formed_skeleton st sk1 ;
      check_well_formed_skeleton st sk2
  | SkelHandler (sk1, sk2) ->
      check_well_formed_skeleton st sk1 ;
      check_well_formed_skeleton st sk2
  | ForallSkel (skp, sk1) ->
      let st' = extend_skel_params st skp in
      check_well_formed_skeleton st' sk1
  | _ -> failwith "Not yet implemented"


let check_well_formed_dirt st = function
  | {Types.row= Types.EmptyRow} -> ()
  | {Types.row= Types.ParamRow v} -> assert (List.mem v st.dirt_params)


let rec check_well_formed_ty st ty =
  match ty with
  | TyParam typ ->
      let ty_var_list = List.map (fun (x, y) -> x) st.ty_param_skeletons in
      assert (List.mem typ ty_var_list)
  | Arrow (tty1, tty2) ->
      check_well_formed_ty st tty1 ;
      check_well_formed_dirty_ty st tty2
  | Tuple ttyl -> List.iter (check_well_formed_ty st) ttyl
  | Handler (tty1, tty2) ->
      check_well_formed_dirty_ty st tty1 ;
      check_well_formed_dirty_ty st tty2
  | PrimTy _ -> ()
  | QualTy (ct_ty1, tty1) ->
      check_well_formed_ty_cons st ct_ty1 ;
      check_well_formed_ty st tty1
  | QualDirt (ct_ty1, tty1) ->
      check_well_formed_dirt_cons st ct_ty1 ;
      check_well_formed_ty st tty1
  | TySchemeTy (ty_param, skel, tty1) ->
      let st' = extend_ty_param_skeletons st ty_param skel in
      check_well_formed_ty st' tty1
  | TySchemeDirt (dirt_param, tty1) ->
      let st' = extend_dirt_params st dirt_param in
      check_well_formed_ty st' tty1
  | TySchemeSkel (skel_param, tty1) ->
      let st' = extend_skel_params st skel_param in
      check_well_formed_ty st' tty1


and check_well_formed_dirty_ty st (ty, drt) =
  check_well_formed_ty st ty ;
  check_well_formed_dirt st drt


and check_well_formed_ty_cons st (t1, t2) =
  check_well_formed_ty st t1 ; check_well_formed_ty st t2


and check_well_formed_dirt_cons st (d1, d2) =
  check_well_formed_dirt st d1 ;
  check_well_formed_dirt st d2


let rec type_of_ty_coercion st ty_coer =
  match ty_coer with
  | ReflTy tty -> (tty, tty)
  | ArrowCoercion (tycoer1, dirtycoer) ->
      let t2, t1 = type_of_ty_coercion st tycoer1 in
      let c1, c2 = type_of_dirty_coercion st dirtycoer in
      (Types.Arrow (t1, c1), Types.Arrow (t2, c2))
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      let c3, c1 = type_of_dirty_coercion st dirtycoer1 in
      let c2, c4 = type_of_dirty_coercion st dirtycoer2 in
      (Types.Handler (c1, c2), Types.Handler (c3, c4))
  | TyCoercionVar p -> (
    match OldUtils.lookup p st.ty_coer_types with
    | None -> assert false
    | Some pi -> pi )
  | SequenceTyCoer (ty_coer1, ty_coer2) ->
      let t1, t2 = type_of_ty_coercion st ty_coer1 in
      let t2, t3 = type_of_ty_coercion st ty_coer2 in
      (t1, t3)
  | LeftArrow tc1 -> (
    match type_of_ty_coercion st tc1 with
    | Types.Arrow (t1, _), Types.Arrow (t2, _) -> (t2, t1)
    | _ -> assert false )
  | ForallTy (ty_param, ty_coer1) ->
      let new_st = extend_ty_params st ty_param in
      let t1, t2 = type_of_ty_coercion new_st ty_coer1 in
      ( Types.TySchemeTy (ty_param, Types.PrimSkel Types.IntTy, t1)
      , Types.TySchemeTy (ty_param, Types.PrimSkel Types.IntTy, t2) )
  | ApplyTyCoer (ty_coer1, tty1) -> (
    match type_of_ty_coercion st ty_coer1 with
    | Types.TySchemeTy (ty_param1, _, t1), Types.TySchemeTy (ty_param2, _, t2) ->
        check_well_formed_ty st tty1 ;
        let sub = Unification.TyParamToTy (ty_param1, tty1) in
        assert (ty_param1 = ty_param2) ;
        (Unification.apply_sub_ty sub t1, Unification.apply_sub_ty sub t2)
    | _ -> assert false )
  | ForallDirt (dirt_param, ty_coer1) ->
      let new_st = extend_dirt_params st dirt_param in
      let t1, t2 = type_of_ty_coercion new_st ty_coer1 in
      (Types.TySchemeDirt (dirt_param, t1), Types.TySchemeDirt (dirt_param, t2))
  | ApplyDirCoer (ty_coer1, drt) -> (
    match type_of_ty_coercion st ty_coer1 with
    | Types.TySchemeDirt (drt_param1, t1), Types.TySchemeDirt (drt_param2, t2) ->
        check_well_formed_dirt st drt ;
        let sub = Unification.DirtVarToDirt (drt_param1, drt) in
        assert (drt_param1 = drt_param2) ;
        (Unification.apply_sub_ty sub t1, Unification.apply_sub_ty sub t2)
    | _ -> assert false )
  | PureCoercion dirty_coer1 ->
      let (t1, _), (t2, _) = type_of_dirty_coercion st dirty_coer1 in
      (t1, t2)
  | QualTyCoer (ty_cons, ty_coer1) ->
      check_well_formed_ty_cons st ty_cons ;
      let t1, t2 = type_of_ty_coercion st ty_coer1 in
      (QualTy (ty_cons, t1), QualTy (ty_cons, t2))
  | QualDirtCoer (dirt_cons, ty_coer1) ->
      check_well_formed_dirt_cons st dirt_cons ;
      let t1, t2 = type_of_ty_coercion st ty_coer1 in
      (QualDirt (dirt_cons, t1), QualDirt (dirt_cons, t2))
  | ApplyQualTyCoer (ty_coer1, ty_coer_applied) -> (
      let ty_coer_applied_cons = type_of_ty_coercion st ty_coer_applied in
      match type_of_ty_coercion st ty_coer1 with
      | QualTy (cons1, t1), QualTy (cons2, t2) ->
          assert (cons1 = cons2 && cons2 = ty_coer_applied_cons) ;
          (t1, t2)
      | _ -> assert false )
  | ApplyQualDirtCoer (ty_coer1, dirt_coer_applied) -> (
      let dirt_coer_applied_cons =
        type_of_dirt_coercion st dirt_coer_applied
      in
      match type_of_ty_coercion st ty_coer1 with
      | QualDirt (cons1, t1), QualDirt (cons2, t2) ->
          assert (cons1 = cons2 && cons2 = dirt_coer_applied_cons) ;
          (t1, t2)
      | _ -> assert false )
  | _ -> failwith "Not yet implemented"


and type_of_dirty_coercion st dirty_coer =
  match dirty_coer with
  | BangCoercion (tc, dc) ->
      let t1, t2 = type_of_ty_coercion st tc in
      let d1, d2 = type_of_dirt_coercion st dc in
      ((t1, d1), (t2, d2))
  | RightArrow tc -> (
    match type_of_ty_coercion st tc with
    | Types.Arrow (_, c1), Types.Arrow (_, c2) -> (c1, c2)
    | _ -> assert false )
  | RightHandler tc -> (
    match type_of_ty_coercion st tc with
    | Types.Handler (_, c1), Types.Handler (_, c2) -> (c1, c2)
    | _ -> assert false )
  | LeftHandler tc -> (
    match type_of_ty_coercion st tc with
    | Types.Handler (c2, _), Types.Handler (c1, _) -> (c1, c2)
    | _ -> assert false )
  | SequenceDirtyCoer (dc1, dc2) ->
      let t1, t2 = type_of_dirty_coercion st dc1 in
      let t2, t3 = type_of_dirty_coercion st dc2 in
      (t1, t3)


and type_of_dirt_coercion st dirt_coer =
  match dirt_coer with
  | ReflDirt d -> (d, d)
  | DirtCoercionVar p -> (
    match OldUtils.lookup p st.dirt_coer_types with
    | None -> assert false
    | Some pi -> pi )
  | Empty d ->
      check_well_formed_dirt st d ;
      (Types.empty_dirt, d)
  | UnionDirt (es, dirt_coer1) ->
      let dc_a, dc_b = type_of_dirt_coercion st dirt_coer1 in
      (Types.add_effects es dc_a, Types.add_effects es dc_b)
  | SequenceDirtCoer (dc1, dc2) ->
      let t1, t2 = type_of_dirt_coercion st dc1 in
      let t2, t3 = type_of_dirt_coercion st dc2 in
      (t1, t3)
  | DirtCoercion dirty_coer1 ->
      let (_, t1), (_, t2) = type_of_dirty_coercion st dirty_coer1 in
      (t1, t2)


let rec extend_pattern_types st p ty =
  match p.term with
  | PVar x -> extend_var_types st x ty
  | PNonbinding -> st
  | PConst c ->
      let ty_c =
        ExplicitInfer.source_to_target (ExplicitInfer.ty_of_const c)
      in
      assert (Types.types_are_equal ty_c ty) ;
      st
  | _ -> failwith "Not yet implemented"


let type_of_const = function
  | Const.Integer _ -> Types.PrimTy IntTy
  | Const.String _ -> Types.PrimTy StringTy
  | Const.Boolean _ -> Types.PrimTy BoolTy
  | Const.Float _ -> Types.PrimTy FloatTy


let rec type_of_expression st e =
  match e with
  | Var v -> (
    match OldUtils.lookup v st.var_types with
    | Some ty -> ty
    | _ -> assert false )
  | Const const -> type_of_const const
  | Lambda (pat, ty1, c1) ->
      check_well_formed_ty st ty1 ;
      let st' = extend_pattern_types st pat ty1 in
      let c_ty = type_of_computation st' c1.term in
      Types.Arrow (ty1, c_ty)
  | Effect (eff, (eff_in, eff_out)) ->
      Types.Arrow
        (eff_in, (eff_out, Types.closed_dirt (EffectSet.singleton eff)))
  | Handler h -> type_of_handler st h
  | BigLambdaTy (ty_param, skel, e1) ->
      let st' = extend_ty_param_skeletons st ty_param skel in
      let e1_ty = type_of_expression st' e1.term in
      TySchemeTy (ty_param, skel, e1_ty)
  | BigLambdaSkel (skel_param, e1) ->
      let st' = extend_skel_params st skel_param in
      let e1_ty = type_of_expression st' e1.term in
      TySchemeSkel (skel_param, e1_ty)
  | BigLambdaDirt (dirt_param, e1) ->
      let st' = extend_dirt_params st dirt_param in
      let e1_ty = type_of_expression st' e1.term in
      TySchemeDirt (dirt_param, e1_ty)
  | CastExp (e1, tc1) ->
      let e1_ty = type_of_expression st e1.term in
      let tc1a, tc1b = type_of_ty_coercion st tc1 in
      assert (Types.types_are_equal tc1a e1_ty) ;
      tc1b
  | ApplyTyExp (e1, tty) -> (
    match type_of_expression st e1.term with
    | Types.TySchemeTy (p_e1, skel, ty_e1) ->
        check_well_formed_ty st tty ;
        let sub = Unification.TyParamToTy (p_e1, tty) in
        Unification.apply_sub_ty sub ty_e1
    | _ -> assert false )
  | ApplySkelExp (e1, sk) -> (
    match type_of_expression st e1.term with
    | Types.TySchemeSkel (p_e1, ty_e1) ->
        check_well_formed_skeleton st sk ;
        let sub = Unification.SkelParamToSkel (p_e1, sk) in
        Unification.apply_sub_ty sub ty_e1
    | _ -> assert false )
  | ApplyDirtExp (e1, d1) -> (
    match type_of_expression st e1.term with
    | Types.TySchemeDirt (p_e1, ty_e1) ->
        check_well_formed_dirt st d1 ;
        let sub = Unification.DirtVarToDirt (p_e1, d1) in
        Unification.apply_sub_ty sub ty_e1
    | _ -> assert false )
  | LambdaTyCoerVar (tcp1, ct_ty1, e1) ->
      let st' = extend_ty_coer_types st tcp1 ct_ty1 in
      let e1_ty = type_of_expression st' e1.term in
      check_well_formed_ty_cons st ct_ty1 ;
      Types.QualTy (ct_ty1, e1_ty)
  | LambdaDirtCoerVar (dcp1, ct_dirt1, e1) ->
      let st' = extend_dirt_coer_types st dcp1 ct_dirt1 in
      let e1_ty = type_of_expression st' e1.term in
      check_well_formed_dirt_cons st ct_dirt1 ;
      Types.QualDirt (ct_dirt1, e1_ty)
  | ApplyTyCoercion (e1, tc1) -> (
      let tc1' = type_of_ty_coercion st tc1 in
      match type_of_expression st e1.term with
      | QualTy (cons, e1_ty) ->
          assert (tc1' = cons) ;
          e1_ty
      | _ -> assert false )
  | ApplyDirtCoercion (e1, dc1) ->
      let dc1' = type_of_dirt_coercion st dc1 in
      match type_of_expression st e1.term with
      | QualDirt (cons, e1_ty) ->
          assert (dc1' = cons) ;
          e1_ty
      | _ -> assert false
      | _ -> failwith "Not yet implemented"

and type_of_computation st c =
  match c with
  | Value e ->
      let ty1 = type_of_expression st e.term in
      (ty1, Types.empty_dirt)
  | LetVal (e1, (p1, ty, c1)) ->
      let t_v = type_of_expression st e1.term in
      assert (Types.types_are_equal t_v ty) ;
      let st' = extend_pattern_types st p1 t_v in
      type_of_computation st' c1.term
  | Match (e, alist) -> (
      let t_e = type_of_expression st e.term in
      let ty_list = List.map (type_of_abstraction st t_e) alist in
      match ty_list with
      | [] -> assert false
      | dty :: dtys ->
          assert (List.for_all (Types.dirty_types_are_equal dty) dtys) ;
          dty )
  | Apply (e1, e2) -> (
    match type_of_expression st e1.term with
    | Types.Arrow (ty1, dty1) ->
        let ty_e2 = type_of_expression st e2.term in
        assert (Types.types_are_equal ty1 ty_e2) ;
        dty1
    | _ -> assert false )
  | Handle (e1, c1) -> (
    match type_of_expression st e1.term with
    | Types.Handler (dty1, dty2) ->
        let ty_c1 = type_of_computation st c1.term in
        assert (Types.dirty_types_are_equal dty1 ty_c1) ;
        dty2
    | _ -> assert false )
  | Call ((eff, (eff_in, eff_out)), e2, abs) ->
      let e2_ty = type_of_expression st e2.term in
      assert (Types.types_are_equal e2_ty eff_in) ;
      let p, ty_eff, c1 = abs.term in
      let st' = extend_pattern_types st p eff_out in
      let final_ty, final_dirt = type_of_computation st' c1.term in
      assert (Types.EffectSet.mem eff final_dirt.Types.effect_set) ;
      (final_ty, final_dirt)
  | Bind (c1, a1) ->
      let c1_ty, c1_drt = type_of_computation st c1.term in
      let p, c2 = a1.term in
      let st' = extend_pattern_types st p c1_ty in
      let c2_ty, c2_drt = type_of_computation st' c2.term in
      assert (Types.dirts_are_equal c1_drt c2_drt) ;
      (c2_ty, c2_drt)
  | CastComp (c1, dc) ->
      let c1_drty_ty = type_of_computation st c1.term in
      let dc11, dc2 = type_of_dirty_coercion st dc in
      assert (Types.dirty_types_are_equal c1_drty_ty dc11) ;
      dc2
  | LetRec ([(var,ty,e1)],c1) ->
      let st' = extend_var_types st var ty in 
      assert (Types.types_are_equal ty (type_of_expression st' e1.term));
      type_of_computation st' c1.term
  | _ -> failwith "Not yet implemented"

and type_of_handler st h =
  let tv, type_cv = type_of_abstraction_with_ty st h.value_clause in
  let mapper (effe, abs2) =
    let eff, (in_op_ty, out_op_ty) = effe in
    let x, y, c_op = abs2.term in
    let st' = extend_pattern_types st x in_op_ty in
    let st'' = extend_pattern_types st' y (Types.Arrow (out_op_ty, type_cv)) in
    let ty_op = type_of_computation st'' c_op.term in
    assert (Types.dirty_types_are_equal type_cv ty_op) ;
    eff
  in
  let handlers_ops = OldUtils.map mapper h.effect_clauses in
  let handlers_ops_set = Types.EffectSet.of_list handlers_ops in
  let t_cv, d_cv = type_cv in
  let input_dirt = Types.add_effects handlers_ops_set d_cv in
  Types.Handler ((tv, input_dirt), type_cv)

and type_of_abstraction st ty {term= pv, cv} =
  let st' = extend_pattern_types st pv ty in
  type_of_computation st' cv.term

and type_of_abstraction_with_ty st {term= pv, tv, cv} =
  let st' = extend_pattern_types st pv tv in
  (tv, type_of_computation st' cv.term)
