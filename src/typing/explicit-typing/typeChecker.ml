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


let extend_pattern_types st p ty =
  match p.term with
  | Typed.PVar v -> extend_var_types st v ty
  | _ -> failwith "Not yet implemented"


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


let rec type_check_skel st sk =
  match sk with
  | SkelParam skel_param when List.mem skel_param st.skel_params -> sk
  | PrimSkel p -> PrimSkel p
  | SkelArrow (sk1, sk2) ->
      SkelArrow (type_check_skel st sk1, type_check_skel st sk2)
  | SkelHandler (sk1, sk2) ->
      SkelHandler (type_check_skel st sk1, type_check_skel st sk2)
  | ForallSkel (skp, sk1) ->
      let st' = extend_skel_params st skp in
      ForallSkel (skp, type_check_skel st' sk1)
  | _ -> failwith "Not yet implemented"


let type_check_dirt st d =
  match d with
  | {Types.effect_set= eset; Types.row= Types.EmptyRow}
    when EffectSet.is_empty eset ->
      d
  | {Types.row= Types.EmptyRow} -> d
  | {Types.row= Types.ParamRow v} ->
      assert (List.mem v st.dirt_params) ;
      d


let rec type_check_ty st ty =
  Print.debug "NOW CHECKING %t" (Types.print_target_ty ty) ;
  match ty with
  | TyParam typ ->
      let ty_var_list = List.map (fun (x, y) -> x) st.ty_param_skeletons in
      assert (List.mem typ ty_var_list) ;
      ty
  | Arrow (tty1, tty2) ->
      ignore (type_check_ty st tty1) ;
      ignore (type_check_dirty_ty st tty2) ;
      ty
  | Tuple ttyl -> Tuple (List.map (fun x -> type_check_ty st x) ttyl)
  | Handler (tty1, tty2) ->
      ignore (type_check_dirty_ty st tty1) ;
      ignore (type_check_dirty_ty st tty2) ;
      ty
  | PrimTy _ -> ty
  | QualTy (ct_ty1, tty1) ->
      ignore (type_check_ty_cons st ct_ty1) ;
      ignore (type_check_ty st tty1) ;
      ty
  | QualDirt (ct_ty1, tty1) ->
      ignore (type_check_dirt_cons st ct_ty1) ;
      ignore (type_check_ty st tty1) ;
      ty
  | TySchemeTy (ty_param, skel, tty1) ->
      let st' = extend_ty_param_skeletons st ty_param skel in
      ignore (type_check_ty st' tty1) ;
      ty
  | TySchemeDirt (dirt_param, tty1) ->
      let st' = extend_dirt_params st dirt_param in
      ignore (type_check_ty st' tty1) ;
      ty
  | TySchemeSkel (skel_param, tty1) ->
      let st' = extend_skel_params st skel_param in
      ignore (type_check_ty st' tty1) ;
      ty


and type_check_dirty_ty st (ty, drt) =
  ignore (type_check_ty st ty) ;
  ignore (type_check_dirt st drt) ;
  (ty, drt)


and type_check_ty_cons st (t1, t2) =
  let t1' = type_check_ty st t1 in
  let t2' = type_check_ty st t2 in
  (t1', t2')


and type_check_dirt_cons st (d1, d2) =
  let d1' = type_check_dirt st d1 in
  let d2' = type_check_dirt st d2 in
  (d1', d2')


let rec type_check_ty_coercion st ty_coer =
  match ty_coer with
  | ReflTy tty -> (tty, tty)
  | ArrowCoercion (tycoer1, dirtycoer) ->
      let t2, t1 = type_check_ty_coercion st tycoer1 in
      let c1, c2 = type_check_dirty_coercion st dirtycoer in
      (Types.Arrow (t1, c1), Types.Arrow (t2, c2))
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      let c3, c1 = type_check_dirty_coercion st dirtycoer1 in
      let c2, c4 = type_check_dirty_coercion st dirtycoer2 in
      (Types.Handler (c1, c2), Types.Handler (c3, c4))
  | TyCoercionVar p -> (
    match OldUtils.lookup p st.ty_coer_types with
    | None -> assert false
    | Some pi -> pi )
  | SequenceTyCoer (ty_coer1, ty_coer2) ->
      let t1, t2 = type_check_ty_coercion st ty_coer1 in
      let t2, t3 = type_check_ty_coercion st ty_coer2 in
      (t1, t3)
  | LeftArrow tc1 -> (
    match type_check_ty_coercion st tc1 with
    | Types.Arrow (t1, _), Types.Arrow (t2, _) -> (t2, t1)
    | _ -> assert false )
  | ForallTy (ty_param, ty_coer1) ->
      let new_st = extend_ty_params st ty_param in
      let t1, t2 = type_check_ty_coercion new_st ty_coer1 in
      ( Types.TySchemeTy (ty_param, Types.PrimSkel Types.IntTy, t1)
      , Types.TySchemeTy (ty_param, Types.PrimSkel Types.IntTy, t2) )
  | ApplyTyCoer (ty_coer1, tty1) -> (
    match type_check_ty_coercion st ty_coer1 with
    | Types.TySchemeTy (ty_param1, _, t1), Types.TySchemeTy (ty_param2, _, t2) ->
        let tt = type_check_ty st tty1 in
        let sub = Unification.TyParamToTy (ty_param1, tt) in
        assert (ty_param1 = ty_param2) ;
        (Unification.apply_sub_ty sub t1, Unification.apply_sub_ty sub t2)
    | _ -> assert false )
  | ForallDirt (dirt_param, ty_coer1) ->
      let new_st = extend_dirt_params st dirt_param in
      let t1, t2 = type_check_ty_coercion new_st ty_coer1 in
      (Types.TySchemeDirt (dirt_param, t1), Types.TySchemeDirt (dirt_param, t2))
  | ApplyDirCoer (ty_coer1, drt) -> (
    match type_check_ty_coercion st ty_coer1 with
    | Types.TySchemeDirt (drt_param1, t1), Types.TySchemeDirt (drt_param2, t2) ->
        let tt = type_check_dirt st drt in
        let sub = Unification.DirtVarToDirt (drt_param1, tt) in
        assert (drt_param1 = drt_param2) ;
        (Unification.apply_sub_ty sub t1, Unification.apply_sub_ty sub t2)
    | _ -> assert false )
  | PureCoercion dirty_coer1 ->
      let (t1, _), (t2, _) = type_check_dirty_coercion st dirty_coer1 in
      (t1, t2)
  | QualTyCoer (ty_cons, ty_coer1) ->
      let tc1, tc2 = type_check_ty_cons st ty_cons in
      let t1, t2 = type_check_ty_coercion st ty_coer1 in
      (QualTy ((tc1, tc2), t1), QualTy ((tc1, tc2), t2))
  | QualDirtCoer (dirt_cons, ty_coer1) ->
      ignore (type_check_dirt_cons st dirt_cons) ;
      let t1, t2 = type_check_ty_coercion st ty_coer1 in
      (QualDirt (dirt_cons, t1), QualDirt (dirt_cons, t2))
  | ApplyQualTyCoer (ty_coer1, ty_coer_applied) -> (
      let ty_coer_applied_cons = type_check_ty_coercion st ty_coer_applied in
      match type_check_ty_coercion st ty_coer1 with
      | QualTy (cons1, t1), QualTy (cons2, t2) ->
          assert (cons1 = cons2 && cons2 = ty_coer_applied_cons) ;
          (t1, t2)
      | _ -> assert false )
  | ApplyQualDirtCoer (ty_coer1, dirt_coer_applied) -> (
      let dirt_coer_applied_cons =
        type_check_dirt_coercion st dirt_coer_applied
      in
      match type_check_ty_coercion st ty_coer1 with
      | QualDirt (cons1, t1), QualDirt (cons2, t2) ->
          assert (cons1 = cons2 && cons2 = dirt_coer_applied_cons) ;
          (t1, t2)
      | _ -> assert false )
  | _ -> failwith "Not yet implemented"


and type_check_dirty_coercion st dirty_coer =
  match dirty_coer with
  | BangCoercion (tc, dc) ->
      let t1, t2 = type_check_ty_coercion st tc in
      let d1, d2 = type_check_dirt_coercion st dc in
      ((t1, d1), (t2, d2))
  | RightArrow tc -> (
    match type_check_ty_coercion st tc with
    | Types.Arrow (_, c1), Types.Arrow (_, c2) -> (c1, c2)
    | _ -> assert false )
  | RightHandler tc -> (
    match type_check_ty_coercion st tc with
    | Types.Handler (_, c1), Types.Handler (_, c2) -> (c1, c2)
    | _ -> assert false )
  | LeftHandler tc -> (
    match type_check_ty_coercion st tc with
    | Types.Handler (c2, _), Types.Handler (c1, _) -> (c1, c2)
    | _ -> assert false )
  | SequenceDirtyCoer (dc1, dc2) ->
      let t1, t2 = type_check_dirty_coercion st dc1 in
      let t2, t3 = type_check_dirty_coercion st dc2 in
      (t1, t3)


and type_check_dirt_coercion st dirt_coer =
  match dirt_coer with
  | ReflDirt d -> (d, d)
  | DirtCoercionVar p -> (
    match OldUtils.lookup p st.dirt_coer_types with
    | None -> assert false
    | Some pi -> pi )
  | Empty d ->
      let d' = type_check_dirt st d in
      (Types.empty_dirt, d')
  | UnionDirt (es, dirt_coer1) ->
      let dc_a, dc_b = type_check_dirt_coercion st dirt_coer1 in
      let dc_a' = {dc_a with effect_set= EffectSet.union es dc_a.effect_set} in
      let dc_b' = {dc_b with effect_set= EffectSet.union es dc_b.effect_set} in
      (dc_a', dc_b')
  | SequenceDirtCoer (dc1, dc2) ->
      let t1, t2 = type_check_dirt_coercion st dc1 in
      let t2, t3 = type_check_dirt_coercion st dc2 in
      (t1, t3)
  | DirtCoercion dirty_coer1 ->
      let (_, t1), (_, t2) = type_check_dirty_coercion st dirty_coer1 in
      (t1, t2)


let rec type_check_pattern st ty p =
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


let type_check_const = function
  | Const.Integer _ -> Types.PrimTy IntTy
  | Const.String _ -> Types.PrimTy StringTy
  | Const.Boolean _ -> Types.PrimTy BoolTy
  | Const.Float _ -> Types.PrimTy FloatTy


let rec type_check_exp st e =
  match e with
  | Var v -> (
    match OldUtils.lookup v st.var_types with
    | Some ty -> ty
    | _ -> assert false )
  | BuiltIn (s, i) -> failwith "Not yet implemented"
  | Const const -> type_check_const const
  | Tuple elist -> failwith "Not yet implemented"
  | Record r -> failwith "Not yet implemented"
  | Variant (lbl, e1) -> failwith "Not yet implemented"
  | Lambda (pat, ty1, c1) ->
      let ty1' = type_check_ty st ty1 in
      let st' = extend_pattern_types st pat ty1 in
      let c_ty = type_check_comp st' c1.term in
      Types.Arrow (ty1', c_ty)
  | Effect (eff, (eff_in, eff_out)) ->
      Types.Arrow
        (eff_in, (eff_out, Types.closed_dirt (EffectSet.singleton eff)))
  | Handler h -> type_check_handler st h
  | BigLambdaTy (ty_param, skel, e1) ->
      let st' = extend_ty_param_skeletons st ty_param skel in
      let e1_ty = type_check_exp st' e1.term in
      TySchemeTy (ty_param, skel, e1_ty)
  | BigLambdaSkel (skel_param, e1) ->
      let st' = extend_skel_params st skel_param in
      let e1_ty = type_check_exp st' e1.term in
      TySchemeSkel (skel_param, e1_ty)
  | BigLambdaDirt (dirt_param, e1) ->
      let st' = extend_dirt_params st dirt_param in
      let e1_ty = type_check_exp st' e1.term in
      TySchemeDirt (dirt_param, e1_ty)
  | CastExp (e1, tc1) ->
      let e1_ty = type_check_exp st e1.term in
      let tc1a, tc1b = type_check_ty_coercion st tc1 in
      assert (Types.types_are_equal tc1a e1_ty) ;
      tc1b
  | ApplyTyExp (e1, tty) -> (
    match type_check_exp st e1.term with
    | Types.TySchemeTy (p_e1, skel, ty_e1) ->
        let tty1 = type_check_ty st tty in
        let sub = Unification.TyParamToTy (p_e1, tty1) in
        Unification.apply_sub_ty sub ty_e1
    | _ -> assert false )
  | ApplySkelExp (e1, sk) -> (
    match type_check_exp st e1.term with
    | Types.TySchemeSkel (p_e1, ty_e1) ->
        let sk1 = type_check_skel st sk in
        let sub = Unification.SkelParamToSkel (p_e1, sk1) in
        Unification.apply_sub_ty sub ty_e1
    | _ -> assert false )
  | ApplyDirtExp (e1, d1) -> (
    match type_check_exp st e1.term with
    | Types.TySchemeDirt (p_e1, ty_e1) ->
        let tty1 = type_check_dirt st d1 in
        let sub = Unification.DirtVarToDirt (p_e1, tty1) in
        Unification.apply_sub_ty sub ty_e1
    | _ -> assert false )
  | LambdaTyCoerVar (tcp1, ct_ty1, e1) ->
      let st' = extend_ty_coer_types st tcp1 ct_ty1 in
      let e1_ty = type_check_exp st' e1.term in
      let ct_ty1' = type_check_ty_cons st ct_ty1 in
      Types.QualTy (ct_ty1', e1_ty)
  | LambdaDirtCoerVar (dcp1, ct_dirt1, e1) ->
      let st' = extend_dirt_coer_types st dcp1 ct_dirt1 in
      let e1_ty = type_check_exp st' e1.term in
      let ct_dirt1' = type_check_dirt_cons st ct_dirt1 in
      Types.QualDirt (ct_dirt1', e1_ty)
  | ApplyTyCoercion (e1, tc1) -> (
      let tc1' = type_check_ty_coercion st tc1 in
      match type_check_exp st e1.term with
      | QualTy (cons, e1_ty) ->
          assert (tc1' = cons) ;
          e1_ty
      | _ -> assert false )
  | ApplyDirtCoercion (e1, dc1) ->
      let dc1' = type_check_dirt_coercion st dc1 in
      match type_check_exp st e1.term with
      | QualDirt (cons, e1_ty) ->
          assert (dc1' = cons) ;
          e1_ty
      | _ -> assert false

and type_check_comp st c =
  match c with
  | Value e ->
      let ty1 = type_check_exp st e.term in
      (ty1, Types.empty_dirt)
  | LetVal (e1, (p1, ty, c1)) ->
      let t_v = type_check_exp st e1.term in
      assert (Types.types_are_equal t_v ty) ;
      let st' = extend_pattern_types st p1 t_v in
      type_check_comp st' c1.term
  | LetRec (l, c1) -> failwith "Not yet implemented"
  | Match (e, alist) -> (
      let t_e = type_check_exp st e.term in
      let ty_list = List.map (type_check_abstraction st t_e) alist in
      match ty_list with
      | [] -> assert false
      | dty :: dtys ->
          assert (List.for_all (Types.dirty_types_are_equal dty) dtys) ;
          dty )
  | Apply (e1, e2) -> (
    match type_check_exp st e1.term with
    | Types.Arrow (ty1, dty1) ->
        let ty_e2 = type_check_exp st e2.term in
        assert (Types.types_are_equal ty1 ty_e2) ;
        dty1
    | _ -> assert false )
  | Handle (e1, c1) -> (
    match type_check_exp st e1.term with
    | Types.Handler (dty1, dty2) ->
        let ty_c1 = type_check_comp st c1.term in
        assert (Types.dirty_types_are_equal dty1 ty_c1) ;
        dty2
    | _ -> assert false )
  | Call ((eff, (eff_in, eff_out)), e2, abs) ->
      let e2_ty = type_check_exp st e2.term in
      assert (Types.types_are_equal e2_ty eff_in) ;
      let p, ty_eff, c1 = abs.term in
      let st' = extend_pattern_types st p eff_out in
      let final_ty, final_dirt = type_check_comp st' c1.term in
      assert (Types.EffectSet.mem eff final_dirt.Types.effect_set) ;
      (final_ty, final_dirt)
  | Op (ef, e1) -> failwith "Not yet implemented"
  | Bind (c1, a1) -> (
      let c1_ty, c1_drt = type_check_comp st c1.term in
      let x, c2 = a1.term in
      match x.term with
      | Typed.PVar p ->
          let st' = extend_var_types st p c1_ty in
          let c2_ty, c2_drt = type_check_comp st' c2.term in
          assert (Types.dirts_are_equal c1_drt c2_drt) ;
          (c2_ty, c2_drt)
      | Typed.PNonbinding ->
          let c2_ty, c2_drt = type_check_comp st c2.term in
          assert (Types.dirts_are_equal c1_drt c2_drt) ;
          (c2_ty, c2_drt)
      | _ -> failwith "Not yet implemented" )
  | CastComp (c1, dc) ->
      let c1_drty_ty = type_check_comp st c1.term in
      let dc11, dc2 = type_check_dirty_coercion st dc in
      assert (Types.dirty_types_are_equal c1_drty_ty dc11) ;
      dc2
  | CastComp_ty (c1, tc1) -> failwith "Not yet implemented"
  | CastComp_dirt (c1, tc1) -> failwith "Not yet implemented"

and type_check_handler st h =
  let tv, type_cv = type_check_abstraction_with_ty st h.value_clause in
  let mapper (effe, abs2) =
    let eff, (in_op_ty, out_op_ty) = effe in
    let x, y, c_op = abs2.term in
    let st_temp = extend_pattern_types st x in_op_ty in
    let st' =
      extend_pattern_types st_temp y (Types.Arrow (out_op_ty, type_cv))
    in
    ignore (type_check_comp st' c_op.term) ;
    eff
  in
  let handlers_ops = OldUtils.map mapper h.effect_clauses in
  let handlers_ops_set = Types.EffectSet.of_list handlers_ops in
  let t_cv, d_cv = type_cv in
  let input_dirt =
    { d_cv with
      Types.effect_set=
        Types.EffectSet.union d_cv.Types.effect_set handlers_ops_set }
  in
  Types.Handler ((tv, input_dirt), type_cv)

and type_check_abstraction st ty {term= pv, cv} =
  let st' = type_check_pattern st ty pv in
  type_check_comp st' cv.term

and type_check_abstraction_with_ty st {term= pv, tv, cv} =
  let st' = extend_pattern_types st pv tv in
  (tv, type_check_comp st' cv.term)
