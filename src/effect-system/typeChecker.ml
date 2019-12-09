open Typed
open Types
open Unification

type state =
  { var_types: (Typed.variable, Types.target_ty) Assoc.t
  ; ty_params: CoreTypes.TyParam.t list
  ; dirt_params: CoreTypes.DirtParam.t list
  ; skel_params: CoreTypes.SkelParam.t list
  ; ty_param_skeletons: (CoreTypes.TyParam.t, Types.skeleton) Assoc.t
  ; ty_coer_types: (CoreTypes.TyCoercionParam.t, Types.ct_ty) Assoc.t
  ; dirt_coer_types: (CoreTypes.DirtCoercionParam.t, Types.ct_dirt) Assoc.t }


let extend_ty_params st ty_var = {st with ty_params= ty_var :: st.ty_params}

let extend_var_types st t_var tty =
  {st with var_types= Assoc.update t_var tty st.var_types}

let addExternal st x ty = extend_var_types st x ty

let extend_dirt_params st dirt_var =
  {st with dirt_params= dirt_var :: st.dirt_params}

let extend_skel_params st sk_var =
  {st with skel_params= sk_var :: st.skel_params}

let extend_ty_coer_types st tcp ctty =
  {st with ty_coer_types= Assoc.update tcp ctty st.ty_coer_types}

let extend_dirt_coer_types st tcp ctdrt =
  {st with dirt_coer_types= Assoc.update tcp ctdrt st.dirt_coer_types}

let extend_ty_param_skeletons st tv sk =
  {st with ty_param_skeletons= Assoc.update tv sk st.ty_param_skeletons}

let initial_state =
  { var_types= Assoc.empty
  ; ty_params= []
  ; dirt_params= []
  ; skel_params= []
  ; ty_param_skeletons= Assoc.empty
  ; ty_coer_types= Assoc.empty
  ; dirt_coer_types= Assoc.empty }

let rec check_well_formed_skeleton st = function
  | SkelParam skel_param -> assert (List.mem skel_param st.skel_params)
  | PrimSkel p -> ()
  | SkelArrow (sk1, sk2) ->
      check_well_formed_skeleton st sk1 ;
      check_well_formed_skeleton st sk2
  | SkelHandler (sk1, sk2) ->
      check_well_formed_skeleton st sk1 ;
      check_well_formed_skeleton st sk2
  | _ -> failwith __LOC__

let checkWellFormedDirt st = function
  | {Types.row= Types.EmptyRow} -> ()
  | {Types.row= Types.ParamRow v} -> assert (List.mem v st.dirt_params)

let rec checkWellFormedValTyTemp st = function
  | TyParam typ ->
      let ty_var_list = Assoc.keys_of st.ty_param_skeletons in
      assert (List.mem typ ty_var_list)
  | Arrow (tty1, tty2) ->
      checkWellFormedValTy st tty1 ;
      checkWellFormedCmpTy st tty2
  | Tuple ttyl -> List.iter (checkWellFormedValTy st) ttyl
  | Apply (_, []) -> () (* GEORGE: There is no need for this to be partial I think *)
  | Handler (tty1, tty2) ->
      checkWellFormedCmpTy st tty1 ;
      checkWellFormedCmpTy st tty2
  | PrimTy _ -> ()
  | QualTy (ct_ty1, tty1) ->
      checkWellFormedTyCt st ct_ty1 ;
      checkWellFormedValTy st tty1
  | QualDirt (ct_ty1, tty1) ->
      checkWellFormedDirtCt st ct_ty1 ;
      checkWellFormedValTy st tty1
  | TySchemeDirt (dirt_param, tty1) ->
      let st' = extend_dirt_params st dirt_param in
      checkWellFormedValTy st' tty1

and checkWellFormedValTy st ty =
  Print.debug "checkWellFormedValTy (%t){" (Types.print_target_ty ty);
  checkWellFormedValTyTemp st ty;
  Print.debug "checkWellFormedValTy (%t)}" (Types.print_target_ty ty)

and checkWellFormedCmpTy st (ty, drt) =
  Print.debug "checkWellFormedCmpTy (%t){" (Types.print_target_dirty (ty, drt));
  checkWellFormedValTy st ty ;
  checkWellFormedDirt  st drt ;
  Print.debug "checkWellFormedCmpTy (%t)}" (Types.print_target_dirty (ty, drt));

and checkWellFormedTyCt (st : state) ((t1,t2) : Types.ct_ty) =
  Print.debug "checkWellFormedTyCt (%t){" (Types.print_ct_ty (t1,t2));
  checkWellFormedValTy st t1 ;
  checkWellFormedValTy st t2 ;
  Print.debug "checkWellFormedTyCt (%t)}" (Types.print_ct_ty (t1,t2))

and checkWellFormedDirtCt (st : state) ((d1,d2) : Types.ct_dirt) =
  Print.debug "checkWellFormedDirtCt (%t){" (Types.print_ct_dirt (d1,d2));
  checkWellFormedDirt st d1 ;
  checkWellFormedDirt st d2 ;
  Print.debug "checkWellFormedDirtCt (%t)}" (Types.print_ct_dirt (d1,d2))

(* Typecheck a value-type coercion *)
let rec tcValTyCoTemp st = function
  | ReflTy vty -> (vty, vty)
  | ArrowCoercion (vco,cco) ->
      let vty2, vty1 = tcValTyCo st vco in
      let cty1, cty2 = tcCmpTyCo st cco in
      (Types.Arrow (vty1,cty1), Types.Arrow (vty2,cty2))
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      let c3, c1 = tcCmpTyCo st dirtycoer1 in
      let c2, c4 = tcCmpTyCo st dirtycoer2 in
      (Types.Handler (c1, c2), Types.Handler (c3, c4))
  | TupleCoercion tycoers ->
      let tys1, tys2 = tcManyValCo st tycoers in
      (Types.Tuple tys1, Types.Tuple tys2)
  | ApplyCoercion (ty_name, tycoers) ->
      let tys1, tys2 = tcManyValCo st tycoers in
      (Types.Apply (ty_name, tys1), Types.Apply (ty_name, tys2))
  | TyCoercionVar p -> (
    match Assoc.lookup p st.ty_coer_types with
    | None -> assert false
    | Some pi -> pi )
  | SequenceTyCoer (ty_coer1, ty_coer2) ->
      let t1 , t2 = tcValTyCo st ty_coer1 in
      let t2', t3 = tcValTyCo st ty_coer2 in
      assert (Types.types_are_equal t2 t2');
      (t1, t3)
  | LeftArrow tc1 -> (
    match tcValTyCo st tc1 with
    | Types.Arrow (t1, _), Types.Arrow (t2, _) -> (t2, t1)
    | _ -> assert false )
  | ForallDirt (dirt_param, ty_coer1) ->
      let new_st = extend_dirt_params st dirt_param in
      let t1, t2 = tcValTyCo new_st ty_coer1 in
      (Types.TySchemeDirt (dirt_param, t1), Types.TySchemeDirt (dirt_param, t2))
  | ApplyDirtCoer (ty_coer1, drt) -> (
    match tcValTyCo st ty_coer1 with
    | Types.TySchemeDirt (drt_param1, t1), Types.TySchemeDirt (drt_param2, t2) ->
        checkWellFormedDirt st drt ;
        let sub = Substitution.add_dirt_substitution_e drt_param1 drt in
        assert (drt_param1 = drt_param2) ;
        (Substitution.apply_substitutions_to_type sub t1, Substitution.apply_substitutions_to_type sub t2)
    | _ -> assert false )
  | PureCoercion dirty_coer1 ->
      let (t1, _), (t2, _) = tcCmpTyCo st dirty_coer1 in
      (t1, t2)
  | QualTyCoer (ty_cons, ty_coer1) ->
      checkWellFormedTyCt st ty_cons ;
      let t1, t2 = tcValTyCo st ty_coer1 in
      (QualTy (ty_cons, t1), QualTy (ty_cons, t2))
  | QualDirtCoer (dirt_cons, ty_coer1) ->
      checkWellFormedDirtCt st dirt_cons ;
      let t1, t2 = tcValTyCo st ty_coer1 in
      (QualDirt (dirt_cons, t1), QualDirt (dirt_cons, t2))
  | ApplyQualTyCoer (ty_coer1, ty_coer_applied) -> (
      let ty_coer_applied_cons = tcValTyCo st ty_coer_applied in
      match tcValTyCo st ty_coer1 with
      | QualTy (cons1, t1), QualTy (cons2, t2) ->
          assert (cons1 = cons2 && cons2 = ty_coer_applied_cons) ;
          (t1, t2)
      | _ -> assert false )
  | ApplyQualDirtCoer (ty_coer1, dirt_coer_applied) -> (
      let dirt_coer_applied_cons =
        tcDirtCo st dirt_coer_applied
      in
      match tcValTyCo st ty_coer1 with
      | QualDirt (cons1, t1), QualDirt (cons2, t2) ->
          assert (cons1 = cons2 && cons2 = dirt_coer_applied_cons) ;
          (t1, t2)
      | _ -> assert false )
  | _ -> failwith __LOC__

(* Typecheck a value-type coercion *)
and tcValTyCo st co =
  Print.debug "tcValTyCo (%t){" (Typed.print_ty_coercion co);
  let res = tcValTyCoTemp st co in
  Print.debug "tcValTyCo (%t)}" (Typed.print_ty_coercion co);
  res

(* Typecheck a computation-type coercion *)
and tcCmpTyCoTemp st = function
  | BangCoercion (tc, dc) ->
      let t1, t2 = tcValTyCo st tc in
      let d1, d2 = tcDirtCo st dc in
      ((t1, d1), (t2, d2))
  | RightArrow tc -> (
    match tcValTyCo st tc with
    | Types.Arrow (_, c1), Types.Arrow (_, c2) -> (c1, c2)
    | _ -> assert false )
  | RightHandler tc -> (
    match tcValTyCo st tc with
    | Types.Handler (_, c1), Types.Handler (_, c2) -> (c1, c2)
    | _ -> assert false )
  | LeftHandler tc -> (
    match tcValTyCo st tc with
    | Types.Handler (c2, _), Types.Handler (c1, _) -> (c1, c2)
    | _ -> assert false )
  | SequenceDirtyCoer (dc1, dc2) ->
      let t1 , t2 = tcCmpTyCo st dc1 in
      let t2', t3 = tcCmpTyCo st dc2 in
      assert (Types.dirty_types_are_equal t2 t2') ;
      (t1, t3)

(* Typecheck a computation-type coercion *)
and tcCmpTyCo st co =
  Print.debug "tcCmpTyCo (%t){" (Typed.print_dirty_coercion co);
  let res = tcCmpTyCoTemp st co in
  Print.debug "tcCmpTyCo (%t)}" (Typed.print_dirty_coercion co);
  res

and tcManyValCo st coercions =
  List.fold_right
    (fun co (tys1, tys2) ->
      let ty1, ty2 = tcValTyCo st co in
      (ty1 :: tys1, ty2 :: tys2) )
    coercions ([], [])

(* Typecheck a dirt coercion *)
and tcDirtCoTemp st = function
  | ReflDirt d -> (d, d)
  | DirtCoercionVar p ->
    (match Assoc.lookup p st.dirt_coer_types with
     | Some pi -> pi
     | None    -> failwith __LOC__
    )
  | Empty d ->
      checkWellFormedDirt st d ;
      (Types.empty_dirt, d)
  | UnionDirt (es, dirt_coer1) ->
      let dc_a, dc_b = tcDirtCo st dirt_coer1 in
      (Types.add_effects es dc_a, Types.add_effects es dc_b)
  | SequenceDirtCoer (dc1, dc2) ->
      let t1 , t2 = tcDirtCo st dc1 in
      let t2', t3 = tcDirtCo st dc2 in
      assert (Types.dirts_are_equal t2 t2');
      (t1, t3)
  | DirtCoercion dirty_coer1 ->
      let (_, t1), (_, t2) = tcCmpTyCo st dirty_coer1 in
      (t1, t2)

(* Typecheck a dirt coercion *)
and tcDirtCo st co =
  Print.debug "tcDirtCo (%t){" (Typed.print_dirt_coercion co);
  let res = tcDirtCoTemp st co in
  Print.debug "tcDirtCo (%t)}" (Typed.print_dirt_coercion co);
  res

let rec extendPatternTypesTemp st p ty =
  match p with
  | PVar x -> extend_var_types st x ty
  | PNonbinding -> st
  | PConst c ->
      let ty_c = Types.type_const c in
      assert (Types.types_are_equal ty_c ty) ;
      st
  | PVariant (lbl, p) ->
      let ty_in, ty_out = Types.constructor_signature lbl in
      assert (Types.types_are_equal ty ty_out) ;
      extendPatternTypes st p ty_in
  | PTuple ps -> (
    match ty with
    | Tuple tys -> List.fold_left2 extendPatternTypes st ps tys
    | _ -> assert false )
  | _ -> failwith __LOC__

and extendPatternTypes st p ty =
  Print.debug "extendPatternTypes{" ;
  let res = extendPatternTypesTemp st p ty in
  Print.debug "extendPatternTypes}" ;
  res


let type_of_const =  function
  | Const.Integer _ -> Types.PrimTy IntTy
  | Const.String _ -> Types.PrimTy StringTy
  | Const.Boolean _ -> Types.PrimTy BoolTy
  | Const.Float _ -> Types.PrimTy FloatTy


let rec typeOfExpressionTemp st = function (*  (%t) (Typed.print_expression inputExpression); *)
  | Var v -> (
    (*Print.debug "right before the lookup"; *)
    match Assoc.lookup v st.var_types with
    | Some ty -> (*Print.debug "right after the lookup (%t)" (Types.print_target_ty ty); *) ty
    | _ -> assert false )
  | Const const -> type_of_const const
  | Lambda abs ->
      let ty1, c_ty = type_of_abstraction_with_ty st abs in
      Types.Arrow (ty1, c_ty)
  | Tuple es -> Types.Tuple (List.map (fun e -> typeOfExpression st e) es)
  | Variant (lbl, e) ->
      let ty_in, ty_out = Types.constructor_signature lbl in
      let u' = typeOfExpression st e in
      assert (Types.types_are_equal u' ty_in) ;
      ty_out
  | Effect (eff, (eff_in, eff_out)) ->
      Types.Arrow
        (eff_in, (eff_out, Types.closed_dirt (EffectSet.singleton eff)))
  | Handler h -> type_of_handler st h
  | BigLambdaDirt (dirt_param, e1) ->
      let st' = extend_dirt_params st dirt_param in
      let e1_ty = typeOfExpression st' e1 in
      TySchemeDirt (dirt_param, e1_ty)
  | CastExp (e1, tc1) ->
      let e1_ty = typeOfExpression st e1 in
      Print.debug "CastExp: before tcValTyCo";
      let tc1a, tc1b = tcValTyCo st tc1 in
      Print.debug "CastExp: after  tcValTyCo";
      assert (Types.types_are_equal tc1a e1_ty) ;
      tc1b
  | ApplyDirtExp (e1, d1) -> (
    match typeOfExpression st e1 with
    | Types.TySchemeDirt (p_e1, ty_e1) ->
        Print.debug "ApplyDirtExp 1";
        checkWellFormedDirt st d1 ;
        Print.debug "ApplyDirtExp 2";
        (* Avoid capture *)
        let freshDVar   = CoreTypes.DirtParam.fresh () in
        let renamedType = Types.rnDirtVarInValTy p_e1 freshDVar ty_e1 in
        let sub = Substitution.add_dirt_substitution_e freshDVar d1 in
(*
        let sub = Substitution.add_dirt_substitution_e p_e1 d1 in
*)
        Print.debug "ApplyDirtExp 3";
        Substitution.print_substitutions sub;
        let res = Substitution.apply_substitutions_to_type sub renamedType in
(*
        let res = Substitution.apply_substitutions_to_type sub ty_e1 in
*)
        Print.debug "ApplyDirtExp 4";
        res
    | _ -> assert false )
  | LambdaTyCoerVar (tcp1, ct_ty1, e1) ->
      let st' = extend_ty_coer_types st tcp1 ct_ty1 in
      let e1_ty = typeOfExpression st' e1 in
      checkWellFormedTyCt st ct_ty1 ;
      Types.QualTy (ct_ty1, e1_ty)
  | LambdaDirtCoerVar (dcp1, ct_dirt1, e1) ->
      let st' = extend_dirt_coer_types st dcp1 ct_dirt1 in
      let e1_ty = typeOfExpression st' e1 in
      checkWellFormedDirtCt st ct_dirt1 ;
      Types.QualDirt (ct_dirt1, e1_ty)
  | ApplyTyCoercion (e1, tc1) -> (
      let tc1' = tcValTyCo st tc1 in
      match typeOfExpression st e1 with
      | QualTy (cons, e1_ty) ->
          assert (tc1' = cons) ;
          e1_ty
      | _ -> assert false )
  | ApplyDirtCoercion (e1, dc1) -> (
      let dc1' = tcDirtCo st dc1 in
      match typeOfExpression st e1 with
      | QualDirt (cons, e1_ty) ->
          assert (dc1' = cons) ;
          e1_ty
      | _ -> assert false )
  | _ -> failwith __LOC__

and typeOfExpression st e =
  Print.debug "typeOfExpression (%t){" (Typed.print_expression e);
  let res = typeOfExpressionTemp st e in
  Print.debug "typeOfExpression (%t)}" (Typed.print_expression e);
  res

and typeOfComputationTemp st = function
  | Value e ->
      let ty1 = typeOfExpression st e in
      (ty1, Types.empty_dirt)
  | LetVal (e1, abs) ->
      let t_v = typeOfExpression st e1
      and ty_in, ty_out = type_of_abstraction_with_ty st abs in
      assert (Types.types_are_equal t_v ty_in) ;
      ty_out
  | Match (e, resTy, alist, _) -> (
      let t_e = typeOfExpression st e in
      let ty_list = List.map (type_of_abstraction st t_e) alist in
      checkWellFormedCmpTy st resTy ;
      assert (List.for_all (Types.dirty_types_are_equal resTy) ty_list) ;
      resTy )
  | Apply (e1, e2) -> (
    match typeOfExpression st e1 with
    | Types.Arrow (ty1, dty1) ->
        let ty_e2 = typeOfExpression st e2 in
        assert (Types.types_are_equal ty1 ty_e2) ;
        dty1
    | _ -> assert false )
  | Handle (e1, c1) -> (
    match typeOfExpression st e1 with
    | Types.Handler (dty1, dty2) ->
        let ty_c1 = typeOfComputation st c1 in
        assert (Types.dirty_types_are_equal dty1 ty_c1) ;
        dty2
    | _ -> assert false )
  | Call ((eff, (eff_in, eff_out)), e2, abs) ->
      let e2_ty = typeOfExpression st e2 in
      assert (Types.types_are_equal e2_ty eff_in) ;
      let p, ty_eff, c1 = abs in
      let st' = extendPatternTypes st p eff_out in
      let final_ty, final_dirt = typeOfComputation st' c1 in
      assert (Types.EffectSet.mem eff final_dirt.Types.effect_set) ;
      (final_ty, final_dirt)
  | Bind (c1, (p, c2)) ->
      let c1_ty, c1_drt = typeOfComputation st c1 in
      let st' = extendPatternTypes st p c1_ty in
      let c2_ty, c2_drt = typeOfComputation st' c2 in
      assert (Types.dirts_are_equal c1_drt c2_drt) ;
      (c2_ty, c2_drt)
  | CastComp (c1, dc) ->
      let c1_drty_ty = typeOfComputation st c1 in
      Print.debug "CastComp: before tcCmpTyCo";
      let dc11, dc2 = tcCmpTyCo st dc in
      Print.debug "CastComp: after  tcCmpTyCo";
      if Types.dirty_types_are_equal c1_drty_ty dc11
        then dc2
        else ( Print.debug "typeOfComputation(CastComp): %t ~/~ %t"
                 (Types.print_target_dirty c1_drty_ty)
                 (Types.print_target_dirty dc11)
             ; Print.debug "typeOfComputation(CastComp): %t"
                 (Typed.print_computation c1)
             ; Print.debug "coercion(CastComp): %t" (Typed.print_dirty_coercion dc)
             ; assert (Types.dirty_types_are_equal c1_drty_ty dc11)
             ; failwith "canthappen"
             )
  | LetRec ([(f, argTy, resTy, (pat, rhs))], c) ->
      checkWellFormedValTy st argTy ;
      checkWellFormedCmpTy st resTy ;
      let st'  = extend_var_types st f (Types.Arrow (argTy,resTy)) in
      let st'' = extendPatternTypes st' pat argTy in
      let tempTy = typeOfComputation st'' rhs in
      assert (Types.dirty_types_are_equal resTy tempTy) ;
      typeOfComputation st' c (* NOTE: Do not use the pattern bindings! :-) *)
  | _ -> failwith __LOC__

and typeOfComputation st c =
  Print.debug "typeOfComputation (%t){" (Typed.print_computation c);
  let res = typeOfComputationTemp st c in
  Print.debug "typeOfComputation (%t)}" (Typed.print_computation c);
  res

and type_of_handler st h =
  Print.debug "type_of_handler{";
  let tv, type_cv = type_of_abstraction_with_ty st h.value_clause in
  let mapper (effe, abs2) =
    let eff, (in_op_ty, out_op_ty) = effe in
    let x, y, c_op = abs2 in
    let st' = extendPatternTypes st x in_op_ty in
    let st'' = extendPatternTypes st' y (Types.Arrow (out_op_ty, type_cv)) in
    let ty_op = typeOfComputation st'' c_op in
    assert (Types.dirty_types_are_equal type_cv ty_op) ;
    eff
  in
  let handlers_ops = List.map mapper (Assoc.to_list h.effect_clauses) in
  let handlers_ops_set = Types.EffectSet.of_list handlers_ops in
  let t_cv, d_cv = type_cv in
  let input_dirt = Types.add_effects handlers_ops_set d_cv in
  let res = Types.Handler ((tv, input_dirt), type_cv) in
  Print.debug "type_of_handler}";
  res

and type_of_abstraction st ty (pv, cv) =
  Print.debug "type_of_abstraction{";
  let st' = extendPatternTypes st pv ty in
  let res = typeOfComputation st' cv in
  Print.debug "type_of_abstraction}";
  res

and type_of_abstraction_with_ty st (pv, tv, cv) =
  Print.debug "type_of_abstraction_with_ty{";
  checkWellFormedValTy st tv ;
  let st' = extendPatternTypes st pv tv in
  let res = (tv, typeOfComputation st' cv) in
  Print.debug "type_of_abstraction_with_ty}";
  res

