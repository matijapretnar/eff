open Utils
module TypeCheckerPrimitives = Primitives
open Language
module Untyped = UntypedSyntax

let identity_instantiation (params : Type.Params.t)
    (constraints : Constraints.t) =
  Substitution.
    {
      type_param_to_type_coercions =
        Constraints.TyConstraints.fold_expanded
          (fun _s _t1 _t2 w ty1 ty2 ->
            Type.TyCoercionParam.Map.add w (Coercion.tyCoercionVar w (ty1, ty2)))
          constraints.ty_constraints Type.TyCoercionParam.Map.empty;
      type_param_to_type_subs =
        params.ty_params |> Type.TyParam.Map.bindings
        |> List.map (fun (p, skel) -> (p, Type.tyParam p skel))
        |> Type.TyParam.Map.of_bindings;
      dirt_var_to_dirt_coercions =
        Constraints.DirtConstraints.fold_expanded
          (fun _d1 _d2 w _effs drt1 drt2 ->
            Type.DirtCoercionParam.Map.add w
              (Coercion.dirtCoercionVar w (drt1, drt2)))
          constraints.dirt_constraints Type.DirtCoercionParam.Map.empty;
      dirt_var_to_dirt_subs =
        params.dirt_params |> Dirt.Param.Set.elements
        |> List.map (fun d -> (d, Dirt.no_effect d))
        |> Dirt.Param.Map.of_bindings;
      skel_param_to_skel_subs =
        params.skel_params |> Language.Skeleton.Param.Set.elements
        |> List.map (fun s -> (s, Language.Skeleton.Param s))
        |> Language.Skeleton.Param.Map.of_bindings;
    }

let fresh_instantiation (params : Type.Params.t) (constraints : Constraints.t) =
  let _, subst = Substitution.of_parameters params in
  let add_dirt_constraint _d1 _d2 w _effs drt1 drt2 (subst, constraints) =
    let w' = Type.DirtCoercionParam.refresh w
    and drt1' = Substitution.apply_substitutions_to_dirt subst drt1
    and drt2' = Substitution.apply_substitutions_to_dirt subst drt2 in
    let coer' = Coercion.dirtCoercionVar w' (drt1', drt2') in
    let subst' = Substitution.add_dirt_var_coercion w coer' subst
    and constraints' =
      Constraint.add_dirt_inequality (w', (drt1', drt2')) constraints
    in
    (subst', constraints')
  in
  let add_ty_constraint _s _t1 _t2 w ty1 ty2 (subst, constraints) =
    let w' = Type.TyCoercionParam.refresh w
    and ty1' = Substitution.apply_substitutions_to_type subst ty1
    and ty2' = Substitution.apply_substitutions_to_type subst ty2 in
    let coer' = Coercion.tyCoercionVar w' (ty1', ty2') in
    let subst' = Substitution.add_type_coercion w coer' subst
    and constraints' =
      Constraint.add_ty_inequality (w', (ty1', ty2')) constraints
    in
    (subst', constraints')
  in
  (subst, Constraint.empty)
  |> Constraints.TyConstraints.fold_expanded add_ty_constraint
       constraints.ty_constraints
  |> Constraints.DirtConstraints.fold_expanded add_dirt_constraint
       constraints.dirt_constraints

type state = {
  variables : TyScheme.t Term.Variable.Map.t;
  effects : (Type.ty * Type.ty) Effect.Map.t;
  type_definitions : TypeDefinitionContext.state;
}

(* Add a single term binding to the global typing environment *)
let extend_poly_var env x ty_scheme =
  { env with variables = Term.Variable.Map.add x ty_scheme env.variables }

let extend_var env x ty = extend_poly_var env x (TyScheme.monotype ty)

(* Initial type inference state: everything is empty *)
let initial_state : state =
  {
    variables = Term.Variable.Map.empty;
    effects = Effect.Map.empty;
    type_definitions = TypeDefinitionContext.initial_state;
  }

(* Typecheck a list of things *)
let rec infer_many infer (xss : 'a list) =
  match xss with
  | [] -> ([], Constraint.empty)
  | x :: xs ->
      let y, cs1 = infer x in
      let ys, cs2 = infer_many infer xs in
      (y :: ys, Constraint.union cs1 cs2)

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

let rec infer_pattern state pat =
  let pat', ty, vars, cnstrs = infer_pattern' ~loc:pat.at state pat.it in
  ({ term = pat'; ty }, vars, cnstrs)

and infer_pattern' ~loc state = function
  | Untyped.PVar x ->
      let alpha = Type.fresh_ty_with_fresh_skel () in
      (Term.PVar x, alpha, Term.Variable.Map.singleton x alpha, Constraint.empty)
  | Untyped.PAnnotated (p, ty) ->
      let p', vars, cnstrs = infer_pattern state p in
      (p'.term, ty, vars, Constraint.add_ty_equality (ty, p'.ty) cnstrs)
  | Untyped.PNonbinding ->
      let alpha = Type.fresh_ty_with_fresh_skel () in
      (Term.PNonbinding, alpha, Term.Variable.Map.empty, Constraint.empty)
  | Untyped.PConst c ->
      ( Term.PConst c,
        Type.type_const c,
        Term.Variable.Map.empty,
        Constraint.empty )
  | Untyped.PTuple ps ->
      let fold p (ps', vars, cnstrs) =
        let p', vars', cnstrs' = infer_pattern state p in
        ( p' :: ps',
          Term.Variable.Map.compatible_union vars vars',
          Constraint.union cnstrs' cnstrs )
      in
      let ps', vars, cnstrs =
        List.fold_right fold ps ([], Term.Variable.Map.empty, Constraint.empty)
      in
      let p = Term.pTuple ps' in
      (p.term, p.ty, vars, cnstrs)
  | Untyped.PVariant (lbl, p) -> (
      match
        (p, TypeDefinitionContext.infer_variant lbl state.type_definitions)
      with
      | None, (None, out_ty) ->
          ( Term.PVariant (lbl, None),
            out_ty,
            Term.Variable.Map.empty,
            Constraint.empty )
      | Some p, (Some in_ty, out_ty) ->
          let p', vars, cnstrs = infer_pattern state p in
          ( Term.PVariant (lbl, Some p'),
            out_ty,
            vars,
            Constraint.add_ty_equality (in_ty, p'.ty) cnstrs )
      | _ -> assert false)
  | Untyped.PAs (p, x) ->
      let p', vars, cnstrs = infer_pattern state p in
      (Term.PAs (p', x), p'.ty, Term.Variable.Map.add x p'.ty vars, cnstrs)
  | Untyped.PRecord flds ->
      let hd_fld, _ = List.hd (Type.Field.Map.bindings flds) in
      let out_ty, (ty_name, fld_tys) =
        TypeDefinitionContext.infer_field hd_fld state.type_definitions
      in
      let fold fld p (flds', vars, cnstrs) =
        let p', vars', cnstrs' = infer_pattern state p in
        match Type.Field.Map.find_opt fld fld_tys with
        | None ->
            Error.typing ~loc "Field %t does not belong to type %t"
              (Type.Field.print fld)
              (Language.TyName.print ty_name)
        | Some fld_ty ->
            ( (fld, p') :: flds',
              Term.Variable.Map.compatible_union vars vars',
              Constraint.union
                (Constraint.add_ty_equality (fld_ty, p'.ty) cnstrs')
                cnstrs )
      in
      let flds', vars, cnstrs' =
        Language.TyName.Map.fold fold flds
          ([], Term.Variable.Map.empty, Constraint.empty)
      in
      (Term.PRecord (Type.Field.Map.of_bindings flds'), out_ty, vars, cnstrs')

let extend_state vars state =
  Term.Variable.Map.fold (fun x ty state -> extend_var state x ty) vars state

(* ************************************************************************* *)
(*                             VALUE TYPING                                  *)
(* ************************************************************************* *)

let rec infer_expression state exp =
  let (trm, ty), cnstrs = infer_expression' state exp.it in
  (* Print.debug "%t -> %t : %t / %t"
     (Untyped.print_expression e)
     (Term.print_expression' trm)
     (Type.print_ty ty) (Constraint.print cnstrs); *)
  ({ term = trm; ty }, cnstrs)

and infer_expression' state = function
  | Untyped.Var x ->
      let ty_scheme = Term.Variable.Map.find x state.variables in
      let subst, cnstrs =
        fresh_instantiation ty_scheme.TyScheme.params ty_scheme.constraints
      in
      let x = Term.poly_var x subst ty_scheme.ty in
      ((x.term, x.ty), cnstrs)
  | Untyped.Const c -> ((Term.Const c, Type.type_const c), Constraint.empty)
  | Untyped.Annotated (e, ty) ->
      let e', cnstrs = infer_expression state e in
      let e'', castCt = Constraint.cast_expression e' ty in
      ((e''.term, e''.ty), Constraint.union castCt cnstrs)
  | Untyped.Tuple es ->
      let es, cs = infer_many (infer_expression state) es in
      let tys = List.map (fun e -> e.ty) es in
      ((Term.Tuple es, Type.tuple tys), cs)
  | Untyped.Record flds ->
      let hd_fld, _ = List.hd (Type.Field.Map.bindings flds) in
      let out_ty, (ty_name, fld_tys) =
        TypeDefinitionContext.infer_field hd_fld state.type_definitions
      in
      let fold fld e (flds', cnstrs) =
        let e', cnstrs' = infer_expression state e in
        match Type.Field.Map.find_opt fld fld_tys with
        | None ->
            Error.typing ~loc:e.at "Field %t does not belong to type %t"
              (Type.Field.print fld)
              (Language.TyName.print ty_name)
        | Some fld_ty ->
            let e'', cons = Constraint.cast_expression e' fld_ty in
            ( (fld, e'') :: flds',
              Constraint.list_union [ cons; cnstrs'; cnstrs ] )
      in
      let flds', cnstrs' =
        Type.Field.Map.fold fold flds ([], Constraint.empty)
      in
      ((Term.Record (Type.Field.Map.of_bindings flds'), out_ty), cnstrs')
  | Untyped.Variant (lbl, mbe) -> (
      match
        (TypeDefinitionContext.infer_variant lbl state.type_definitions, mbe)
      with
      | (None, ty_out), None ->
          ((Term.Variant (lbl, None), ty_out), Constraint.empty)
      | (Some ty_in, ty_out), Some e ->
          let e', cs1 = infer_expression state e in
          let castExp, castCt = Constraint.cast_expression e' ty_in in
          ( (Term.Variant (lbl, Some castExp), ty_out),
            Constraint.union castCt cs1 )
      | _, _ -> assert false)
  | Untyped.Lambda abs ->
      let abs', cnstrs = infer_abstraction state abs in
      ((Term.Lambda abs', Type.arrow abs'.ty), cnstrs)
  | Untyped.Effect eff ->
      let in_ty, out_ty = Effect.Map.find eff state.effects
      and s = Effect.Set.singleton eff in
      let out_drty = (out_ty, Dirt.closed s) in
      let x_pat, x_var = Term.fresh_variable "x" in_ty
      and y_pat, y_var = Term.fresh_variable "y" out_ty in
      let ret, cnstrs =
        Constraint.cast_computation (Term.value y_var) out_drty
      in
      let outVal =
        Term.Lambda
          (Term.abstraction
             ( x_pat,
               Term.call
                 ((eff, (in_ty, out_ty)), x_var, Term.abstraction (y_pat, ret))
             ))
      in
      let outType = Type.arrow (in_ty, out_drty) in
      ((outVal, outType), cnstrs)
  | Untyped.Handler hand -> infer_handler state hand

(* Handlers(Op Case) *)
and infer_effect_clause state (dirtyOut : Type.dirty)
    ((eff, abs2) : Untyped.effect * Untyped.abstraction2)
      (* Op clause *)
      (* Expected output type *) =
  (* 1: Lookup the type of Opi *)
  let tyAi, tyBi = Effect.Map.find eff state.effects in

  (* 2: Generate fresh variables for the type of the codomain of the continuation *)
  let dirtyi = Type.fresh_dirty_with_fresh_skel () in

  let ty_cont = Type.arrow (tyBi, dirtyi) in

  (* 3: Typecheck the clause *)
  let { term = trgPat1, trgPat2, trgCmp; _ }, cs =
    infer_abstraction2 state abs2
  in
  let trgPat1' = { trgPat1 with ty = tyAi }
  and trgPat2' = { trgPat2 with ty = ty_cont } in
  let abs2 = Term.abstraction2 (trgPat1', trgPat2', trgCmp)
  and csi =
    cs
    |> Constraint.add_ty_equality (trgPat1.ty, tyAi)
    |> Constraint.add_ty_equality (trgPat2.ty, ty_cont)
  in

  let (xop, kop, trgCop), (_, _, (tyBOpi, dirtDOpi)) = (abs2.term, abs2.ty) in

  (* 4: Make sure that the pattern for k is a variable one.
   *    We do not support anything else at the moment *)
  let k =
    match kop.term with
    | Term.PVar k -> k
    | Term.PNonbinding -> Term.Variable.fresh "k"
    | _ -> failwith __LOC__
  in

  (* 5: Generate all the needed constraints *)
  let omega34i, omegaCt34i =
    Constraint.fresh_dirty_coer ((tyBOpi, dirtDOpi), dirtyOut)
  in
  let leftty = Type.arrow (tyBi, dirtyOut) in
  let rightty = Type.arrow (tyBi, dirtyi) in

  (* 6: Create the elaborated clause *)
  let l_pat, l_var = Term.fresh_variable "l" leftty in
  let castExp, omegaCt5i = Constraint.cast_expression l_var rightty in
  let lsub = Term.subst_comp (Assoc.of_list [ (k, castExp) ]) in
  let outExpr =
    ( ((eff, (tyAi, tyBi)) : Term.effect) (* Opi *),
      Term.abstraction2 (xop, l_pat, Term.castComp (lsub trgCop, omega34i)) )
  in

  (* 7: Combine the results *)
  let outCs = Constraint.list_union [ omegaCt34i; omegaCt5i; csi ] in
  (outExpr, outCs)

(* Handlers *)
and infer_handler state { Untyped.value_clause; effect_clauses; finally_clause }
    =
  (* 1: Generate fresh variables for the input and output types *)
  let dirt_row_param = Dirt.Param.fresh ()
  and ty_mid = Type.fresh_ty_with_fresh_skel ()
  and ty_out = Type.fresh_ty_with_fresh_skel () in

  let drt_out = Dirt.fresh () in

  (* 2: Process the return and the operation clauses *)
  let value_clause', value_clause_cnstrs = infer_abstraction state value_clause
  and effect_clauses', effect_clauses_cnstrs =
    infer_many
      (infer_effect_clause state (ty_mid, drt_out))
      (Assoc.to_list effect_clauses)
  and finally_clause', finally_clause_cnstrs =
    infer_abstraction state finally_clause
  in

  let drt_in =
    Dirt.
      {
        effect_set = Term.handled_effects (Assoc.of_list effect_clauses');
        row = Dirt.Row.Param dirt_row_param;
      }
  in

  let value_clause'', value_clause_cast_cnstrs =
    Constraint.cast_abstraction value_clause' (ty_mid, drt_out)
  and finally_clause'', finally_clause_cast_cnstrs =
    Constraint.full_cast_abstraction finally_clause' ty_mid (ty_out, drt_out)
  in

  let handler =
    Term.handlerWithFinally
      (Term.handler_clauses value_clause''
         (Assoc.of_list effect_clauses')
         drt_in)
      finally_clause''
  in
  ( (handler.term, handler.ty),
    Constraint.list_union
      [
        value_clause_cnstrs;
        effect_clauses_cnstrs;
        finally_clause_cnstrs;
        value_clause_cast_cnstrs;
        finally_clause_cast_cnstrs;
      ] )

(* ************************************************************************* *)
(*                          COMPUTATION TYPING                               *)
(* ************************************************************************* *)
and infer_computation state cmp =
  let (trm, ty), cnstrs = infer_computation' ~loc:cmp.at state cmp.it in
  (* Print.debug "%t -> %t : %t / %t"
     (Untyped.print_computation c)
     (Term.print_computation' trm)
     (Type.print_dirty ty) (Constraint.print cnstrs); *)
  ({ term = trm; ty }, cnstrs)

(* Dispatch: Type inference for a plan computation *)
and infer_computation' ~loc state = function
  | Untyped.Value exp ->
      let outExpr, outCs = infer_expression state exp in
      ((Term.Value outExpr, (outExpr.ty, Dirt.empty)), outCs)
  (* Nest a list of let-bindings *)
  | Let ([], c2) ->
      let c, cnstrs = infer_computation state c2 in
      ((c.term, c.ty), cnstrs)
  | Let ([ (pdef, c1) ], c2) -> (
      match c1.it with
      | Untyped.Value e1 ->
          let trgE1, cs1 = infer_expression state e1 in

          (* 2: Typecheck abstraction *)
          let abs, cs2 = infer_abstraction state (pdef, c2) in
          let ty_in, drty_out = abs.ty in
          (* 3: Combine the results *)
          let exp', cnstr = Constraint.cast_expression trgE1 ty_in in
          let outExpr = Term.LetVal (exp', abs) in
          let outCs = Constraint.list_union [ cnstr; cs1; cs2 ] in
          ((outExpr, drty_out), outCs)
      | _other_computation ->
          (* 1: Typecheck c1, the pattern, and c2 *)
          let trgC1, cs1 = infer_computation state c1 in
          let tyA1, dirtD1 = trgC1.ty in
          let trgPat, vars, csPat = infer_pattern state pdef in
          let midState = extend_state vars state in
          let csPat' = Constraint.add_ty_equality (trgPat.ty, tyA1) csPat in
          let trgC2, cs2 = infer_computation midState c2 in
          let tyA2, dirtD2 = trgC2.ty in

          (* 2: Generate a fresh dirt variable for the result *)
          let delta = Dirt.fresh () in

          (* 3: Generate the coercions for the dirts *)
          let omega1, omegaCt1 = Constraint.fresh_dirt_coer (dirtD1, delta) in
          (* s2(D1) <= delta *)
          let omega2, omegaCt2 = Constraint.fresh_dirt_coer (dirtD2, delta) in

          (*    D2  <= delta *)
          let cresC1 =
            Term.castComp
              (trgC1, Coercion.bangCoercion (Coercion.reflTy tyA1, omega1))
          in
          let cresC2 =
            Term.castComp
              (trgC2, Coercion.bangCoercion (Coercion.reflTy tyA2, omega2))
          in

          let outExpr = Term.Bind (cresC1, Term.abstraction (trgPat, cresC2)) in
          let outCs =
            Constraint.list_union [ omegaCt1; omegaCt2; cs1; cs2; csPat' ]
          in
          let outType = (tyA2, delta) in

          ((outExpr, outType), outCs))
  | Let ((pat, c1) :: rest, c2) ->
      let subCmp = { it = Untyped.Let (rest, c2); at = c2.at } in
      infer_computation' ~loc state (Untyped.Let ([ (pat, c1) ], subCmp))
  | LetRec (defs, c2) ->
      let defs', cs1 = infer_rec_definitions state defs in
      let state' =
        List.fold_left
          (fun state (x, abs) -> extend_var state x (Type.arrow abs.ty))
          state (Assoc.to_list defs')
      in
      (* 3: Typecheck c2 *)
      let trgC2, cs2 = infer_computation state' c2 in

      (* 5: Combine the results *)
      let outExpr = Term.LetRec (defs', trgC2) in

      let outCs = Constraint.union cs1 cs2 in
      ((outExpr, trgC2.ty), outCs)
  | Match (scr, alts) ->
      (* 1: Generate fresh variables for the result *)
      let dirtyOut = Type.fresh_dirty_with_fresh_skel () in

      let patTy = Type.fresh_ty_with_fresh_skel () in
      let infer_case case =
        let case', cnstrs' = infer_abstraction state case in
        let ty_in, _ = case'.ty
        and case'', cnstrs'' = Constraint.cast_abstraction case' dirtyOut in
        ( case'',
          Constraint.add_ty_equality (patTy, ty_in)
            (Constraint.list_union [ cnstrs''; cnstrs' ]) )
      in
      (* 2: Infer a type for the patterns *)
      let cases, cs2 = infer_many infer_case alts in

      (* 4: Typecheck the scrutinee and the alternatives *)
      let trgScr, cs1 = infer_expression state scr in

      (* 5: Generate the coercion for casting the scrutinee *)
      (* NOTE: The others should be already included in 'altRes' *)
      let matchExp, omegaCtScr = Constraint.cast_expression trgScr patTy in

      (* 6: Combine the results *)
      let outExpr = Term.Match (matchExp, cases) in
      let outCs = Constraint.list_union [ omegaCtScr; cs1; cs2 ] in
      ((outExpr, dirtyOut), outCs)
  | Apply (val1, val2) ->
      (* Infer the types of val1 and val2 *)
      let trgVal1, cs1 = infer_expression state val1 in
      let trgVal2, cs2 = infer_expression state val2 in

      (* Generate fresh variables for the result *)
      let outType = Type.fresh_dirty_with_fresh_skel () in

      (* Create the constraint and the cast elaborated expression *)
      let castVal1, omegaCt =
        Constraint.cast_expression trgVal1 (Type.arrow (trgVal2.ty, outType))
      in
      let outExpr = Term.Apply (castVal1, trgVal2) in
      let outCs = Constraint.list_union [ omegaCt; cs1; cs2 ] in
      ((outExpr, outType), outCs)
  | Handle (hand, cmp) ->
      (* Typecheck the handler and the computation *)
      let trgHand, cs1 = infer_expression state hand in
      (* Typecheck the handler *)
      let trgCmp, cs2 = infer_computation state cmp in

      (* Typecheck the computation *)

      (* Generate fresh variables *)
      let dirty1 = Type.fresh_dirty_with_fresh_skel () in
      let dirty2 = Type.fresh_dirty_with_fresh_skel () in

      (* Create all constraints *)
      let castHand, omegaCt1 =
        Constraint.cast_expression trgHand (Type.handler (dirty1, dirty2))
      in
      let castCmp, omegaCt23 = Constraint.cast_computation trgCmp dirty1 in

      (* Combine all the outputs *)
      let outExpr = Term.Handle (castHand, castCmp) in
      let outCs = Constraint.list_union [ omegaCt1; omegaCt23; cs1; cs2 ] in
      ((outExpr, dirty2), outCs)
  | Check cmp ->
      let cmp', cnstrs = infer_computation state cmp in
      ((Term.Check (loc, cmp'), Type.pure_ty Type.unit_ty), cnstrs)

(* Typecheck a (potentially) recursive let *)
and infer_rec_definitions state defs =
  (* 1: Generate fresh variables for everything *)
  let defs' =
    List.map
      (fun (x, abs) ->
        let alpha = Type.fresh_ty_with_fresh_skel () in
        let betadelta = Type.fresh_dirty_with_fresh_skel () in
        (x, abs, alpha, betadelta, Constraint.empty))
      defs
  in
  let state' =
    List.fold_left
      (fun state (x, _, alpha, betadelta, _) ->
        extend_var state x (Type.arrow (alpha, betadelta)))
      state defs'
  in
  let defs'', cnstrs =
    List.fold_right
      (fun (x, abs, alpha, betadelta, cs3) (defs, cnstrs) ->
        let p, c = abs in
        Exhaust.is_irrefutable state.type_definitions p;
        Exhaust.check_computation state.type_definitions c;
        let abs', cs1 = infer_abstraction state' abs in
        let abs'', cs2 =
          Constraint.full_cast_abstraction abs' alpha betadelta
        in
        ((x, abs'') :: defs, Constraint.list_union [ cs1; cs2; cs3; cnstrs ]))
      defs' ([], Constraint.empty)
  in
  (Assoc.of_list defs'', cnstrs)

and infer_abstraction state (pat, cmp) : Term.abstraction * Constraint.t =
  let trgPat, vars, cs1 = infer_pattern state pat in
  let state' = extend_state vars state in
  let trgCmp, cs2 = infer_computation state' cmp in
  (Term.abstraction (trgPat, trgCmp), Constraint.union cs1 cs2)

and infer_abstraction2 state (pat1, pat2, cmp) :
    Term.abstraction2 * Constraint.t =
  let trgPat1, vars1, cs1 = infer_pattern state pat1 in
  let trgPat2, vars2, cs2 = infer_pattern state pat2 in
  let state' =
    extend_state (Term.Variable.Map.compatible_union vars1 vars2) state
  in
  let trgCmp, cs = infer_computation state' cmp in
  ( Term.abstraction2 (trgPat1, trgPat2, trgCmp),
    Constraint.list_union [ cs1; cs2; cs ] )

(* ************************************************************************* *)
(* ************************************************************************* *)

let process_def_effect eff (ty1, ty2) state =
  ( { state with effects = Effect.Map.add eff (ty1, ty2) state.effects },
    (ty1, ty2) )

let process_computation state comp =
  let comp', cnstrs = infer_computation state comp in
  let sub, residuals = Unification.solve ~loc:comp.at cnstrs in
  let cmp' = Term.apply_sub_comp sub comp' in
  let params =
    match comp.it with
    | Language.UntypedSyntax.Value _ ->
        Type.Params.union
          (Type.free_params_dirty cmp'.ty)
          (Constraints.free_params residuals)
    | _ -> Type.Params.empty
  in
  Exhaust.check_computation state.type_definitions comp;
  (params, cmp', residuals)

let process_top_let ~loc state defs =
  let fold (pat, cmp) (state', defs) =
    let pat', vars, cnstrs_pat = infer_pattern state pat in
    let cmp', cnstrs_cmp = infer_computation state cmp in
    let sub, constraints =
      Unification.solve ~loc
        (Constraint.add_ty_equality
           (pat'.ty, fst cmp'.ty)
           (Constraint.union cnstrs_pat cnstrs_cmp))
    in
    let pat'', cmp'' =
      (Term.apply_sub_pat sub pat', Term.apply_sub_comp sub cmp')
    in
    let vars' = Term.Variable.Map.map (Substitution.apply_sub_ty sub) vars in
    let params =
      match cmp.it with
      | Language.UntypedSyntax.Value _ ->
          Type.Params.union
            (Type.free_params_dirty cmp''.ty)
            (Constraints.free_params constraints)
      | _ -> Type.Params.empty
    in
    let state'' =
      Term.Variable.Map.fold
        (fun x ty state -> extend_poly_var state x { params; constraints; ty })
        vars' state'
    in
    Exhaust.is_irrefutable state.type_definitions pat;
    Exhaust.check_computation state.type_definitions cmp;
    (state'', (pat'', params, constraints, cmp'') :: defs)
  in
  List.fold_right fold defs (state, [])

let process_top_let_rec ~loc state un_defs =
  let defs', cnstrs = infer_rec_definitions state (Assoc.to_list un_defs) in
  let sub, constraints = Unification.solve ~loc cnstrs in
  let defs = Assoc.map (Term.apply_substitutions_to_abstraction sub) defs' in
  let defs_params = Term.free_params_definitions defs in
  let cnstrs_params = Constraints.free_params constraints in
  let params = Type.Params.union defs_params cnstrs_params in
  let state', defs' =
    Assoc.fold_right
      (fun (f, (abs : Term.abstraction)) (state, defs) ->
        let (ty_scheme : TyScheme.t) =
          TyScheme.{ params; constraints; ty = Type.arrow abs.ty }
        in
        let state' = extend_poly_var state f ty_scheme in
        (state', (f, (params, constraints, abs)) :: defs))
      defs (state, [])
  in
  let subst =
    List.map
      (fun (f, (params, constraints, abs)) ->
        let inst = identity_instantiation params constraints in
        (f, Term.poly_var f inst (Type.arrow abs.ty)))
      defs'
    |> Assoc.of_list
  in
  let defs'' =
    List.map
      (fun (f, (params, constraints, abs)) ->
        (f, (params, constraints, Term.subst_abs subst abs)))
      defs'
  in
  (state', Assoc.of_list defs'')

let add_type_definitions state type_definitions =
  {
    state with
    type_definitions =
      TypeDefinitionContext.extend_type_definitions type_definitions
        state.type_definitions;
  }

let load_primitive_effect state eff prim =
  let ty1, ty2 = TypeCheckerPrimitives.primitive_effect_signature prim in
  ( { state with effects = Effect.Map.add eff (ty1, ty2) state.effects },
    (ty1, ty2) )

let load_primitive_value state x prim =
  let ty = TypeCheckerPrimitives.primitive_value_type_scheme prim in
  extend_poly_var state x ty
