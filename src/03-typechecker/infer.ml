open Utils
module Substitution = Language.Substitution
module Const = Language.Const
module Untyped = Language.UntypedSyntax
module Coercion = Language.Coercion
module Term = Language.Term
module Type = Language.Type
module TypeDefinitionContext = TypeDefinitionContext

let identity_instantiation (params : Type.Params.t)
    (constraints : Type.Constraints.t) =
  Substitution.
    {
      type_param_to_type_coercions =
        Type.TyConstraints.fold_expanded
          (fun _s _t1 _t2 w ty1 ty2 ->
            Type.TyCoercionParam.Map.add w (Coercion.tyCoercionVar w (ty1, ty2)))
          constraints.ty_constraints Type.TyCoercionParam.Map.empty;
      type_param_to_type_subs =
        params.ty_params |> Type.TyParam.Map.bindings
        |> List.map (fun (p, skel) -> (p, Type.tyParam p skel))
        |> Type.TyParam.Map.of_bindings;
      dirt_var_to_dirt_coercions =
        Type.DirtConstraints.fold_expanded
          (fun _d1 _d2 w _effs drt1 drt2 ->
            Type.DirtCoercionParam.Map.add w
              (Coercion.dirtCoercionVar w (drt1, drt2)))
          constraints.dirt_constraints Type.DirtCoercionParam.Map.empty;
      dirt_var_to_dirt_subs =
        params.dirt_params |> Type.DirtParam.Set.elements
        |> List.map (fun d -> (d, Type.no_effect_dirt d))
        |> Type.DirtParam.Map.of_bindings;
      skel_param_to_skel_subs =
        params.skel_params |> Type.SkelParam.Set.elements
        |> List.map (fun s -> (s, Type.SkelParam s))
        |> Type.SkelParam.Map.of_bindings;
    }

module TypingEnv = struct
  type t = (Term.Variable.t, Type.ty_scheme) Assoc.t

  let empty = Assoc.empty

  let fresh_instantiation (params : Type.Params.t)
      (constraints : Type.Constraints.t) =
    let _, subst = Substitution.of_parameters params in
    let type_param_to_type_coercions =
      Type.TyConstraints.fold_expanded
        (fun _s _t1 _t2 w ty1 ty2 ->
          Type.TyCoercionParam.Map.add w
            (Coercion.tyCoercionVar
               (Type.TyCoercionParam.refresh w)
               ( Substitution.apply_substitutions_to_type subst ty1,
                 Substitution.apply_substitutions_to_type subst ty2 )))
        constraints.ty_constraints Type.TyCoercionParam.Map.empty
    and dirt_var_to_dirt_coercions =
      Type.DirtConstraints.fold_expanded
        (fun _d1 _d2 w _effs drt1 drt2 ->
          Type.DirtCoercionParam.Map.add w
            (Coercion.dirtCoercionVar
               (Type.DirtCoercionParam.refresh w)
               (Substitution.apply_sub_ct_dirt subst (drt1, drt2))))
        constraints.dirt_constraints Type.DirtCoercionParam.Map.empty
    in
    Substitution.
      { subst with type_param_to_type_coercions; dirt_var_to_dirt_coercions }

  let lookup ctx x : Term.expression * Constraint.t =
    match Assoc.lookup x ctx with
    | Some ty_scheme ->
        let subst =
          fresh_instantiation ty_scheme.Type.params ty_scheme.constraints
        in
        let x = Term.poly_var x subst ty_scheme.ty in
        let cnstrs =
          Constraint.return_to_unresolved ty_scheme.constraints Constraint.empty
        in
        let cnstrs = Constraint.apply_sub subst cnstrs in
        (x, cnstrs)
    | None -> assert false

  let update ctx x sch = Assoc.update x sch ctx
end

(* GEORGE: TODO:
     1. Add debugging output to the new code snippets
     2. Figure out what is wrong with pattern typing (untyped & typed version)
     3. Understand how variants are implemented
 *)

(* GEORGE: By convention, in types, type inequalities are qualified over first,
and then dirt inequalities *)

type label = Type.Label.t

type field = Type.Field.t

(* GEORGE: I hope to God for the order to be correct here *)

(* [STATE] INFERENCE STATE *)

type state = {
  variables : TypingEnv.t;
  (* Global Typing Environment *)
  effects : (Type.ty * Type.ty) Type.Effect.Map.t;
  (* Valid Effects             *)
  tydefs : TypeDefinitionContext.state; (* Type definition context *)
}

(* Add a single term binding to the global typing environment *)
let extend_var env x ty =
  { env with variables = TypingEnv.update env.variables x (Type.monotype ty) }

let extend_poly_var env x ty_scheme =
  { env with variables = TypingEnv.update env.variables x ty_scheme }

(* Initial type inference state: everything is empty *)
let initial_state : state =
  {
    variables = TypingEnv.empty;
    effects = Type.Effect.Map.empty;
    tydefs = TypeDefinitionContext.initial_state;
  }

(* ************************************************************************* *)

let process_def_effect eff (ty1, ty2) state =
  ( { state with effects = Type.Effect.Map.add eff (ty1, ty2) state.effects },
    (ty1, ty2) )

(* ... *)

(* ************************************************************************* *)
(*                            SUBSTITUTIONS                                  *)
(* ************************************************************************* *)

(* Substitute in target values and computations *)
let subInCmp sub cmp = Term.apply_substitutions_to_computation sub cmp

let subInExp sub exp = Term.apply_substitutions_to_expression sub exp

let subInAbs sub abs = Term.apply_substitutions_to_abstraction sub abs

(* Substitute in target value types, computation types, and dirts *)
let subInValTy sub ty = Substitution.apply_substitutions_to_type sub ty

let subInDirt sub dirt = Substitution.apply_substitutions_to_dirt sub dirt

let subInCmpTy sub (ty, dirt) = (subInValTy sub ty, subInDirt sub dirt)

let subInAbsTy sub (ty_in, drty_out) =
  (subInValTy sub ty_in, subInCmpTy sub drty_out)

(* Substitute in value, dirt, and computation coercions *)
let subInValCo sub co = Substitution.apply_sub_tycoer sub co

let subInDirtCo sub co = Substitution.apply_sub_dirtcoer sub co

let subInCmpCo sub co = Substitution.apply_sub_dirtycoer sub co

(* Substitute in skeletons *)
let subInSkel sub skel = Substitution.apply_substitutions_to_skeleton sub skel

(* Substitute in type and dirt inequalities *)
let subInTyCt sub (ty1, ty2) = (subInValTy sub ty1, subInValTy sub ty2)

let subInDirtCt sub (d1, d2) = (subInDirt sub d1, subInDirt sub d2)

(* ************************************************************************* *)

(* ************************************************************************* *)

(* Apply a term to all possible arguments *)
let applyTerm tyCoercions dirtCoercions exp : Term.expression =
  let foldLeft f xs x0 = List.fold_left f x0 xs in
  (* GEORGE: Just for convenience *)
  exp
  |> (* 1: Apply to the type coercions *)
  foldLeft (fun e c -> Term.applyTyCoercion (e, c)) tyCoercions
  |> (* 2: Apply to the dirt coercions *)
  foldLeft (fun e c -> Term.applyDirtCoercion (e, c)) dirtCoercions

(* ************************************************************************* *)
(*                           BASIC DEFINITIONS                               *)
(* ************************************************************************* *)

(* Constraint generation output *)
type 'a tcOutput = 'a * Constraint.t

(* Value typing output *)
type tcExprOutput' = (Term.expression' * Type.ty) tcOutput

type tcExprOutput = Term.expression tcOutput

(* Computation typing output *)
type tcCompOutput' = (Term.computation' * Type.dirty) tcOutput

type tcCompOutput = Term.computation tcOutput

(* Typecheck a list of things *)
let rec tcMany state (xss : 'a list) tc =
  match xss with
  | [] -> (([], []), Constraint.empty)
  | x :: xs ->
      let y, cs1 = tc state x in
      let (ys, tys), cs2 = tcMany state xs tc in
      ((y :: ys, y.ty :: tys), Constraint.union cs1 cs2)

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)

let rec infer_pattern state (pat : Untyped.pattern) :
    Term.pattern * state * Constraint.t =
  let pat', ty, state', cnstrs = infer_pattern' state pat in
  ({ term = pat'; ty }, state', cnstrs)

and infer_pattern' state pat =
  match pat.it with
  | Untyped.PVar x ->
      let alpha = Type.fresh_ty_with_fresh_skel () in
      (Term.PVar x, alpha, extend_var state x alpha, Constraint.empty)
  | Untyped.PAnnotated (p, ty) ->
      let p', state', cnstrs = infer_pattern state p in
      (p'.term, ty, state', Constraint.add_ty_equality (ty, p'.ty) cnstrs)
  | Untyped.PNonbinding ->
      let alpha = Type.fresh_ty_with_fresh_skel () in
      (Term.PNonbinding, alpha, state, Constraint.empty)
  | Untyped.PConst c ->
      (Term.PConst c, Type.type_const c, state, Constraint.empty)
  | Untyped.PTuple ps ->
      let fold p (ps', state, cnstrs) =
        let p', state', cnstrs' = infer_pattern state p in
        (p' :: ps', state', Constraint.union cnstrs' cnstrs)
      in
      let ps', state', cnstrs =
        List.fold_right fold ps ([], state, Constraint.empty)
      in
      let p = Term.pTuple ps' in
      (p.term, p.ty, state', cnstrs)
  | Untyped.PVariant (lbl, p) -> (
      match (p, TypeDefinitionContext.infer_variant lbl state.tydefs) with
      | None, (None, out_ty) ->
          (Term.PVariant (lbl, None), out_ty, state, Constraint.empty)
      | Some p, (Some in_ty, out_ty) ->
          let p', state', cnstrs = infer_pattern state p in
          ( Term.PVariant (lbl, Some p'),
            out_ty,
            state',
            Constraint.add_ty_equality (in_ty, p'.ty) cnstrs )
      | _ -> assert false)
  | Untyped.PAs (p, x) ->
      let p', state', cnstrs = infer_pattern state p in
      (Term.PAs (p', x), p'.ty, extend_var state' x p'.ty, cnstrs)
  | Untyped.PRecord flds ->
      let hd_fld, _ = List.hd (Type.Field.Map.bindings flds) in
      let out_ty, (ty_name, fld_tys) =
        TypeDefinitionContext.infer_field hd_fld state.tydefs
      in
      let fold fld p (flds', state, cnstrs) =
        let p', state', cnstrs' = infer_pattern state p in
        match Type.Field.Map.find_opt fld fld_tys with
        | None ->
            Error.typing ~loc:pat.at "Field %t does not belong to type %t"
              (Type.Field.print fld)
              (Type.TyName.print ty_name)
        | Some fld_ty ->
            ( (fld, p') :: flds',
              state',
              Constraint.union
                (Constraint.add_ty_equality (fld_ty, p'.ty) cnstrs')
                cnstrs )
      in
      let flds', state', cnstrs' =
        Type.TyName.Map.fold fold flds ([], state, Constraint.empty)
      in
      (Term.PRecord (Type.Field.Map.of_bindings flds'), out_ty, state', cnstrs')

let isLocatedVarPat (pat : Untyped.pattern) : bool =
  match pat.it with Untyped.PVar _ -> true | _other_pattern -> false

(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(*                             VALUE TYPING                                  *)
(* ************************************************************************* *)

(* Term Variables *)
let rec tcVar state (x : Untyped.variable) : tcExprOutput' =
  let var, cnstrs = TypingEnv.lookup state.variables x in
  ((var.term, var.ty), cnstrs)

(* Constants *)
and tcConst (_state : state) (c : Const.t) : tcExprOutput' =
  ((Term.Const c, Type.type_const c), Constraint.empty)

(* Type-annotated Expressions *)
and tcAnnotated (state : state)
    ((e, ty) : Untyped.expression * Language.Type.ty) : tcExprOutput' =
  let e', cnstrs = tcExpr state e in
  let e'', castCt = Constraint.cast_expression e' ty in

  ((e''.term, e''.ty), Constraint.union castCt cnstrs)

(* GEORGE: Planned TODO for the future I guess?? *)

(* Tuples *)
and tcTuple state (es : Untyped.expression list) : tcExprOutput' =
  let (es, tys), cs = tcMany state es tcExpr in
  ((Term.Tuple es, Type.tuple tys), cs)

(* Records *)
and tcRecord (state : state) (flds : Untyped.expression Type.Field.Map.t) :
    tcExprOutput' =
  let hd_fld, _ = List.hd (Type.Field.Map.bindings flds) in
  let out_ty, (ty_name, fld_tys) =
    TypeDefinitionContext.infer_field hd_fld state.tydefs
  in
  let fold fld e (flds', cnstrs) =
    let e', cnstrs' = tcExpr state e in
    match Type.Field.Map.find_opt fld fld_tys with
    | None ->
        Error.typing ~loc:e.at "Field %t does not belong to type %t"
          (Type.Field.print fld)
          (Type.TyName.print ty_name)
    | Some fld_ty ->
        let e'', cons = Constraint.cast_expression e' fld_ty in
        ((fld, e'') :: flds', Constraint.list_union [ cons; cnstrs'; cnstrs ])
  in
  let flds', cnstrs' = Type.Field.Map.fold fold flds ([], Constraint.empty) in
  ((Term.Record (Type.Field.Map.of_bindings flds'), out_ty), cnstrs')

(* GEORGE: Planned TODO for the future I guess?? *)

(* Variants *)
and tcVariant state ((lbl, mbe) : label * Untyped.expression option) :
    tcExprOutput' =
  match (TypeDefinitionContext.infer_variant lbl state.tydefs, mbe) with
  | (None, ty_out), None ->
      ((Term.Variant (lbl, None), ty_out), Constraint.empty)
  | (Some ty_in, ty_out), Some e ->
      let e', cs1 = tcExpr state e in
      (* GEORGE: Investigate how cast_expression works *)
      let castExp, castCt = Constraint.cast_expression e' ty_in in
      ((Term.Variant (lbl, Some castExp), ty_out), Constraint.union castCt cs1)
  | _, _ -> failwith __LOC__

and tcAbstraction state (pat, cmp) =
  let pat', state', cnstrs1 = infer_pattern state pat in
  let cmp', cnstrs2 = tcComp state' cmp in
  (Term.abstraction (pat', cmp'), Constraint.union cnstrs1 cnstrs2)

(* Lambda Abstractions *)
and tcLambda state abs =
  let abs', cnstrs = tcAbstraction state abs in
  ((Term.Lambda abs', Type.arrow abs'.ty), cnstrs)

and tcEffect state (eff : Untyped.effect) : tcExprOutput' =
  (* GEORGE: NOTE: This is verbatim copied from the previous implementation *)
  let in_ty, out_ty = Type.Effect.Map.find eff state.effects
  and s = Type.Effect.Set.singleton eff in
  let out_drty = (out_ty, Type.closed_dirt s) in
  let x_pat, x_var = Term.fresh_variable "x" in_ty
  and y_pat, y_var = Term.fresh_variable "y" out_ty in
  let ret, cnstrs = Constraint.cast_computation (Term.value y_var) out_drty in
  let outVal =
    Term.Lambda
      (Term.abstraction
         ( x_pat,
           Term.call
             ((eff, (in_ty, out_ty)), x_var, Term.abstraction (y_pat, ret)) ))
  in
  let outType = Type.arrow (in_ty, out_drty) in
  ((outVal, outType), cnstrs)

(* Handlers(Op Cases) *)
and tcOpCases state (eclauses : (Untyped.effect, Untyped.abstraction2) Assoc.t)
    (dirtyOut : Type.dirty) : (Term.effect, Term.abstraction2) Assoc.t tcOutput
    =
  let rec go cs =
    match Assoc.to_list cs with
    | [] -> ([], Constraint.empty)
    | c :: cs ->
        let y, cs1 = tcOpCase state c dirtyOut in
        let ys, cs2 = go (Assoc.of_list cs) in
        (y :: ys, Constraint.union cs1 cs2)
  in
  let allClauses, allCs = go eclauses in
  (Assoc.of_list allClauses, allCs)

(* Handlers(Op Case) *)
and tcOpCase state
    ((eff, abs2) : Untyped.effect * Untyped.abstraction2) (* Op clause *)
    (dirtyOut : Type.dirty) (* Expected output type *) =
  (* 1: Lookup the type of Opi *)
  let tyAi, tyBi = Type.Effect.Map.find eff state.effects in

  (* 2: Generate fresh variables for the type of the codomain of the continuation *)
  let dirtyi = Type.fresh_dirty_with_fresh_skel () in

  (* 3: Typecheck the clause *)
  let abs2, csi (* GEORGE: I don't like the unused types *) =
    check_abstraction2 state abs2 tyAi (Type.arrow (tyBi, dirtyi))
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
and tcHandler state (h : Untyped.handler) : tcExprOutput' =
  (* 1: Generate fresh variables for the input and output types *)
  let deltaIn = Type.fresh_dirt () in
  let ((_, deltaOut) as dirtyOut) = Type.fresh_dirty_with_fresh_skel () in

  (* 2: Process the return and the operation clauses *)
  let trgRet, cs1 = tcAbstraction state h.value_clause in
  let trgCls, cs2 = tcOpCases state h.effect_clauses dirtyOut in

  (* 3: Create the omega7 coercion (cast the whole handler) *)
  let ty_ret_in, _ = trgRet.ty in
  let omega7, omegaCt7 =
    let allOps =
      trgCls |> Assoc.to_list
      |> List.map (fun ((eff, _), _) -> eff)
      |> Type.Effect.Set.of_list
    in

    (* GEORGE: This should be done in a cleaner way but let's leave it for later *)
    let deltaOutVar =
      match deltaOut.row with
      | ParamRow deltaOutVar -> deltaOutVar
      | EmptyRow -> assert false
    in

    Constraint.fresh_dirt_coer
      (deltaIn, Type.{ effect_set = allOps; row = ParamRow deltaOutVar })
  in

  let handlerCo =
    Coercion.handlerCoercion
      ( Coercion.bangCoercion (Coercion.reflTy ty_ret_in, omega7),
        Coercion.reflDirty dirtyOut )
  in
  let handTy, _ = handlerCo.ty in
  match handTy.term with
  | Type.Handler ((_, drt_in), _) ->
      let trgRet', cnstr_ret = Constraint.cast_abstraction trgRet dirtyOut in
      let handler = Term.Handler (Term.handler_clauses trgRet' trgCls drt_in) in
      let outExpr = Term.CastExp ({ term = handler; ty = handTy }, handlerCo) in
      let outType = Type.handler ((ty_ret_in, deltaIn), dirtyOut) in
      let outCs = Constraint.list_union [ omegaCt7; cnstr_ret; cs1; cs2 ] in
      (* 7, ain : skelin, aout : skelout && 1, 2, 6 && 3i, 4i, 5i *)
      ((outExpr, outType), outCs)
  | _ -> assert false

(* Dispatch: Type inference for a plain value (expression) *)
and tcExpr' state : Untyped.plain_expression -> tcExprOutput' = function
  | Untyped.Var x -> tcVar state x
  | Untyped.Const c -> tcConst state c
  | Untyped.Annotated (e, ty) -> tcAnnotated state (e, ty)
  | Untyped.Tuple es -> tcTuple state es
  | Untyped.Record lst -> tcRecord state lst
  | Untyped.Variant (lbl, mbe) -> tcVariant state (lbl, mbe)
  | Untyped.Lambda abs -> tcLambda state abs
  | Untyped.Effect eff -> tcEffect state eff
  | Untyped.Handler hand -> tcHandler state hand

(* Type inference for a located value (expression) *)
and tcExpr state (e : Untyped.expression) : tcExprOutput =
  let (trm, ty), cnstrs = tcExpr' state e.it in
  (* Print.debug "%t -> %t : %t / %t"
     (Untyped.print_expression e)
     (Term.print_expression' trm)
     (Type.print_ty ty) (Constraint.print cnstrs); *)
  ({ term = trm; ty }, cnstrs)

(* ************************************************************************* *)
(*                          COMPUTATION TYPING                               *)
(* ************************************************************************* *)

(* Dispatch: Type inference for a plan computation *)
and tcComp' state : Untyped.plain_computation -> tcCompOutput' = function
  | Value exp -> tcValue state exp
  (* Nest a list of let-bindings *)
  | Let ([], c2) ->
      let c, cnstrs = tcComp state c2 in
      ((c.term, c.ty), cnstrs)
  | Let ([ (pat, c1) ], c2) -> tcLet state pat c1 c2
  | Let ((pat, c1) :: rest, c2) ->
      let subCmp = { it = Untyped.Let (rest, c2); at = c2.at } in
      tcComp' state (Untyped.Let ([ (pat, c1) ], subCmp))
  | LetRec (defs, c2) -> tcLetRecNoGen state defs c2
  (* Pattern Matching: Special Case 2: Variable-binding *)
  | Match (scr, [ (p, c) ]) when isLocatedVarPat p ->
      tcComp' state
        (Untyped.Let ([ (p, { it = Untyped.Value scr; at = p.at }) ], c))
  (* Pattern Matching: General Case: Monomorphic patterns *)
  | Match (scr, cases) -> tcMatch state scr cases
  | Apply (val1, val2) -> tcApply state val1 val2
  | Handle (hand, cmp) -> tcHandle state hand cmp
  | Check cmp -> tcCheck state cmp

(* Type inference for a located computation *)
and tcComp state (c : Untyped.computation) : tcCompOutput =
  let (trm, ty), cnstrs = tcComp' state c.it in
  (* Print.debug "%t -> %t : %t / %t"
     (Untyped.print_computation c)
     (Term.print_computation' trm)
     (Type.print_dirty ty) (Constraint.print cnstrs); *)
  ({ term = trm; ty }, cnstrs)

(* Typecheck a value wrapped in a return *)
and tcValue state (exp : Untyped.expression) : tcCompOutput' =
  let outExpr, outCs = tcExpr state exp in
  ((Term.Value outExpr, (outExpr.ty, Type.empty_dirt)), outCs)

(* Typecheck a let where c1 is a value *)
and tcLetValNoGen state (patIn : Untyped.pattern) (e1 : Untyped.expression)
    (c2 : Untyped.computation) : tcCompOutput' =
  (* 1: Typecheck e1 *)
  let trgE1, cs1 = tcExpr state e1 in

  (* 2: Typecheck abstraction *)
  let abs, cs2 = tcAbstraction state (patIn, c2) in
  let ty_in, drty_out = abs.ty in
  (* 3: Combine the results *)
  let exp', cnstr = Constraint.cast_expression trgE1 ty_in in
  let outExpr = Term.LetVal (exp', abs) in
  let outCs = Constraint.list_union [ cnstr; cs1; cs2 ] in
  ((outExpr, drty_out), outCs)

(* Typecheck a let when c1 is a computation (== do binding) *)
and tcLetCmp state (pat : Untyped.pattern) (c1 : Untyped.computation)
    (c2 : Untyped.computation) : tcCompOutput' =
  (* 1: Typecheck c1, the pattern, and c2 *)
  let trgC1, cs1 = tcComp state c1 in
  let tyA1, dirtD1 = trgC1.ty in
  let trgPat, midState, csPat = infer_pattern state pat in
  let csPat' = Constraint.add_ty_equality (trgPat.ty, tyA1) csPat in
  let trgC2, cs2 = tcComp midState c2 in
  let tyA2, dirtD2 = trgC2.ty in

  (* 2: Generate a fresh dirt variable for the result *)
  let delta = Type.fresh_dirt () in

  (* 3: Generate the coercions for the dirts *)
  let omega1, omegaCt1 = Constraint.fresh_dirt_coer (dirtD1, delta) in
  (* s2(D1) <= delta *)
  let omega2, omegaCt2 = Constraint.fresh_dirt_coer (dirtD2, delta) in

  (*    D2  <= delta *)
  let cresC1 =
    Term.castComp (trgC1, Coercion.bangCoercion (Coercion.reflTy tyA1, omega1))
  in
  let cresC2 =
    Term.castComp (trgC2, Coercion.bangCoercion (Coercion.reflTy tyA2, omega2))
  in

  let outExpr = Term.Bind (cresC1, Term.abstraction (trgPat, cresC2)) in
  let outCs = Constraint.list_union [ omegaCt1; omegaCt2; cs1; cs2; csPat' ] in
  let outType = (tyA2, delta) in

  ((outExpr, outType), outCs)

(* Typecheck a non-recursive let *)
and tcLet state (pdef : Untyped.pattern) (c1 : Untyped.computation)
    (c2 : Untyped.computation) : tcCompOutput' =
  match c1.it with
  | Untyped.Value e1 -> tcLetValNoGen state pdef e1 c2
  | _other_computation -> tcLetCmp state pdef c1 c2

(* Typecheck a (potentially) recursive let *)
and infer_let_rec state defs =
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
        Exhaust.is_irrefutable state.tydefs p;
        Exhaust.check_computation state.tydefs c;
        let abs', cs1 = infer_abstraction state' abs in
        let abs'', cs2 =
          Constraint.full_cast_abstraction abs' alpha betadelta
        in
        ((x, abs'') :: defs, Constraint.list_union [ cs1; cs2; cs3; cnstrs ]))
      defs' ([], Constraint.empty)
  in
  (Assoc.of_list defs'', cnstrs)

and tcLetRecNoGen state defs (c2 : Untyped.computation) : tcCompOutput' =
  let defs', cs1 = infer_let_rec state defs in
  let state' =
    List.fold_left
      (fun state (x, abs) -> extend_var state x (Type.arrow abs.ty))
      state (Assoc.to_list defs')
  in
  (* 3: Typecheck c2 *)
  let trgC2, cs2 = tcComp state' c2 in

  (* 5: Combine the results *)
  let outExpr = Term.LetRec (defs', trgC2) in

  let outCs = Constraint.union cs1 cs2 in
  ((outExpr, trgC2.ty), outCs)

(* Typecheck a case expression *)
and tcMatch state (scr : Untyped.expression) (alts : Untyped.abstraction list) :
    tcCompOutput' =
  if List.length alts > 0 then tcNonEmptyMatch state scr alts
  else tcEmptyMatch state scr

and infer_cases state drty (cases : Untyped.abstraction list) =
  let ty = Type.fresh_ty_with_fresh_skel () in
  let infer_case state case (cases', cnstrs) =
    let case', cnstrs' = infer_abstraction state case in
    let ty_in, _ = case'.ty
    and case'', cnstrs'' = Constraint.cast_abstraction case' drty in
    ( case'' :: cases',
      Constraint.add_ty_equality (ty, ty_in)
        (Constraint.list_union [ cnstrs''; cnstrs'; cnstrs ]) )
  in
  let cases', cnstrs =
    List.fold_right (infer_case state) cases ([], Constraint.empty)
  in
  (cases', ty, cnstrs)

(* Typecheck a non-empty case expression *)
and tcNonEmptyMatch state (scr : Untyped.expression) alts : tcCompOutput' =
  (* 0: Make sure that we have at least one alternative *)
  assert (List.length alts > 0);

  (* 1: Generate fresh variables for the result *)
  let dirtyOut = Type.fresh_dirty_with_fresh_skel () in

  (* 2: Infer a type for the patterns *)
  let cases, patTy, cs2 = infer_cases state dirtyOut alts in

  (* 4: Typecheck the scrutinee and the alternatives *)
  let trgScr, cs1 = tcExpr state scr in

  (* 5: Generate the coercion for casting the scrutinee *)
  (* NOTE: The others should be already included in 'altRes' *)
  let matchExp, omegaCtScr = Constraint.cast_expression trgScr patTy in

  (* 6: Combine the results *)
  let outExpr = Term.Match (matchExp, cases) in
  let outCs = Constraint.list_union [ omegaCtScr; cs1; cs2 ] in
  ((outExpr, dirtyOut), outCs)

(* Typecheck an empty case expression *)
and tcEmptyMatch state (scr : Untyped.expression) : tcCompOutput' =
  (* 1: Generate fresh variables for the result *)
  let dirtyOut = Type.fresh_dirty_with_fresh_skel () in

  (* 2: Typecheck the scrutinee *)
  let trgScr, cs1 = tcExpr state scr in

  (* 3: Combine the results *)
  let outExpr = Term.Match (trgScr, []) in
  let outCs = cs1 in
  ((outExpr, dirtyOut), outCs)

(* Typecheck a function application *)
and tcApply state (val1 : Untyped.expression) (val2 : Untyped.expression) :
    tcCompOutput' =
  (* Infer the types of val1 and val2 *)
  let trgVal1, cs1 = tcExpr state val1 in
  let trgVal2, cs2 = tcExpr state val2 in

  (* Generate fresh variables for the result *)
  let outType = Type.fresh_dirty_with_fresh_skel () in

  (* Create the constraint and the cast elaborated expression *)
  let castVal1, omegaCt =
    Constraint.cast_expression trgVal1 (Type.arrow (trgVal2.ty, outType))
  in
  let outExpr = Term.Apply (castVal1, trgVal2) in
  let outCs = Constraint.list_union [ omegaCt; cs1; cs2 ] in
  ((outExpr, outType), outCs)

(* Typecheck a handle-computation *)
and tcHandle state (hand : Untyped.expression) (cmp : Untyped.computation) :
    tcCompOutput' =
  (* Typecheck the handler and the computation *)
  let trgHand, cs1 = tcExpr state hand in
  (* Typecheck the handler *)
  let trgCmp, cs2 = tcComp state cmp in

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

(* Typecheck a "Check" expression (GEORGE does not know what this means yet *)
and tcCheck (state : state) (cmp : Untyped.computation) : tcCompOutput' =
  let cmp', cnstrs = tcComp state cmp in
  ((Term.Check cmp', Type.pure_ty Type.unit_ty), cnstrs)

(* GEORGE: Planned TODO for the future I guess?? *)

(* ************************************************************************* *)
(*                               UTILITIES                                   *)
(* ************************************************************************* *)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and infer_abstraction (state : state) (pat, cmp) :
    Term.abstraction * Constraint.t =
  let trgPat, state', cs1 = infer_pattern state pat in
  let trgCmp, cs2 = tcComp state' cmp in
  (Term.abstraction (trgPat, trgCmp), Constraint.union cs1 cs2)

and check_abstraction state abs patTy : Term.abstraction * Constraint.t =
  let { term = trgPat, trgCmp; _ }, cs = infer_abstraction state abs in
  let trgPat' = { trgPat with ty = patTy } in
  ( Term.abstraction (trgPat', trgCmp),
    Constraint.add_ty_equality (trgPat.ty, patTy) cs )

and infer_abstraction2 (state : state) (pat1, pat2, cmp) :
    Term.abstraction2 * Constraint.t =
  let trgPat1, state', cs1 = infer_pattern state pat1 in
  let trgPat2, state', cs2 = infer_pattern state' pat2 in
  let trgCmp, cs = tcComp state' cmp in
  ( Term.abstraction2 (trgPat1, trgPat2, trgCmp),
    Constraint.list_union [ cs1; cs2; cs ] )

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and check_abstraction2 state abs2 patTy1 patTy2 :
    Term.abstraction2 * Constraint.t =
  let { term = trgPat1, trgPat2, trgCmp; _ }, cs =
    infer_abstraction2 state abs2
  in
  let trgPat1' = { trgPat1 with ty = patTy1 }
  and trgPat2' = { trgPat2 with ty = patTy2 } in
  ( Term.abstraction2 (trgPat1', trgPat2', trgCmp),
    cs
    |> Constraint.add_ty_equality (trgPat1.ty, patTy1)
    |> Constraint.add_ty_equality (trgPat2.ty, patTy2) )

(* ************************************************************************* *)
(* ************************************************************************* *)

let monomorphize free_ty_params cnstrs =
  let free_cnstrs_params = Type.Constraints.free_params cnstrs in
  let free_params = Type.Params.union free_ty_params free_cnstrs_params in
  let cnstrs' =
    Constraint.empty
    |> List.fold_right
         (fun sk ->
           Constraint.add_skeleton_equality
             (Type.SkelParam sk, Type.SkelBasic Const.FloatTy))
         (Type.SkelParam.Set.elements free_params.skel_params)
    |> List.fold_right
         (fun (t, skel) ->
           Constraint.add_ty_inequality
             ( Type.TyCoercionParam.fresh (),
               (Type.tyParam t skel, Type.tyBasic Const.FloatTy) ))
         (Type.TyParam.Map.bindings free_params.ty_params)
    |> List.fold_right
         (fun d ->
           Constraint.add_dirt_inequality
             ( Type.DirtCoercionParam.fresh (),
               (Type.no_effect_dirt d, Type.empty_dirt) ))
         (Type.DirtParam.Set.elements free_params.dirt_params)
  in
  let sub, residuals =
    Unification.solve (Constraint.union cnstrs' (Constraint.unresolve cnstrs))
  in
  (* After zapping, there should be no more constraints left to solve. *)
  assert (Type.Constraints.is_empty residuals);
  sub

let infer_computation state comp =
  let comp', cnstrs = tcComp state comp in
  let sub, residuals = Unification.solve cnstrs in
  (subInCmp sub comp', residuals)

let infer_expression state expr =
  let expr', cnstrs = tcExpr state expr in
  let sub, residuals = Unification.solve cnstrs in
  (subInExp sub expr', residuals)

let infer_rec_abstraction state defs =
  let defs', cnstrs = infer_let_rec state defs in
  let sub, residuals = Unification.solve cnstrs in
  (Assoc.map (Term.apply_substitutions_to_abstraction sub) defs', residuals)

(* Typecheck a top-level expression *)
let process_computation state comp =
  let comp', residuals = infer_computation state comp in
  (* Print.debug "TERM: %t" (Term.print_computation comp); *)
  (* Print.debug "TYPE: %t" (Type.print_dirty comp.ty); *)
  (* Print.debug "CONSTRAINTS: %t" (Constraint.print_constraints residuals); *)
  let free_params = Term.free_params_computation comp' in
  let mono_sub = monomorphize free_params residuals in
  (* Print.debug "SUB: %t" (Substitution.print_substitutions mono_sub); *)
  let mono_comp = subInCmp mono_sub comp' in
  (* Print.debug "MONO TERM: %t" (Term.print_computation mono_comp); *)
  (* Print.debug "MONO TYPE: %t" (Type.print_dirty mono_comp.ty); *)
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (Type.Params.is_empty (Term.free_params_computation mono_comp));
  Exhaust.check_computation state.tydefs comp;
  mono_comp

let process_top_let state defs =
  let fold (p, c) (state', defs) =
    match (p.it, c.it) with
    | Language.UntypedSyntax.PVar x, Language.UntypedSyntax.Value v ->
        let expr, constraints = infer_expression state v in
        let params =
          Type.Params.union
            (Type.free_params_ty expr.ty)
            (Type.Constraints.free_params constraints)
        in
        let ty_scheme = Type.{ params; constraints; ty = expr.ty } in
        let state'' = extend_poly_var state' x ty_scheme in
        Exhaust.is_irrefutable state.tydefs p;
        Exhaust.check_computation state.tydefs c;
        (state'', (x, (params, constraints, expr)) :: defs)
    | _ -> failwith __LOC__
  in
  let state', defs' = List.fold_right fold defs (state, []) in
  (state', Assoc.of_list defs')

let process_top_let_rec state defs =
  let defs, constraints = infer_rec_abstraction state (Assoc.to_list defs) in
  let defs_params = Term.free_params_definitions defs in
  let cnstrs_params = Type.Constraints.free_params constraints in
  let params = Type.Params.union defs_params cnstrs_params in
  let state', defs' =
    Assoc.fold_right
      (fun (f, (abs : Term.abstraction)) (state, defs) ->
        let (ty_scheme : Type.ty_scheme) =
          Type.{ params; constraints; ty = Type.arrow abs.ty }
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

let add_type_definitions ~loc state tydefs =
  {
    state with
    tydefs =
      TypeDefinitionContext.extend_type_definitions ~loc tydefs state.tydefs;
  }

let load_primitive_effect state eff prim =
  let ty1, ty2 = Primitives.primitive_effect_signature prim in
  ( { state with effects = Type.Effect.Map.add eff (ty1, ty2) state.effects },
    (ty1, ty2) )

let load_primitive_value state x prim =
  let ty = Primitives.primitive_value_type_scheme prim in
  extend_poly_var state x ty
