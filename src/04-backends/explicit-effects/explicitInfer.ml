open Utils
module Const = Language.Const
module Untyped = Language.UntypedSyntax
module CoreTypes = Language.CoreTypes
module TypeDefinitionContext = Typechecker.TypeDefinitionContext

(* GEORGE: TODO:
     1. Add debugging output to the new code snippets
     2. Figure out what is wrong with pattern typing (untyped & typed version)
     3. Understand how variants are implemented
 *)

(* GEORGE: By convention, in types, type inequalities are qualified over first,
and then dirt inequalities *)

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

(* [WRITER] SUBSTITUTION *)

(* Extend the generated substitution *)
let extendGenSub acc sub = Substitution.merge acc sub

(* GEORGE: I hope to God for the order to be correct here *)

(* [STATE] INFERENCE STATE *)

type state = {
  variables : TypingEnv.t;
  (* Global Typing Environment *)
  effects : (Type.ty * Type.ty) Term.EffectMap.t;
  (* Valid Effects             *)
  tydefs : TypeDefinitionContext.state; (* Type definition context *)
}

(* A bag/list of constraints *)
type constraints = Constraint.omega_ct list

(* Add a single term binding to the global typing environment *)
let extend_var env x ty_sch =
  { env with variables = TypingEnv.update env.variables x ty_sch }

(* Apply a substitution to the global typing environment *)
let apply_sub_to_variables env sub =
  { env with variables = TypingEnv.apply_sub env.variables sub }

(* Extend the global typing environment with multiple term bindings *)
let extend_env vars env =
  List.fold_right (fun (x, ty_sch) env -> extend_var env x ty_sch) vars env

(* Initial type inference state: everything is empty *)
let initial_state : state =
  {
    variables = TypingEnv.empty;
    effects = Term.EffectMap.empty;
    tydefs = TypeDefinitionContext.initial_state;
  }

let add_effect eff (ty1, ty2) state =
  { state with effects = Term.EffectMap.add eff (ty1, ty2) state.effects }

(* ... *)

(* ************************************************************************* *)
(*                            SUBSTITUTIONS                                  *)
(* ************************************************************************* *)

(* Substitute in typing environments *)
let subInEnv sub env = TypingEnv.apply_sub env sub

(* Substitute in target values and computations *)
let subInCmp sub cmp = Substitution.apply_substitutions_to_computation sub cmp

let subInExp sub exp = Substitution.apply_substitutions_to_expression sub exp

let subInAbs sub abs = Substitution.apply_substitutions_to_abstraction sub abs

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
(*                           PARTITION TYPES                                 *)
(* ************************************************************************* *)

(* Partition a HM-like type into its corresponding abstractions. We follow the
 * original publication and expect the abstractions in this strict order:
 * skeleton variables, type variables, dirt variables, type inequalities, and
 * dirt inequalities. At the end, there should be a HM-monotype (that is, no
 * qualification or quantification in nested positions). If the type is not in
 * that exact form, [stripHindleyMilnerLikeTy] will return [None]. *)
let stripHindleyMilnerLikeTy :
    Type.ty ->
    (Type.ct_ty list
    (* Type inequalities *)
    * Type.ct_dirt list
    (* Dirt inequalities *)
    * Type.ty)
    option =
  (* Remaining monotype *)
  let rec stripTyQual = function
    | Type.QualTy (ct, ty) ->
        let cs, rem = stripTyQual ty in
        (ct :: cs, rem)
    | other_type -> ([], other_type)
  in
  let rec stripDirtQual = function
    | Type.QualDirt (ct, ty) ->
        let cs, rem = stripDirtQual ty in
        (ct :: cs, rem)
    | other_type -> ([], other_type)
  in
  function
  | inTy ->
      let allTyCs, ty1 = stripTyQual inTy in
      (* 1: Strip off the type inequality qualification *)
      let allDirtCs, ty2 = stripDirtQual ty1 in
      (* 2: Strip off the dirt inequality qualification *)
      if Type.isMonoTy ty2 (* 3: Ensure the remainder is a monotype *) then
        Some (allTyCs, allDirtCs, ty2)
      else None

(* ************************************************************************* *)
(*                       VARIABLE INSTANTIATION                              *)
(* ************************************************************************* *)

let instantiateVariable (x : Term.variable) (scheme : Type.ty) :
    Term.expression * Type.ty * Constraint.omega_ct list =
  (* 1: Take the type signature apart *)
  let tyCs, dirtCs, monotype =
    match stripHindleyMilnerLikeTy scheme with
    | Some (a, b, c) -> (a, b, c)
    | None -> failwith "instantiateVariable: Non-HM type in the environment!"
  in

  (* 2: Generate the freshening substitution *)
  let sub = Substitution.empty in

  (* 3: Generate the wanted type inequality constraints *)
  let tyOmegas, wantedTyCs =
    tyCs
    |> List.map (fun ct -> Constraint.fresh_ty_coer (subInTyCt sub ct))
    |> List.split
  in

  (* 4: Generate the wanted dirt inequality constraints *)
  let dirtOmegas, wantedDirtCs =
    dirtCs
    |> List.map (fun ct -> Constraint.fresh_dirt_coer (subInDirtCt sub ct))
    |> List.split
  in

  (* 5: Apply x to all its fresh arguments *)
  let targetX = applyTerm tyOmegas dirtOmegas (Term.var x scheme) in

  (* 6: Combine the results *)
  (targetX, subInValTy sub monotype, wantedTyCs @ wantedDirtCs)

(* ************************************************************************* *)
(*                           BASIC DEFINITIONS                               *)
(* ************************************************************************* *)

(* Constraint generation output *)
type 'a tcOutput = 'a * constraints

(* Value typing output *)
type tcExprOutput' = (Term.expression' * Type.ty) tcOutput

type tcExprOutput = Term.expression tcOutput

(* Computation typing output *)
type tcCompOutput' = (Term.computation' * Type.dirty) tcOutput

type tcCompOutput = Term.computation tcOutput

(* Typecheck a list of things *)
let rec tcMany state (xss : 'a list) tc =
  match xss with
  | [] -> (([], []), [])
  | x :: xs ->
      let y, cs1 = tc state x in
      let (ys, tys), cs2 = tcMany state xs tc in
      ((y :: ys, y.ty :: tys), cs1 @ cs2)

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)

let rec check_pattern state ty (pat : Untyped.pattern) : Term.pattern * state =
  let pat', state' = check_pattern' state ty pat in
  ({ term = pat'; ty }, state')

and check_pattern' state ty pat =
  match pat.it with
  | Untyped.PVar x -> (Term.PVar x, extend_var state x ty)
  | Untyped.PAnnotated (p, ty') when Type.source_to_target state.tydefs ty' = ty
    ->
      let p', state = check_pattern state ty p in
      (p'.term, state)
  | Untyped.PNonbinding -> (Term.PNonbinding, state)
  | Untyped.PConst c when ty = Type.type_const c -> (Term.PConst c, state)
  | Untyped.PTuple ps -> (
      match ty with
      | Type.Tuple tys ->
          let fold p ty (ps', state) =
            let p', state' = check_pattern state ty p in
            (p' :: ps', state')
          in
          let ps', state' = List.fold_right2 fold ps tys ([], state) in
          let p = Term.pTuple ps' in
          (p.term, state')
      | _ ->
          failwith
            "check_pattern: Please no pattern matching in lambda abstractions!")
  | Untyped.PVariant (lbl, p) -> (
      match (p, Type.constructor_signature state.tydefs lbl) with
      | None, (None, out_ty) when out_ty = ty ->
          (Term.PVariant (lbl, None), state)
      | Some p, (Some in_ty, out_ty) when out_ty = ty ->
          let p', state' = check_pattern state in_ty p in
          (Term.PVariant (lbl, Some p'), state')
      | _, (_, out_ty) ->
          Error.typing ~loc:pat.at
            "check_pattern: Variant output type %t does not match %t"
            (Type.print_ty out_ty) (Type.print_ty ty))
  | _ ->
      Error.typing ~loc:pat.at "check_pattern: Unsupported pattern %t"
        (Untyped.print_pattern pat)

let rec infer_pattern state (pat : Untyped.pattern) :
    Term.pattern * state * constraints =
  let pat', ty, state', cnstrs = infer_pattern' state pat in
  ({ term = pat'; ty }, state', cnstrs)

and infer_pattern' state pat =
  match pat.it with
  | Untyped.PVar x ->
      let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
      (Term.PVar x, alpha, extend_var state x alpha, [ alphaSkel ])
  | Untyped.PAnnotated (p, ty) ->
      let ty' = Type.source_to_target state.tydefs ty in
      let p', state' = check_pattern state ty' p in
      (p'.term, ty', state', [])
  | Untyped.PNonbinding ->
      let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
      (Term.PNonbinding, alpha, state, [ alphaSkel ])
  | Untyped.PConst c -> (Term.PConst c, Type.type_const c, state, [])
  | Untyped.PTuple ps ->
      let fold p (ps', state, cnstrs) =
        let p', state', cnstrs' = infer_pattern state p in
        (p' :: ps', state', cnstrs' @ cnstrs)
      in
      let ps', state', cnstrs = List.fold_right fold ps ([], state, []) in
      let p = Term.pTuple ps' in
      (p.term, p.ty, state', cnstrs)
  | Untyped.PVariant (lbl, p) -> (
      match (p, Type.constructor_signature state.tydefs lbl) with
      | None, (None, out_ty) -> (Term.PVariant (lbl, None), out_ty, state, [])
      | Some p, (Some in_ty, out_ty) ->
          let p', state' = check_pattern state in_ty p in
          (Term.PVariant (lbl, Some p'), out_ty, state', [])
      | _ -> assert false)
  | _ ->
      Error.typing ~loc:pat.at "infer_pattern: Unsupported pattern %t"
        (Untyped.print_pattern pat)

let isLocatedVarPat (pat : Untyped.pattern) : bool =
  match pat.it with Untyped.PVar _ -> true | _other_pattern -> false

(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)

(* ************************************************************************* *)
(*                             VALUE TYPING                                  *)
(* ************************************************************************* *)

(* Lookup the type of a term variable in the local and the global contexts
 * (local first, global after). George: I wish we had monads.. *)
let lookupTmVar state x = TypingEnv.lookup state.variables x

(* Term Variables *)
let rec tcVar state (x : Term.variable) : tcExprOutput' =
  match lookupTmVar state x with
  | Some scheme ->
      let x, x_monotype, constraints = instantiateVariable x scheme in
      ((x.term, x_monotype), constraints)
  | None -> assert false

(* Constants *)
and tcConst (_state : state) (c : Const.t) : tcExprOutput' =
  ((Term.Const c, Type.type_const c), [])

(* Type-annotated Expressions *)
and tcAnnotated (_state : state)
    ((_e, _ty) : Untyped.expression * Language.Type.ty) : tcExprOutput' =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* Tuples *)
and tcTuple state (es : Untyped.expression list) : tcExprOutput' =
  let (es, tys), cs = tcMany state es tcExpr in
  ((Term.Tuple es, Type.Tuple tys), cs)

(* Records *)
and tcRecord (_state : state) (_lst : (field, Untyped.expression) Assoc.t) :
    tcExprOutput' =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* Variants *)
and tcVariant state ((lbl, mbe) : label * Untyped.expression option) :
    tcExprOutput' =
  match (Type.constructor_signature state.tydefs lbl, mbe) with
  | (None, ty_out), None -> ((Term.Variant (lbl, None), ty_out), [])
  | (Some ty_in, ty_out), Some e ->
      let e', cs1 = tcExpr state e in
      (* GEORGE: Investigate how cast_expression works *)
      let castExp, castCt = Term.cast_expression e' ty_in in
      ((Term.Variant (lbl, Some castExp), ty_out), castCt :: cs1)
  | _, _ -> failwith "tcVariant"

and tcAbstraction state (pat, cmp) =
  let pat', state', cnstrs1 = infer_pattern state pat in
  let cmp', cnstrs2 = tcComp state' cmp in
  (Term.abstraction (pat', cmp'), cnstrs1 @ cnstrs2)

(* Lambda Abstractions *)
and tcLambda state abs =
  let abs', cnstrs = tcAbstraction state abs in
  ((Term.Lambda abs', Type.Arrow abs'.ty), cnstrs)

and tcEffect state (eff : Untyped.effect) : tcExprOutput' =
  (* GEORGE: NOTE: This is verbatim copied from the previous implementation *)
  let in_ty, out_ty = Term.EffectMap.find eff state.effects
  and s = Type.EffectSet.singleton eff in
  let out_drty = (out_ty, Type.closed_dirt s) in
  let x_pat, x_var = Term.fresh_variable "x" in_ty
  and y_pat, y_var = Term.fresh_variable "y" out_ty in
  let ret, cnstrs = Term.cast_computation (Term.value y_var) out_drty in
  let outVal =
    Term.Lambda
      (Term.abstraction
         ( x_pat,
           Term.call
             ((eff, (in_ty, out_ty)), x_var, Term.abstraction (y_pat, ret)) ))
  in
  let outType = Type.Arrow (in_ty, out_drty) in
  ((outVal, outType), cnstrs)

(* Handlers(Op Cases) *)
and tcOpCases state (eclauses : (Untyped.effect, Untyped.abstraction2) Assoc.t)
    (dirtyOut : Type.dirty) : (Term.effect, Term.abstraction2) Assoc.t tcOutput
    =
  let rec go cs =
    match Assoc.to_list cs with
    | [] -> ([], [])
    | c :: cs ->
        let y, cs1 = tcOpCase state c dirtyOut in
        let ys, cs2 = go (Assoc.of_list cs) in
        (y :: ys, cs1 @ cs2)
  in
  let allClauses, allCs = go eclauses in
  (Assoc.of_list allClauses, allCs)

(* Handlers(Op Case) *)
and tcOpCase state
    ((eff, abs2) : Untyped.effect * Untyped.abstraction2) (* Op clause *)
    (dirtyOut : Type.dirty) (* Expected output type *) =
  (* 1: Lookup the type of Opi *)
  let tyAi, tyBi = Term.EffectMap.find eff state.effects in

  (* 2: Generate fresh variables for the type of the codomain of the continuation *)
  let dirtyi, alphaiSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 3: Typecheck the clause *)
  let abs2, csi (* GEORGE: I don't like the unused types *) =
    check_abstraction2 state abs2 tyAi (Type.Arrow (tyBi, dirtyi))
  in

  let (xop, kop, trgCop), (_, _, (tyBOpi, dirtDOpi)) = (abs2.term, abs2.ty) in

  (* 4: Make sure that the pattern for k is a variable one.
   *    We do not support anything else at the moment *)
  let k =
    match kop.term with
    | Term.PVar k -> k
    | _ -> failwith "tcOpCase: only varpats allowed"
  in

  (* 5: Generate all the needed constraints *)
  let omega34i, omegaCt34i =
    Constraint.fresh_dirty_coer ((tyBOpi, dirtDOpi), dirtyOut)
  in
  let leftty = Type.Arrow (tyBi, dirtyOut) in
  let rightty = Type.Arrow (tyBi, dirtyi) in

  (* 6: Create the elaborated clause *)
  let lvar = CoreTypes.Variable.fresh "l" in
  let castExp, omegaCt5i =
    Term.cast_expression (Term.var lvar leftty) rightty
  in
  let lsub = Term.subst_comp (Assoc.of_list [ (k, castExp) ]) in
  let outExpr =
    ( ((eff, (tyAi, tyBi)) : Term.effect) (* Opi *),
      Term.abstraction2
        (xop, Term.pVar lvar leftty, Term.castComp (lsub trgCop, omega34i)) )
  in

  (* 7: Combine the results *)
  let outCs = (alphaiSkel :: omegaCt34i) @ (omegaCt5i :: csi) in
  (outExpr, outCs)

(* Handlers *)
and tcHandler state (h : Untyped.handler) : tcExprOutput' =
  (* 1: Generate fresh variables for the input and output types *)
  let deltaIn = Type.fresh_dirt () in
  let ((_, deltaOut) as dirtyOut), alphaOutSkel =
    Constraint.fresh_dirty_with_fresh_skel ()
  in

  (* 2: Process the return and the operation clauses *)
  let trgRet, cs1 = tcAbstraction state h.value_clause in
  let trgCls, cs2 = tcOpCases state h.effect_clauses dirtyOut in

  (* 3: Create the omega7 coercion (cast the whole handler) *)
  let ty_ret_in, _ = trgRet.ty in
  let omega7, omegaCt7 =
    let allOps =
      trgCls |> Assoc.to_list
      |> List.map (fun ((eff, _), _) -> eff)
      |> Type.EffectSet.of_list
    in

    (* GEORGE: This should be done in a cleaner way but let's leave it for later *)
    let deltaOutVar =
      match deltaOut.row with
      | ParamRow deltaOutVar -> deltaOutVar
      | EmptyRow -> failwith "deltaOut: IMPOSSIBLE"
    in

    Constraint.fresh_dirt_coer
      (deltaIn, Type.{ effect_set = allOps; row = ParamRow deltaOutVar })
  in

  let handlerCo =
    Constraint.handlerCoercion
      ( Constraint.bangCoercion (Constraint.reflTy ty_ret_in, omega7),
        Constraint.reflDirty dirtyOut )
  in
  let handTy, _ = handlerCo.ty in
  match handTy with
  | Type.Handler (inTy, outTy) ->
      let trgRet', cnstr_ret = Term.cast_abstraction trgRet dirtyOut in
      let handler =
        Term.Handler (Term.fresh_handler trgRet' trgCls (inTy, outTy))
      in
      let outExpr = Term.CastExp ({ term = handler; ty = handTy }, handlerCo) in
      let outType = Type.Handler ((ty_ret_in, deltaIn), dirtyOut) in
      let outCs = ((omegaCt7 :: alphaOutSkel :: cnstr_ret) @ cs1) @ cs2 in
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
  (* Nest a list of letrec-bindings; MUTUAL RECURSION NOT ALLOWED AT THE MOMENT *)
  | LetRec ([], c2) ->
      let c, cnstrs = tcComp state c2 in
      ((c.term, c.ty), cnstrs)
  | LetRec ([ (var, abs) ], c2) -> tcLetRecNoGen state var abs c2
  | LetRec ((var, abs) :: rest, c2) ->
      let subCmp = { it = Untyped.LetRec (rest, c2); at = c2.at } in
      tcComp' state (Untyped.LetRec ([ (var, abs) ], subCmp))
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

  (* (v',A, Qv, Sigma1) *)

  (* 2: Typecheck c2 *)
  let x =
    match patIn.it with
    | Untyped.PVar x -> x (* GEORGE: Support nothing else at the moment *)
    | _ -> failwith "tcLetValNoGen: only varpats allowed"
  in
  let trgC2, cs2 = tcComp (extend_var state x trgE1.ty) c2 in

  (* 3: Combine the results *)
  let outExpr =
    Term.LetVal (trgE1, Term.abstraction (Term.pVar x trgE1.ty, trgC2))
  in
  let outCs = cs1 @ cs2 in
  ((outExpr, trgC2.ty), outCs)

(* Typecheck a let when c1 is a computation (== do binding) *)
and tcLetCmp state (pat : Untyped.pattern) (c1 : Untyped.computation)
    (c2 : Untyped.computation) : tcCompOutput' =
  (* 1: Typecheck c1, the pattern, and c2 *)
  let trgC1, cs1 = tcComp state c1 in
  let tyA1, dirtD1 = trgC1.ty in
  let trgPat, midState = check_pattern state tyA1 pat in
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
    Term.castComp
      (trgC1, Constraint.bangCoercion (Constraint.reflTy tyA1, omega1))
  in
  let cresC2 =
    Term.castComp
      (trgC2, Constraint.bangCoercion (Constraint.reflTy tyA2, omega2))
  in

  let outExpr = Term.Bind (cresC1, Term.abstraction (trgPat, cresC2)) in
  let outType = (tyA2, delta) in
  let outCs = (omegaCt1 :: omegaCt2 :: cs1) @ cs2 in

  ((outExpr, outType), outCs)

(* Typecheck a non-recursive let *)
and tcLet state (pdef : Untyped.pattern) (c1 : Untyped.computation)
    (c2 : Untyped.computation) : tcCompOutput' =
  match c1.it with
  | Untyped.Value e1 -> tcLetValNoGen state pdef e1 c2
  | _other_computation -> tcLetCmp state pdef c1 c2

(* Typecheck a (potentially) recursive let *)
and infer_let_rec state (var : Untyped.variable) (abs : Untyped.abstraction) =
  (* 1: Generate fresh variables for everything *)
  let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let betadelta, betaSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Typecheck the abstraction *)
  let abs, cs1 =
    check_abstraction
      (extend_var state var (Type.Arrow (alpha, betadelta)))
      abs alpha
  in

  let (trgPat, trgC1), (_trgPatTy, dirty1) = (abs.term, abs.ty) in

  (* 3: The assumed type should be at least as general as the inferred one *)
  let omega12, omegaCt12 = Constraint.fresh_dirty_coer (dirty1, betadelta) in

  (* 4: Create the (complicated) c1''. *)
  let c1'' =
    let f_coercion =
      Constraint.arrowCoercion (Constraint.reflTy alpha, omega12)
    in
    let subst_fn =
      Term.subst_comp
        (Assoc.of_list
           [
             ( var,
               Term.castExp
                 (Term.var var (Type.Arrow (alpha, dirty1)), f_coercion) );
           ])
    in

    subst_fn trgC1
  in
  let outCs = (alphaSkel :: betaSkel :: omegaCt12) @ cs1 in

  (Term.abstraction (trgPat, c1''), outCs)

and tcLetRecNoGen state (var : Untyped.variable) (abs : Untyped.abstraction)
    (c2 : Untyped.computation) : tcCompOutput' =
  let abs, cs1 = infer_let_rec state var abs in

  (* 3: Typecheck c2 *)
  let trgC2, cs2 = tcComp (extend_var state var (Type.Arrow abs.ty)) c2 in

  (* 5: Combine the results *)
  let outExpr = Term.LetRec ([ (var, abs) ], trgC2) in

  let outCs = cs1 @ cs2 in
  ((outExpr, trgC2.ty), outCs)

(* Typecheck a case expression *)
and tcMatch state (scr : Untyped.expression) (alts : Untyped.abstraction list) :
    tcCompOutput' =
  if List.length alts > 0 then tcNonEmptyMatch state scr alts
  else tcEmptyMatch state scr

and infer_cases state drty (cases : Untyped.abstraction list) =
  let infer_pattern_ty state (pat, _) =
    match infer_pattern state pat with
    | { ty; _ }, _, [] -> Some ty
    | _, _, _ :: _ -> None
  and infer_case state ty case (cases', cnstrs) =
    let case', cnstrs' = check_abstraction state case ty in
    let case'', cnstrs'' = Term.cast_abstraction case' drty in
    (case'' :: cases', cnstrs'' @ cnstrs' @ cnstrs)
  in
  match List.filter_map (infer_pattern_ty state) cases with
  | [] -> failwith "Annotate one case so that it's type may be inferred"
  | ty :: _ ->
      let cases', cnstrs =
        List.fold_right (infer_case state ty) cases ([], [])
      in
      (cases', ty, cnstrs)

(* Typecheck a non-empty case expression *)
and tcNonEmptyMatch state (scr : Untyped.expression) alts : tcCompOutput' =
  (* 0: Make sure that we have at least one alternative *)
  assert (List.length alts > 0);

  (* 1: Generate fresh variables for the result *)
  let dirtyOut, alphaOutSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Infer a type for the patterns *)
  let cases, patTy, cs2 = infer_cases state dirtyOut alts in

  (* 4: Typecheck the scrutinee and the alternatives *)
  let trgScr, cs1 = tcExpr state scr in

  (* 5: Generate the coercion for casting the scrutinee *)
  (* NOTE: The others should be already included in 'altRes' *)
  let matchExp, omegaCtScr = Term.cast_expression trgScr patTy in

  (* 6: Combine the results *)
  let outExpr = Term.Match (matchExp, cases) in
  let outCs = (alphaOutSkel :: omegaCtScr :: cs1) @ cs2 in
  ((outExpr, dirtyOut), outCs)

(* Typecheck an empty case expression *)
and tcEmptyMatch state (scr : Untyped.expression) : tcCompOutput' =
  (* 1: Generate fresh variables for the result *)
  let dirtyOut, alphaOutSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Typecheck the scrutinee *)
  let trgScr, cs1 = tcExpr state scr in

  (* 3: Combine the results *)
  let outExpr = Term.Match (trgScr, []) in
  let outCs = alphaOutSkel :: cs1 in
  ((outExpr, dirtyOut), outCs)

(* Typecheck a function application *)
and tcApply state (val1 : Untyped.expression) (val2 : Untyped.expression) :
    tcCompOutput' =
  (* Infer the types of val1 and val2 *)
  let trgVal1, cs1 = tcExpr state val1 in
  let trgVal2, cs2 = tcExpr state val2 in

  (* Generate fresh variables for the result *)
  let outType, alphaSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* Create the constraint and the cast elaborated expression *)
  let castVal1, omegaCt =
    Term.cast_expression trgVal1 (Type.Arrow (trgVal2.ty, outType))
  in
  let outExpr = Term.Apply (castVal1, trgVal2) in
  let outCs = (alphaSkel :: omegaCt :: cs1) @ cs2 in
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
  let dirty1, alphaSkel1 = Constraint.fresh_dirty_with_fresh_skel () in
  let dirty2, alphaSkel2 = Constraint.fresh_dirty_with_fresh_skel () in

  (* Create all constraints *)
  let castHand, omegaCt1 =
    Term.cast_expression trgHand (Type.Handler (dirty1, dirty2))
  in
  let castCmp, omegaCt23 = Term.cast_computation trgCmp dirty1 in

  (* Combine all the outputs *)
  let outExpr = Term.Handle (castHand, castCmp) in
  let outCs = (alphaSkel1 :: alphaSkel2 :: omegaCt1 :: omegaCt23) @ cs1 @ cs2 in
  ((outExpr, dirty2), outCs)

(* Typecheck a "Check" expression (GEORGE does not know what this means yet *)
and tcCheck (_state : state) (_cmp : Untyped.computation) : tcCompOutput' =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* ************************************************************************* *)
(*                               UTILITIES                                   *)
(* ************************************************************************* *)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and check_abstraction state (pat, cmp) patTy :
    Term.abstraction * Constraint.omega_ct list =
  let trgPat, state' = check_pattern state patTy pat in
  let trgCmp, cs = tcComp state' cmp in
  (Term.abstraction (trgPat, trgCmp), cs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and check_abstraction2 state (pat1, pat2, cmp) patTy1 patTy2 :
    Term.abstraction2 * Constraint.omega_ct list =
  let trgPat1, state' = check_pattern state patTy1 pat1 in
  let trgPat2, state'' = check_pattern state' patTy2 pat2 in
  let trgCmp, cs = tcComp state'' cmp in
  (Term.abstraction2 (trgPat1, trgPat2, trgCmp), cs)

(* ************************************************************************* *)
(*                     LET-GENERALIZATION UTILITIES                          *)
(* ************************************************************************* *)

(* GEORGE: I would suggest adding more checks here;
 * only a few kinds of constraints are expected after constraint solving. *)
let rec partitionResidualCs = function
  | [] -> ([], [], [])
  | Constraint.TyParamHasSkel (a, Type.SkelParam s) :: rest ->
      let alphaSkels, tyCs, dirtCs = partitionResidualCs rest in
      ((a, s) :: alphaSkels, tyCs, dirtCs)
  | TyOmega (o, ct) :: rest ->
      let alphaSkels, tyCs, dirtCs = partitionResidualCs rest in
      (alphaSkels, (o, ct) :: tyCs, dirtCs)
  | DirtOmega (o, ct) :: rest ->
      let alphaSkels, tyCs, dirtCs = partitionResidualCs rest in
      (alphaSkels, tyCs, (o, ct) :: dirtCs)
  | _cs -> failwith "partitionResidualCs: malformed"

(* Detect the components to abstract over from the residual constraints. To be
 * used in let-generalization. *)
(* GEORGE NOTE: We might have "dangling" dirt variables at the end. In the end
 * check whether this is the case and if it is compute the dirt variables from
 * the elaborated expression and pass them in. *)
let mkGenParts (cs : Constraint.omega_ct list) :
    Type.SkelParam.t list
    * (CoreTypes.TyParam.t * Type.skeleton) list
    * Type.DirtParam.t list
    * (Type.TyCoercionParam.t * Type.ct_ty) list
    * (Type.DirtCoercionParam.t * Type.ct_dirt) list =
  let alphasSkelVars, tyCs, dirtCs = partitionResidualCs cs in
  let skelVars =
    alphasSkelVars
    |> List.map snd (* Keep only the skeleton variables *)
    |> Type.SkelParamSet.of_list (* Convert to a set *)
    |> Type.SkelParamSet.elements
  in

  (* Convert back to a list *)
  let alphaSkels =
    List.map (fun (a, s) -> (a, Type.SkelParam s)) alphasSkelVars
  in
  let dirtVars =
    Type.DirtParamSet.elements
      (Type.FreeParams.union_map Constraint.free_params_constraint cs)
        .dirt_params
  in
  (*let tyDirtVars  = Type.fdvsOfTargetValTy valTy in (* fv(A) *) *)
  (skelVars, alphaSkels, dirtVars, tyCs, dirtCs)

(* Create a generalized type from parts (as delivered from "mkGenParts"). *)
let mkGeneralizedType (_freeSkelVars : Type.SkelParam.t list)
    (_annFreeTyVars : (CoreTypes.TyParam.t * Type.skeleton) list)
    (_freeDirtVars : Type.DirtParam.t list)
    (tyCs : (Type.TyCoercionParam.t * Type.ct_ty) list)
    (dirtCs : (Type.DirtCoercionParam.t * Type.ct_dirt) list)
    (monotype : Type.ty) : Type.ty =
  (* expected to be a monotype! *)
  monotype
  |> (* 1: Add the constraint abstractions (dirt) *)
  List.fold_right (fun (_, pi) qual -> Type.QualDirt (pi, qual)) dirtCs
  |> (* 2: Add the constraint abstractions (type) *)
  List.fold_right (fun (_, pi) qual -> Type.QualTy (pi, qual)) tyCs

(* Create a generalized term from parts (as delivered from "mkGenParts"). *)
(* GEORGE NOTE: We might have "dangling" dirt variables at the end. In the end
 * check whether this is the case and if it is compute the dirt variables from
 * the elaborated expression and pass them in. *)
let mkGeneralizedExpression (_freeSkelVars : Type.SkelParam.t list)
    (_annFreeTyVars : (CoreTypes.TyParam.t * Type.skeleton) list)
    (_freeDirtVars : Type.DirtParam.t list)
    (tyCs : (Type.TyCoercionParam.t * Type.ct_ty) list)
    (dirtCs : (Type.DirtCoercionParam.t * Type.ct_dirt) list)
    (exp : Term.expression) : Term.expression =
  exp
  |> (* 1: Add the constraint abstractions (dirt) *)
  List.fold_right
    (fun (omega, _pi) qual -> Term.lambdaDirtCoerVar (omega, qual))
    dirtCs
  |> (* 2: Add the constraint abstractions (type) *)
  List.fold_right
    (fun (omega, _pi) qual -> Term.lambdaTyCoerVar (omega, qual))
    tyCs

let generalize cs ty expr =
  let freeSkelVars, annFreeTyVars, freeDirtVars, tyVs, dirtCs = mkGenParts cs in
  let ty' =
    mkGeneralizedType freeSkelVars annFreeTyVars freeDirtVars tyVs dirtCs ty
  and expr' =
    mkGeneralizedExpression freeSkelVars annFreeTyVars freeDirtVars tyVs dirtCs
      expr
  in
  (ty', expr')

(* ************************************************************************* *)
(*                         LET-REC-GENERALIZATION                            *)
(* ************************************************************************* *)

let tcTopLevelLet state (exp : Untyped.expression) =
  let exp', outCs = tcExpr state exp in
  let sub, residuals = Unification.solve outCs in
  let exp'' = subInExp sub exp' and ty'' = subInValTy sub exp'.ty in
  generalize residuals ty'' exp''

(* ************************************************************************* *)
(* ************************************************************************* *)

let monomorphize free_ty_params cnstrs =
  let free_cnstrs_params = Constraint.free_params_constraints cnstrs in
  let free_params = Type.FreeParams.union free_ty_params free_cnstrs_params in
  let monomorphize_skeletons =
    List.map
      (fun sk ->
        Constraint.SkelEq (Type.SkelParam sk, Type.SkelBasic Const.FloatTy))
      (Type.SkelParamSet.elements free_params.skel_params)
  and monomorphize_dirts =
    List.map
      (fun d ->
        Constraint.DirtOmega
          ( Type.DirtCoercionParam.fresh (),
            (Type.no_effect_dirt d, Type.empty_dirt) ))
      (Type.DirtParamSet.elements free_params.dirt_params)
  in
  let sub, residuals =
    Unification.solve (monomorphize_skeletons @ monomorphize_dirts @ cnstrs)
  in
  (* After zapping, there should be no more constraints left to solve. *)
  assert (residuals = []);
  sub

let infer_computation state comp =
  let comp', cnstrs = tcComp state comp in
  let sub, residuals = Unification.solve cnstrs in
  (subInCmp sub comp', residuals)

let infer_expression state expr =
  let expr', cnstrs = tcExpr state expr in
  let sub, residuals = Unification.solve cnstrs in
  (subInExp sub expr', residuals)

let infer_rec_abstraction state f abs =
  let abs', cnstrs = infer_let_rec state f abs in
  let sub, residuals = Unification.solve cnstrs in
  (subInAbs sub abs', residuals)

(* Typecheck a top-level expression *)
let top_level_computation state comp =
  let comp, residuals = infer_computation state comp in
  (* Print.debug "TYPE: %t" (Type.print_dirty comp.ty); *)
  (* Print.debug "CONSTRAINTS: %t" (Constraint.print_constraints residuals); *)
  let free_ty_params = Type.free_params_dirty comp.ty in
  let mono_sub = monomorphize free_ty_params residuals in
  (* Print.debug "SUB: %t" (Substitution.print_substitutions mono_sub); *)
  let mono_comp = subInCmp mono_sub comp in
  (* Print.debug "MONO TERM: %t" (Term.print_computation mono_comp); *)
  (* Print.debug "MONO TYPE: %t" (Type.print_dirty mono_comp.ty); *)
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (Type.FreeParams.is_empty (Term.free_params_computation mono_comp));
  mono_comp

let top_level_rec_abstraction state x (abs : Untyped.abstraction) =
  let abs, residuals = infer_rec_abstraction state x abs in
  let free_ty_params = Type.free_params_abstraction_ty abs.ty in
  let mono_sub = monomorphize free_ty_params residuals in
  let mono_abs = subInAbs mono_sub abs in
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (Type.FreeParams.is_empty (Term.free_params_abstraction mono_abs));
  mono_abs

let top_level_expression state expr =
  let expr, residuals = infer_expression state expr in
  (* Print.debug "TERM: %t" (Term.print_expression expr); *)
  (* Print.debug "TYPE: %t" (Type.print_ty expr.ty); *)
  (* Print.debug "CONSTRAINTS: %t" (Constraint.print_constraints residuals); *)
  let free_ty_params = Type.free_params_ty expr.ty in
  let mono_sub = monomorphize free_ty_params residuals in
  (* Print.debug "SUB: %t" (Substitution.print_substitutions mono_sub); *)
  let mono_expr = subInExp mono_sub expr in
  (* Print.debug "MONO TERM: %t" (Term.print_expression mono_expr); *)
  (* Print.debug "MONO TYPE: %t" (Type.print_ty mono_expr.ty); *)
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (Type.FreeParams.is_empty (Term.free_params_expression mono_expr));
  mono_expr

let add_type_definitions state tydefs =
  {
    state with
    tydefs =
      TypeDefinitionContext.extend_type_definitions ~loc:Location.unknown tydefs
        state.tydefs;
  }
