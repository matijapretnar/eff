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
  gblCtxt : TypingEnv.t;
  (* Global Typing Environment *)
  effects : (Type.ty * Type.ty) Term.EffectMap.t;
  (* Valid Effects             *)
  tctx_st : TypeDefinitionContext.state; (* Type definition context *)
}

(* A bag/list of constraints *)
type constraints = Constraint.omega_ct list

(* Add a single term binding to the global typing environment *)
let add_gbl_def env x ty_sch =
  { env with gblCtxt = TypingEnv.update env.gblCtxt x ty_sch }

(* Apply a substitution to the global typing environment *)
let apply_sub_to_gblCtxt env sub =
  { env with gblCtxt = TypingEnv.apply_sub env.gblCtxt sub }

(* Extend the global typing environment with multiple term bindings *)
let extend_env vars env =
  List.fold_right
    (fun (x, ty_sch) env ->
      { env with gblCtxt = TypingEnv.update env.gblCtxt x ty_sch })
    vars env

(* Initial type inference state: everything is empty *)
let initial_state : state =
  {
    gblCtxt = TypingEnv.empty;
    effects = Term.EffectMap.empty;
    tctx_st = TypeDefinitionContext.initial_state;
  }

let add_effect eff (ty1, ty2) st =
  { st with effects = Term.EffectMap.add eff (ty1, ty2) st.effects }

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

let rec mapAndUnzipTcOutputs (f : 'a -> 'b tcOutput) :
    'a list -> 'b list tcOutput = function
  | [] -> ([], [])
  | x :: xs ->
      let y, cs1 = f x in
      let ys, cs2 = mapAndUnzipTcOutputs f xs in
      (y :: ys, cs1 @ cs2)

(* Value typing output *)
type tcExprOutput' = (Term.expression' * Type.ty) tcOutput

type tcExprOutput = Term.expression tcOutput

(* Computation typing output *)
type tcCompOutput' = (Term.computation' * Type.dirty) tcOutput

type tcCompOutput = Term.computation tcOutput

(* Typecheck a list of things *)
let rec tcMany (inState : state) (xss : 'a list) tc =
  match xss with
  | [] -> (([], []), [])
  | x :: xs ->
      let y, cs1 = tc inState x in
      let (ys, tys), cs2 = tcMany inState xs tc in
      ((y :: ys, y.ty :: tys), cs1 @ cs2)

(* ************************************************************************* *)
(*                       PATTERN TYPING (REVISED)                            *)
(* ************************************************************************* *)

(** CHECK the type of a (located) pattern. Return the extended typing
 * environment with the additional term bindings. *)
let rec checkLocatedPatTy st (pat : Untyped.pattern) (patTy : Type.ty) :
    Term.pattern * state =
  checkPatTy st pat.it patTy

(** CHECK the type of a pattern. Return the extended typing environment with
 * the additional term bindings. *)
and checkPatTy (st : state) (pat : Untyped.plain_pattern) (patTy : Type.ty) :
    Term.pattern * state =
  let pat', env = checkPatTy' st pat patTy in
  ({ term = pat'; ty = patTy }, env)

and checkPatTy' (st : state) (pat : Untyped.plain_pattern) (patTy : Type.ty) :
    Term.pattern' * state =
  match pat with
  (* Variable Case *)
  | Untyped.PVar x -> (Term.PVar x, add_gbl_def st x patTy)
  (* Wildcard Case *)
  | Untyped.PNonbinding -> (Term.PNonbinding, st)
  (* Nullary Constructor Case *)
  | Untyped.PVariant (lbl, None) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if ty_in = Type.Tuple [] && patTy = ty_out then
        (Term.PVariant (lbl, Term.pTuple []), st)
      else failwith "checkPatTy: PVariant(None)"
  (* Unary Constructor Case *)
  | Untyped.PVariant (lbl, Some p) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if patTy = ty_out then
        let p', midCtxt = checkLocatedPatTy st p ty_in in
        (Term.PVariant (lbl, p'), midCtxt)
      else failwith "checkPatTy: PVariant(Some)"
  (* Constant Case *)
  | Untyped.PConst c ->
      if patTy = Type.type_const c then (Term.PConst c, st)
      else failwith "checkPatTy: PConst"
  (* Tuple Case *)
  | Untyped.PTuple pats -> (
      match patTy with
      | Type.Tuple tys ->
          let outPats, outCtxt = checkLocatedPatTys st pats tys in
          (Term.PTuple outPats, outCtxt)
      | _ -> failwith "checkPatTy: PTuple")
  (* GEORGE: Not implemented yet cases *)
  | Untyped.PAs _ -> failwith __LOC__
  | Untyped.PRecord _ -> failwith __LOC__
  | Untyped.PAnnotated _ -> failwith __LOC__

and checkLocatedPatTys st (pats : Untyped.pattern list) (patTys : Type.ty list)
    : Term.pattern list * state =
  match (pats, patTys) with
  | [], [] -> ([], st)
  | pat :: pats, ty :: tys ->
      let newPat, st' = checkLocatedPatTy st pat ty in
      let newPats, st'' = checkLocatedPatTys st' pats tys in
      (newPat :: newPats, st'')
  | _, _ -> failwith "checkLocatedPatTys: length mismatch"

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

(* mapAndUnzip :: (a -> (b, c)) -> [a] -> ([b], [c]) *)

let rec optionMapM (f : 'a -> 'b option) : 'a list -> 'b list option = function
  | [] -> Some []
  | x :: xs ->
      Option.bind (f x) (fun y ->
          Option.bind (optionMapM f xs) (fun ys -> Some (y :: ys)))

(* Infer a ground monotype for a pattern, if possible. *)
let rec inferClosedPatTy st : Untyped.plain_pattern -> Type.ty option = function
  | Untyped.PVar _ -> None
  | Untyped.PNonbinding -> None
  | Untyped.PVariant (lbl, None) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if ty_in = Type.Tuple [] && Type.isClosedMonoTy ty_out then (
        assert (Type.isClosedMonoTy ty_out);
        Some ty_out)
      else failwith "inferClosedPatTy: PVariant(None)"
  | Untyped.PVariant (lbl, Some p) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      checkLocatedClosedPatTy st p ty_in;
      assert (Type.isClosedMonoTy ty_out);
      Some ty_out
  | Untyped.PConst c -> Some (Type.type_const c)
  | Untyped.PAs (p, _) -> inferLocatedClosedPatTy st p
  | Untyped.PTuple l ->
      Option.bind
        (optionMapM (inferLocatedClosedPatTy st) l)
        (fun tys -> Some (Type.Tuple tys))
  | Untyped.PRecord _ -> None (* TODO: Not implemented yet *)
  | Untyped.PAnnotated _ -> failwith __LOC__

(* TODO: Not implemented yet *)

(* if Type.isClosedMonoTy ty (* TODO: This is not an elaborated type *)
 *  then checkClosedPatTy p ty
 *  else None
 *)
and inferLocatedClosedPatTy st (inpat : Untyped.pattern) : Type.ty option =
  inferClosedPatTy st inpat.it

and checkLocatedClosedPatTy st (inpat : Untyped.pattern) (patTy : Type.ty) :
    unit =
  checkClosedPatTy st inpat.it patTy

(* Check a pattern against a ground monotype. Fail if not possible. *)
and checkClosedPatTy st (inpat : Untyped.plain_pattern) (patTy : Type.ty) : unit
    =
  match inpat with
  | Untyped.PVar _ -> () (* Always possible *)
  | Untyped.PNonbinding -> () (* Always possible *)
  | Untyped.PVariant (lbl, None) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if ty_in = Type.Tuple [] && patTy = ty_out then ()
      else failwith "checkClosedPatTy: PVariant(None)"
  | Untyped.PVariant (lbl, Some p) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if patTy = ty_out then checkLocatedClosedPatTy st p ty_in
      else failwith "checkClosedPatTy: PVariant(Some)"
  | Untyped.PConst c ->
      if patTy = Type.type_const c then ()
      else failwith "checkClosedPatTy: PConst"
  | Untyped.PAs (p, _v) -> checkLocatedClosedPatTy st p patTy
  | Untyped.PTuple pats -> (
      match patTy with
      | Type.Tuple tys -> List.iter2 (checkLocatedClosedPatTy st) pats tys
      | _ -> failwith "checkClosedPatTy: PTuple")
  | Untyped.PRecord _ -> failwith __LOC__ (* TODO: Not implemented yet *)
  | Untyped.PAnnotated _ -> failwith __LOC__

(* TODO: Not implemented yet *)

let rec inferCheckLocatedClosedPatTys st (pats : Untyped.pattern list) :
    Type.ty option =
  inferCheckClosedPatTys st (List.map (fun p -> p.it) pats)

and inferCheckClosedPatTys st (pats : Untyped.plain_pattern list) :
    Type.ty option =
  let rec filterMap f = function
    | [] -> []
    | x :: xs -> (
        match f x with None -> filterMap f xs | Some y -> y :: filterMap f xs)
  in
  match filterMap (inferClosedPatTy st) pats with
  (* Case 1: We cannot infer a ground type for any of the patterns *)
  | [] -> None
  (* Case 2: We can infer a type for at least a pattern. Verify that all
   * other patterns can be typed against this type and return it *)
  | ty :: _ ->
      List.iter (fun p -> checkClosedPatTy st p ty) pats;
      Some ty

and inferCheckLocatedClosedPatAlts st alts =
  match inferCheckLocatedClosedPatTys st (List.map fst alts) with
  | None ->
      failwith
        "inferCheckLocatedClosedPatAlts: Could not infer the type of the \
         patterns"
  | Some t -> t

(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
let rec tcPattern state (pat : Untyped.pattern) :
    Term.pattern * state * constraints =
  let pat', ty, state', cnstrs = tcPattern' state pat.it in
  ({ term = pat'; ty }, state', cnstrs)

and tcPattern' state :
    Untyped.plain_pattern -> Term.pattern' * Type.ty * state * constraints =
  function
  | Untyped.PVar x ->
      let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
      (Term.PVar x, alpha, add_gbl_def state x alpha, [ alphaSkel ])
  | Untyped.PNonbinding ->
      let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
      (Term.PNonbinding, alpha, state, [ alphaSkel ])
  | Untyped.PConst c -> (Term.PConst c, Type.type_const c, state, [])
  | Untyped.PTuple ps ->
      let fold p (ps', state, cnstrs) =
        let p', state', cnstrs' = tcPattern state p in
        (p' :: ps', state', cnstrs' @ cnstrs)
      in
      let ps', state', cnstrs = List.fold_right fold ps ([], state, []) in
      let p = Term.pTuple ps' in
      (p.term, p.ty, state', cnstrs)
  (* GEORGE: TODO: Unhandled cases *)
  | _other_pattern ->
      failwith "tcPattern: Please no pattern matching in lambda abstractions!"

(* NOTE: We do not really want to return ANY constraints but given the current
 * elaboration strategy we do not want to fail when matching against a literal
 * or unit or something. Feels hacky but one does what one can. *)
let tcLocatedTypedVarPat state (pat : Untyped.pattern) (patTy : Type.ty) :
    Term.pattern * state * constraints =
  let pat, env, cnstrs = tcPattern state pat in
  let _, cnstr = Constraint.fresh_ty_coer (pat.ty, patTy) in
  (pat, env, cnstr :: cnstrs)

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
let lookupTmVar (state : state) x = TypingEnv.lookup state.gblCtxt x

(* Term Variables *)
let rec tcVar (inState : state) (x : Term.variable) : tcExprOutput' =
  match lookupTmVar inState x with
  | Some scheme ->
      let x, x_monotype, constraints = instantiateVariable x scheme in
      ((x.term, x_monotype), constraints)
  | None -> assert false

(* Constants *)
and tcConst (_inState : state) (c : Const.t) : tcExprOutput' =
  ((Term.Const c, Type.type_const c), [])

(* Type-annotated Expressions *)
and tcAnnotated (_inState : state)
    ((_e, _ty) : Untyped.expression * Language.Type.ty) : tcExprOutput' =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* Tuples *)
and tcTuple (inState : state) (es : Untyped.expression list) : tcExprOutput' =
  let (es, tys), cs = tcMany inState es tcExpr in
  ((Term.Tuple es, Type.Tuple tys), cs)

(* Records *)
and tcRecord (_inState : state) (_lst : (field, Untyped.expression) Assoc.t) :
    tcExprOutput' =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* Variants *)
and tcVariant (inState : state) ((lbl, mbe) : label * Untyped.expression option)
    : tcExprOutput' =
  let ty_in, ty_out = Type.constructor_signature inState.tctx_st lbl in
  match mbe with
  | None -> ((Term.Variant (lbl, Term.tuple []), ty_out), [])
  | Some e ->
      let e', cs1 = tcExpr inState e in
      (* GEORGE: Investigate how cast_expression works *)
      let castExp, castCt = Term.cast_expression e' ty_in in
      ((Term.Variant (lbl, castExp), ty_out), castCt :: cs1)

and tcAbstraction state (pat, cmp) =
  let pat', state', cnstrs1 = tcPattern state pat in
  let cmp', cnstrs2 = tcComp state' cmp in
  (Term.abstraction (pat', cmp'), cnstrs1 @ cnstrs2)

(* Lambda Abstractions *)
and tcLambda state abs =
  let abs', cnstrs = tcAbstraction state abs in
  ((Term.Lambda abs', Type.Arrow abs'.ty), cnstrs)

(* Effects (GEORGE: Isn't this supposed to be in computations? *)
and tcEffect (inState : state) (eff : Untyped.effect) : tcExprOutput' =
  (* GEORGE: NOTE: This is verbatim copied from the previous implementation *)
  let in_ty, out_ty = Term.EffectMap.find eff inState.effects in
  let s = Type.EffectSet.singleton eff in
  let outVal = Term.Effect (eff, (in_ty, out_ty)) in
  let outType = Type.Arrow (in_ty, (out_ty, Type.closed_dirt s)) in
  ((outVal, outType), [])

(* Handlers(Return Case) *)
and tcReturnCase (inState : state) (abs : Untyped.abstraction)
    (* Return clause *) (tyIn : Type.ty)
    (* Expected input value type *) (drtyOut : Type.dirty) =
  (* Expected output dirt *)

  (* 1: Typecheck the pattern and the body of the return clause *)
  let abs, cs1 = tcAbstraction inState abs in

  (* 2: Make sure that the pattern is a variable one.
   *    We do not support anything else at the moment *)
  let x, pat, cmp =
    match abs.term with
    | ({ term = PVar x; _ } as pat), cmp -> (x, pat, cmp)
    | _ -> failwith "tcReturnCase: only varpats allowed"
  in

  (* 3: Generate all wanted constraints *)
  let omega12, omegaCt12 = Constraint.fresh_dirty_coer (cmp.ty, drtyOut) in

  (* 4: Create the elaborated clause *)
  let yvar = CoreTypes.Variable.fresh "y" in
  let castY, omegaCt6 = Term.cast_expression (Term.var yvar tyIn) pat.ty in
  let ysub = Term.subst_comp (Assoc.of_list [ (x, castY) ]) in
  let outExpr =
    Term.abstraction (Term.pVar yvar pat.ty, Term.castComp (ysub cmp, omega12))
  in

  (* 5: Combine the results *)
  (outExpr, omegaCt12 @ (omegaCt6 :: cs1))

(* NOTE: (a_r : skel_r) \in cs1 *)

(* Handlers(Op Cases) *)
and tcOpCases (inState : state)
    (eclauses : (Untyped.effect, Untyped.abstraction2) Assoc.t)
    (dirtyOut : Type.dirty) : (Term.effect, Term.abstraction2) Assoc.t tcOutput
    =
  let rec go cs =
    match Assoc.to_list cs with
    | [] -> ([], [])
    | c :: cs ->
        let y, cs1 = tcOpCase inState c dirtyOut in
        let ys, cs2 = go (Assoc.of_list cs) in
        (y :: ys, cs1 @ cs2)
  in
  let allClauses, allCs = go eclauses in
  (Assoc.of_list allClauses, allCs)

(* Handlers(Op Case) *)
and tcOpCase (inState : state)
    ((eff, abs2) : Untyped.effect * Untyped.abstraction2) (* Op clause *)
    (dirtyOut : Type.dirty) (* Expected output type *) =
  (* 1: Lookup the type of Opi *)
  let tyAi, tyBi = Term.EffectMap.find eff inState.effects in

  (* 2: Generate fresh variables for the type of the codomain of the continuation *)
  let dirtyi, alphaiSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 3: Typecheck the clause *)
  let ((xop, kop, trgCop), (_, _, (tyBOpi, dirtDOpi))), csi
      (* GEORGE: I don't like the unused types *) =
    tcTypedAbstraction2 inState abs2 tyAi (Type.Arrow (tyBi, dirtyi))
  in

  (* 4: Make sure that the pattern for k is a variable one.
   *    We do not support anything else at the moment *)
  let k =
    match kop with
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
      (xop, Term.pVar lvar leftty, Term.castComp (lsub trgCop, omega34i)) )
  in

  (* 7: Combine the results *)
  let outCs = (alphaiSkel :: omegaCt34i) @ (omegaCt5i :: csi) in
  (outExpr, outCs)

(* Handlers *)
and tcHandler (inState : state) (h : Untyped.handler) : tcExprOutput' =
  (* 1: Generate fresh variables for the input and output types *)
  let ((alphaIn, deltaIn) as dirtyIn), alphaInSkel =
    Constraint.fresh_dirty_with_fresh_skel ()
  in
  let ((_, deltaOut) as dirtyOut), alphaOutSkel =
    Constraint.fresh_dirty_with_fresh_skel ()
  in

  (* 2: Process the return and the operation clauses *)
  let trgRet, cs1 = tcReturnCase inState h.value_clause alphaIn dirtyOut in
  let trgCls, cs2 = tcOpCases inState h.effect_clauses dirtyOut in

  (* 3: Create the omega7 coercion (cast the whole handler) *)
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
      ( Constraint.bangCoercion (Constraint.reflTy alphaIn, omega7),
        Constraint.reflDirty dirtyOut )
  in
  let handTy, _ = handlerCo.ty in
  match handTy with
  | Type.Handler (inTy, outTy) ->
      let outExpr =
        Term.CastExp
          ( {
              term =
                Term.Handler
                  {
                    term = { effect_clauses = trgCls; value_clause = trgRet };
                    ty = (inTy, outTy);
                  };
              ty = handTy;
            },
            handlerCo )
      in
      let outType = Type.Handler (dirtyIn, dirtyOut) in
      let outCs = (omegaCt7 :: alphaInSkel :: alphaOutSkel :: cs1) @ cs2 in
      (* 7, ain : skelin, aout : skelout && 1, 2, 6 && 3i, 4i, 5i *)
      ((outExpr, outType), outCs)
  | _ -> assert false

(* Dispatch: Type inference for a plain value (expression) *)
and tcExpr' (inState : state) : Untyped.plain_expression -> tcExprOutput' =
  function
  | Untyped.Var x -> tcVar inState x
  | Untyped.Const c -> tcConst inState c
  | Untyped.Annotated (e, ty) -> tcAnnotated inState (e, ty)
  | Untyped.Tuple es -> tcTuple inState es
  | Untyped.Record lst -> tcRecord inState lst
  | Untyped.Variant (lbl, mbe) -> tcVariant inState (lbl, mbe)
  | Untyped.Lambda abs -> tcLambda inState abs
  | Untyped.Effect eff -> tcEffect inState eff
  | Untyped.Handler hand -> tcHandler inState hand

(* Type inference for a located value (expression) *)
and tcExpr (inState : state) (e : Untyped.expression) : tcExprOutput =
  let (trm, ty), cnstrs = tcExpr' inState e.it in
  ({ term = trm; ty }, cnstrs)

(* ************************************************************************* *)
(*                          COMPUTATION TYPING                               *)
(* ************************************************************************* *)

(* Dispatch: Type inference for a plan computation *)
and tcComp' (inState : state) : Untyped.plain_computation -> tcCompOutput' =
  function
  | Value exp -> tcValue inState exp
  (* Nest a list of let-bindings *)
  | Let ([], c2) ->
      let c, cnstrs = tcComp inState c2 in
      ((c.term, c.ty), cnstrs)
  | Let ([ (pat, c1) ], c2) -> tcLet inState pat c1 c2
  | Let ((pat, c1) :: rest, c2) ->
      let subCmp = { it = Untyped.Let (rest, c2); at = c2.at } in
      tcComp' inState (Untyped.Let ([ (pat, c1) ], subCmp))
  (* Nest a list of letrec-bindings; MUTUAL RECURSION NOT ALLOWED AT THE MOMENT *)
  | LetRec ([], c2) ->
      let c, cnstrs = tcComp inState c2 in
      ((c.term, c.ty), cnstrs)
  | LetRec ([ (var, abs) ], c2) -> tcLetRecNoGen inState var abs c2
  | LetRec ((var, abs) :: rest, c2) ->
      let subCmp = { it = Untyped.LetRec (rest, c2); at = c2.at } in
      tcComp' inState (Untyped.LetRec ([ (var, abs) ], subCmp))
  (* Pattern Matching: Special Case 2: Variable-binding *)
  | Match (scr, [ (p, c) ]) when isLocatedVarPat p ->
      tcComp' inState
        (Untyped.Let ([ (p, { it = Untyped.Value scr; at = p.at }) ], c))
  (* Pattern Matching: General Case: Monomorphic patterns *)
  | Match (scr, cases) -> tcMatch inState scr cases
  | Apply (val1, val2) -> tcApply inState val1 val2
  | Handle (hand, cmp) -> tcHandle inState hand cmp
  | Check cmp -> tcCheck inState cmp

(* Type inference for a located computation *)
and tcComp (inState : state) (c : Untyped.computation) : tcCompOutput =
  let (trm, ty), cnstrs = tcComp' inState c.it in
  ({ term = trm; ty }, cnstrs)

(* Typecheck a value wrapped in a return *)
and tcValue (inState : state) (exp : Untyped.expression) : tcCompOutput' =
  let outExpr, outCs = tcExpr inState exp in
  ((Term.Value outExpr, (outExpr.ty, Type.empty_dirt)), outCs)

(* Typecheck a let where c1 is a value *)
and tcLetValNoGen (inState : state) (patIn : Untyped.pattern)
    (e1 : Untyped.expression) (c2 : Untyped.computation) : tcCompOutput' =
  (* 1: Typecheck e1 *)
  let trgE1, cs1 = tcExpr inState e1 in

  (* (v',A, Qv, Sigma1) *)

  (* 2: Typecheck c2 *)
  let x =
    match patIn.it with
    | Untyped.PVar x -> x (* GEORGE: Support nothing else at the moment *)
    | _ -> failwith "tcLetValNoGen: only varpats allowed"
  in
  let trgC2, cs2 = tcComp (add_gbl_def inState x trgE1.ty) c2 in

  (* 3: Combine the results *)
  let outExpr =
    Term.LetVal (trgE1, Term.abstraction (Term.pVar x trgE1.ty, trgC2))
  in
  let outCs = cs1 @ cs2 in
  ((outExpr, trgC2.ty), outCs)

(* Typecheck a let when c1 is a computation (== do binding) *)
and tcLetCmp (inState : state) (pat : Untyped.pattern)
    (c1 : Untyped.computation) (c2 : Untyped.computation) : tcCompOutput' =
  (* 1: Typecheck c1, the pattern, and c2 *)
  let trgC1, cs1 = tcComp inState c1 in
  let tyA1, dirtD1 = trgC1.ty in
  let trgPat, midState, hack = tcLocatedTypedVarPat inState pat tyA1 in
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
  let outCs = hack @ (omegaCt1 :: omegaCt2 :: cs1) @ cs2 in

  ((outExpr, outType), outCs)

(* Typecheck a non-recursive let *)
and tcLet (inState : state) (pdef : Untyped.pattern) (c1 : Untyped.computation)
    (c2 : Untyped.computation) : tcCompOutput' =
  match c1.it with
  | Untyped.Value e1 -> tcLetValNoGen inState pdef e1 c2
  | _other_computation -> tcLetCmp inState pdef c1 c2

(* Typecheck a (potentially) recursive let *)
and tcLetRecNoGen (inState : state) (var : Untyped.variable)
    (abs : Untyped.abstraction) (c2 : Untyped.computation) : tcCompOutput' =
  (* 1: Generate fresh variables for everything *)
  let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let betadelta, betaSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Typecheck the abstraction *)
  let ((trgPat, trgC1), (_trgPatTy, dirty1)), cs1 =
    tcTypedAbstraction
      (add_gbl_def inState var (Type.Arrow (alpha, betadelta)))
      abs alpha
  in

  (* 3: Typecheck c2 *)
  let trgC2, cs2 =
    tcComp (add_gbl_def inState var (Type.Arrow (alpha, dirty1))) c2
  in

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

  (* 5: Combine the results *)
  let outExpr =
    Term.LetRec ([ (var, Term.abstraction (trgPat, c1'')) ], trgC2)
  in

  let outCs = ((alphaSkel :: betaSkel :: omegaCt12) @ cs1) @ cs2 in
  ((outExpr, trgC2.ty), outCs)

(* Typecheck a case expression *)
and tcMatch (inState : state) (scr : Untyped.expression)
    (alts : Untyped.abstraction list) : tcCompOutput' =
  if List.length alts > 0 then tcNonEmptyMatch inState scr alts
  else tcEmptyMatch inState scr

(* Typecheck a non-empty case expression *)
and tcNonEmptyMatch (inState : state) (scr : Untyped.expression)
    (alts : Untyped.abstraction list) : tcCompOutput' =
  (* 0: Make sure that we have at least one alternative *)
  assert (List.length alts > 0);

  (* 1: Generate fresh variables for the result *)
  let dirtyOut, alphaOutSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Infer a type for the patterns *)
  let patTy = inferCheckLocatedClosedPatAlts inState alts in

  (* 4: Typecheck the scrutinee and the alternatives *)
  let trgScr, cs1 = tcExpr inState scr in
  let trgAlts, cs2 =
    mapAndUnzipTcOutputs
      (fun alt -> tcAlternative inState patTy alt dirtyOut)
      alts
  in

  (* 5: Generate the coercion for casting the scrutinee *)
  (* NOTE: The others should be already included in 'altRes' *)
  let matchExp, omegaCtScr = Term.cast_expression trgScr patTy in

  (* 6: Combine the results *)
  let outExpr = Term.Match (matchExp, trgAlts) in
  let outCs = (alphaOutSkel :: omegaCtScr :: cs1) @ cs2 in
  ((outExpr, dirtyOut), outCs)

(* Typecheck an empty case expression *)
and tcEmptyMatch (inState : state) (scr : Untyped.expression) : tcCompOutput' =
  (* 1: Generate fresh variables for the result *)
  let dirtyOut, alphaOutSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Typecheck the scrutinee *)
  let trgScr, cs1 = tcExpr inState scr in

  (* 3: Combine the results *)
  let outExpr = Term.Match (trgScr, []) in
  let outCs = alphaOutSkel :: cs1 in
  ((outExpr, dirtyOut), outCs)

(* Typecheck a function application *)
and tcApply (inState : state) (val1 : Untyped.expression)
    (val2 : Untyped.expression) : tcCompOutput' =
  (* Infer the types of val1 and val2 *)
  let trgVal1, cs1 = tcExpr inState val1 in
  let trgVal2, cs2 = tcExpr inState val2 in

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
and tcHandle (inState : state) (hand : Untyped.expression)
    (cmp : Untyped.computation) : tcCompOutput' =
  (* Typecheck the handler and the computation *)
  let trgHand, cs1 = tcExpr inState hand in
  (* Typecheck the handler *)
  let trgCmp, cs2 = tcComp inState cmp in

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
and tcCheck (_inState : state) (_cmp : Untyped.computation) : tcCompOutput' =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* ************************************************************************* *)
(*                               UTILITIES                                   *)
(* ************************************************************************* *)

(* Given the expected type of the pattern and the expected result type,
 * typecheck a single case alternative. *)
and tcAlternative (inState : state)
    (patTy : Type.ty) (* Expected pattern type *)
    ((pat, cmp) : Untyped.abstraction) (* Case alternative *)
    ((tyAout, dirtDout) : Type.dirty) : Term.abstraction tcOutput =
  (* Expected output type *)

  (* Typecheck the pattern and the right-hand side *)
  let trgPat, midCtxt = checkLocatedPatTy inState pat patTy in
  let trgCmp, cs = tcComp midCtxt cmp in
  (* Generate coercions to cast the RHS *)
  let castCmp, omegaCtLR = Term.cast_computation trgCmp (tyAout, dirtDout) in
  (* Combine the results *)
  let outExpr = Term.abstraction (trgPat, castCmp) in
  let outCs = omegaCtLR @ cs in
  (outExpr, outCs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and tcTypedAbstraction (inState : state) (pat, cmp) patTy =
  let trgPat, midLclCtx, hack = tcLocatedTypedVarPat inState pat patTy in
  let trgCmp, cs = tcComp midLclCtx cmp in
  (((trgPat, trgCmp), (patTy, trgCmp.ty)), hack @ cs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and tcTypedAbstraction2 (inState : state) (pat1, pat2, cmp) patTy1 patTy2 =
  let trgPat1, midCtx1, hack1 = tcLocatedTypedVarPat inState pat1 patTy1 in
  let trgPat2, midCtx2, hack2 = tcLocatedTypedVarPat midCtx1 pat2 patTy2 in
  let trgCmp, cs = tcComp midCtx2 cmp in
  ( ((trgPat1, trgPat2.term, trgCmp), (patTy1, patTy2, trgCmp.ty)),
    hack1 @ hack2 @ cs )

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

let tcTopLevelLet (inState : state) (exp : Untyped.expression) =
  let exp', outCs = tcExpr inState exp in
  let sub, residuals = Unification.solve outCs in
  let exp'' = subInExp sub exp' and ty'' = subInValTy sub exp'.ty in
  generalize residuals ty'' exp''

(* This is currently unused, top lets are translated into local lets *)
let tcTopLetRec (inState : state) (var : Untyped.variable)
    (pat : Untyped.pattern) (cmp : Untyped.computation) =
  (* 1: Generate fresh variables for everything *)
  let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let betadelta, betaSkel = Constraint.fresh_dirty_with_fresh_skel () in

  (* 2: Typecheck the abstraction *)
  let ((trgPat, trgC1), (trgPatTy, dirty1)), cs =
    tcTypedAbstraction
      (add_gbl_def inState var (Type.Arrow (alpha, betadelta)))
      (pat, cmp) alpha
  in

  (* 3: The assumed type should be at least as general as the inferred one *)
  let omega12, omegaCt12 = Constraint.fresh_dirty_coer (dirty1, betadelta) in

  (* 4: Create the (complicated) c1''. *)
  let c1'' =
    let f_coercion =
      Constraint.arrowCoercion (Constraint.reflTy alpha, omega12)
    in
    Term.subst_comp
      (Assoc.of_list
         [
           ( var,
             Term.castExp (Term.var var (Type.Arrow (alpha, dirty1)), f_coercion)
           );
         ])
      trgC1
  in

  (* 5: Solve (simplify, actually) the generated constraints *)
  let subst, residuals =
    Unification.solve ((alphaSkel :: betaSkel :: omegaCt12) @ cs)
  in

  (* 6: Substitute back into everything *)
  let trgPatTy = subInValTy subst trgPatTy in
  let dirty1 = subInCmpTy subst dirty1 in
  (* trgPat needs not a substitution *)
  let trgC1 = subInCmp subst c1'' in

  (* 7: Partition the residual constraints and abstract over them *)
  let outTy, _ =
    generalize residuals (Type.Arrow (trgPatTy, dirty1)) (Term.tuple [])
  (* Matija: Make sure to generalize the expression as well *)
  and outExpr = ([ (var, trgPatTy, dirty1, (trgPat, c1'')) ], trgC1) in
  (outExpr, outTy)

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
  match
    tcLetRecNoGen state f abs
      (unlocated @@ Untyped.Value (unlocated @@ Untyped.Tuple []))
  with
  | (Term.LetRec ([ (_f, abs') ], _ret_unit), _unit_drty), cnstrs ->
      (* These two are not necessarily equal, but should be unifiable *)
      let sub, residuals = Unification.solve cnstrs in
      (subInAbs sub abs', residuals)
  | _ -> assert false

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

(* Add an external binding to the typing environment *)
let addExternal ctx x ty =
  { ctx with gblCtxt = TypingEnv.update ctx.gblCtxt x ty }

let add_type ctx x ty = { ctx with gblCtxt = TypingEnv.update ctx.gblCtxt x ty }

let add_type_definitions state tydefs =
  {
    state with
    tctx_st =
      TypeDefinitionContext.extend_type_definitions ~loc:Location.unknown tydefs
        state.tctx_st;
  }
