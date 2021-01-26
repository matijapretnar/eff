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

(* [READER] LOCAL ENVIRONMENT *)

let initial_lcl_ty_env = TypingEnv.empty

(* Add a single term binding to the local typing environment *)
let extendLclCtxt env x scheme = TypingEnv.update env x scheme

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
  let ty1 = Type.source_to_target st.tctx_st ty1 in
  let ty2 = Type.source_to_target st.tctx_st ty2 in
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

let subInAbs sub abs =
  Substitution.apply_substitutions_to_typed_abstraction sub abs

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
  foldLeft (fun e c -> Term.ApplyTyCoercion (e, c)) tyCoercions
  |> (* 2: Apply to the dirt coercions *)
  foldLeft (fun e c -> Term.ApplyDirtCoercion (e, c)) dirtCoercions

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
  let targetX = applyTerm tyOmegas dirtOmegas (Term.Var x) in

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
type tcExprOutput = (Term.expression * Type.ty) tcOutput

(* Computation typing output *)
type tcCompOutput = (Term.computation * Type.dirty) tcOutput

(* Typecheck a list of things *)
let rec tcMany (inState : state) (lclCtxt : TypingEnv.t) (xss : 'a list)
    (tc : state -> TypingEnv.t -> 'a -> ('b * 'c) tcOutput) :
    ('b list * 'c list) tcOutput =
  match xss with
  | [] -> (([], []), [])
  | x :: xs ->
      let (y, ty), cs1 = tc inState lclCtxt x in
      let (ys, tys), cs2 = tcMany inState lclCtxt xs tc in
      ((y :: ys, ty :: tys), cs1 @ cs2)

(* ************************************************************************* *)
(*                       PATTERN TYPING (REVISED)                            *)
(* ************************************************************************* *)

(** CHECK the type of a (located) pattern. Return the extended typing
 * environment with the additional term bindings. *)
let rec checkLocatedPatTy st (lclCtxt : TypingEnv.t) (pat : Untyped.pattern)
    (patTy : Type.ty) : Term.pattern * TypingEnv.t =
  checkPatTy st lclCtxt pat.it patTy

(** CHECK the type of a pattern. Return the extended typing environment with
 * the additional term bindings. *)
and checkPatTy (st : state) (lclCtxt : TypingEnv.t)
    (pat : Untyped.plain_pattern) (patTy : Type.ty) :
    Term.pattern * TypingEnv.t =
  match pat with
  (* Variable Case *)
  | Untyped.PVar x -> (Term.PVar x, extendLclCtxt lclCtxt x patTy)
  (* Wildcard Case *)
  | Untyped.PNonbinding -> (Term.PNonbinding, lclCtxt)
  (* Nullary Constructor Case *)
  | Untyped.PVariant (lbl, None) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if ty_in = Type.Tuple [] && patTy = ty_out then
        (Term.PVariant (lbl, Term.PTuple []), lclCtxt)
      else failwith "checkPatTy: PVariant(None)"
  (* Unary Constructor Case *)
  | Untyped.PVariant (lbl, Some p) ->
      let ty_in, ty_out = Type.constructor_signature st.tctx_st lbl in
      if patTy = ty_out then
        let p', midCtxt = checkLocatedPatTy st lclCtxt p ty_in in
        (Term.PVariant (lbl, p'), midCtxt)
      else failwith "checkPatTy: PVariant(Some)"
  (* Constant Case *)
  | Untyped.PConst c ->
      if patTy = Type.type_const c then (Term.PConst c, lclCtxt)
      else failwith "checkPatTy: PConst"
  (* Tuple Case *)
  | Untyped.PTuple pats -> (
      match patTy with
      | Type.Tuple tys ->
          let outPats, outCtxt = checkLocatedPatTys st lclCtxt pats tys in
          (Term.PTuple outPats, outCtxt)
      | _ -> failwith "checkPatTy: PTuple")
  (* GEORGE: Not implemented yet cases *)
  | Untyped.PAs _ -> failwith __LOC__
  | Untyped.PRecord _ -> failwith __LOC__
  | Untyped.PAnnotated _ -> failwith __LOC__

and checkLocatedPatTys st (lclCtxt : TypingEnv.t) (pats : Untyped.pattern list)
    (patTys : Type.ty list) : Term.pattern list * TypingEnv.t =
  match (pats, patTys) with
  | [], [] -> ([], lclCtxt)
  | pat :: pats, ty :: tys ->
      let newPat, newCtxt = checkLocatedPatTy st lclCtxt pat ty in
      let newPats, outCtxt = checkLocatedPatTys st newCtxt pats tys in
      (newPat :: newPats, outCtxt)
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
let rec inferClosedPatTy st : Untyped.plain_pattern -> Type.ty option =
  function
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
and inferLocatedClosedPatTy st (inpat : Untyped.pattern) : Type.ty option
    =
  inferClosedPatTy st inpat.it

and checkLocatedClosedPatTy st (inpat : Untyped.pattern)
    (patTy : Type.ty) : unit =
  checkClosedPatTy st inpat.it patTy

(* Check a pattern against a ground monotype. Fail if not possible. *)
and checkClosedPatTy st (inpat : Untyped.plain_pattern) (patTy : Type.ty)
    : unit =
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
let rec tcUntypedVarPat (lclCtxt : TypingEnv.t) :
    Untyped.plain_pattern ->
    Term.pattern * Type.ty * TypingEnv.t * constraints = function
  | Untyped.PVar x ->
      let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
      (Term.PVar x, alpha, extendLclCtxt lclCtxt x alpha, [ alphaSkel ])
  | Untyped.PNonbinding ->
      let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
      (Term.PNonbinding, alpha, lclCtxt, [ alphaSkel ])
  | Untyped.PConst c -> (Term.PConst c, Type.type_const c, lclCtxt, [])
  | Untyped.PTuple ps ->
      let fold p (ps', tys, lclCtxt, cnstrs) =
        let p', ty, lclCtxt', cnstrs' = tcUntypedVarPat lclCtxt p.it in
        (p' :: ps', ty :: tys, lclCtxt', cnstrs' @ cnstrs)
      in
      let ps', tys', lclCtxt', cnstrs =
        List.fold_right fold ps ([], [], lclCtxt, [])
      in
      (Term.PTuple ps', Type.Tuple tys', lclCtxt', cnstrs)
  (* GEORGE: TODO: Unhandled cases *)
  | _other_pattern ->
      failwith
        "tcUntypedVarPat: Please no pattern matching in lambda abstractions!"

let tcLocatedUntypedVarPat (lclCtxt : TypingEnv.t) (pat : Untyped.pattern) :
    Term.pattern * Type.ty * TypingEnv.t * constraints =
  tcUntypedVarPat lclCtxt pat.it

(* NOTE: We do not really want to return ANY constraints but given the current
 * elaboration strategy we do not want to fail when matching against a literal
 * or unit or something. Feels hacky but one does what one can. *)
let tcTypedVarPat (lclCtxt : TypingEnv.t) (pat : Untyped.plain_pattern)
    (patTy : Type.ty) : Term.pattern * TypingEnv.t * constraints =
  match pat with
  | Untyped.PVar x -> (Term.PVar x, extendLclCtxt lclCtxt x patTy, [])
  | Untyped.PNonbinding -> (Term.PNonbinding, lclCtxt, [])
  | Untyped.PConst c ->
      let _, omegaCt = Constraint.fresh_ty_coer (patTy, Type.type_const c) in
      (Term.PConst c, lclCtxt, [ omegaCt ])
  | Untyped.PTuple [] ->
      let _, omegaCt = Constraint.fresh_ty_coer (patTy, Type.Tuple []) in
      (Term.PTuple [], lclCtxt, [ omegaCt ])
  (* Do not worry about the coercion variable not being used in this case;
   * the shape of the constraint will turn this into unification *)
  (* GEORGE: TODO: Unhandled cases *)
  | _other_pattern ->
      failwith
        "tcTypedVarPat: Please no pattern matching in lambda abstractions!"

(* NOTE: We do not really want to return ANY constraints but given the current
 * elaboration strategy we do not want to fail when matching against a literal
 * or unit or something. Feels hacky but one does what one can. *)
let tcLocatedTypedVarPat (lclCtxt : TypingEnv.t) (pat : Untyped.pattern)
    (patTy : Type.ty) : Term.pattern * TypingEnv.t * constraints =
  tcTypedVarPat lclCtxt pat.it patTy

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
let lookupTmVar (inState : state) (lclCtxt : TypingEnv.t) x =
  match TypingEnv.lookup lclCtxt x with
  | Some scheme -> Some scheme
  | None -> (
      match TypingEnv.lookup inState.gblCtxt x with
      | Some scheme -> Some scheme
      | None -> None)

(* Term Variables *)
let rec tcVar (inState : state) (lclCtxt : TypingEnv.t) (x : Term.variable) :
    tcExprOutput =
  match lookupTmVar inState lclCtxt x with
  | Some scheme ->
      let x, x_monotype, constraints = instantiateVariable x scheme in
      ((x, x_monotype), constraints)
  | None -> assert false

(* Constants *)
and tcConst (_inState : state) (_lclCtxt : TypingEnv.t) (c : Const.t) :
    tcExprOutput =
  ((Term.Const c, Type.type_const c), [])

(* Type-annotated Expressions *)
and tcAnnotated (_inState : state) (_lclCtxt : TypingEnv.t)
    ((_e, _ty) : Untyped.expression * Language.Type.ty) : tcExprOutput =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* Tuples *)
and tcTuple (inState : state) (lclCtxt : TypingEnv.t)
    (es : Untyped.expression list) : tcExprOutput =
  let (es, tys), cs = tcMany inState lclCtxt es tcExpr in
  ((Term.Tuple es, Type.Tuple tys), cs)

(* Records *)
and tcRecord (_inState : state) (_lclCtx : TypingEnv.t)
    (_lst : (field, Untyped.expression) Assoc.t) : tcExprOutput =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* Variants *)
and tcVariant (inState : state) (lclCtx : TypingEnv.t)
    ((lbl, mbe) : label * Untyped.expression option) : tcExprOutput =
  let ty_in, ty_out = Type.constructor_signature inState.tctx_st lbl in
  match mbe with
  | None -> ((Term.Variant (lbl, Term.Tuple []), ty_out), [])
  | Some e ->
      let (e', ety), cs1 = tcExpr inState lclCtx e in
      (* GEORGE: Investigate how cast_expression works *)
      let castExp, castCt = Term.cast_expression e' ety ty_in in
      ((Term.Variant (lbl, castExp), ty_out), castCt :: cs1)

(* Lambda Abstractions *)
and tcLambda (inState : state) (lclCtx : TypingEnv.t)
    ((pat, cmp) : Untyped.abstraction) : tcExprOutput =
  let trgPat, patTy, midCtx, cs1 = tcLocatedUntypedVarPat lclCtx pat in
  let (trgCmp, cmpTy), cs2 = tcComp inState midCtx cmp in
  let outVal = Term.Lambda (Term.abstraction_with_ty trgPat patTy trgCmp) in
  let outType = Type.Arrow (patTy, cmpTy) in
  ((outVal, outType), cs1 @ cs2)

(* Effects (GEORGE: Isn't this supposed to be in computations? *)
and tcEffect (inState : state) (_lclCtx : TypingEnv.t) (eff : Untyped.effect) :
    tcExprOutput =
  (* GEORGE: NOTE: This is verbatim copied from the previous implementation *)
  let in_ty, out_ty = Term.EffectMap.find eff inState.effects in
  let s = Type.EffectSet.singleton eff in
  let outVal = Term.Effect (eff, (in_ty, out_ty)) in
  let outType = Type.Arrow (in_ty, (out_ty, Type.closed_dirt s)) in
  ((outVal, outType), [])

(* Handlers(Return Case) *)
and tcReturnCase (inState : state) (lclCtx : TypingEnv.t)
    ((pat, cmp) : Untyped.abstraction) (* Return clause *)
    (tyIn : Type.ty) (* Expected input value type *)
    (tyOut : Type.ty) (* Expected output value type *)
    (dirtOut : Type.dirt) : Term.abstraction_with_ty tcOutput =
  (* Expected output dirt *)

  (* 1: Typecheck the pattern and the body of the return clause *)
  let trgPat, patTy, midCtx, cs1 = tcLocatedUntypedVarPat lclCtx pat in
  let (trgCmp, (tyB, dirtD)), cs2 = tcComp inState midCtx cmp in

  (* 2: Make sure that the pattern is a variable one.
   *    We do not support anything else at the moment *)
  let x =
    match trgPat with
    | PVar x -> x
    | _ -> failwith "tcReturnCase: only varpats allowed"
  in

  (* 3: Generate all wanted constraints *)
  let omega1, omegaCt1 = Constraint.fresh_ty_coer (tyB, tyOut) in
  let omega2, omegaCt2 = Constraint.fresh_dirt_coer (dirtD, dirtOut) in
  let omega6, omegaCt6 = Constraint.fresh_ty_coer (tyIn, patTy) in

  (* 4: Create the elaborated clause *)
  let yvar = CoreTypes.Variable.fresh "y" in
  let ysub =
    Term.subst_comp (Assoc.of_list [ (x, Term.CastExp (Var yvar, omega6)) ])
  in
  let outExpr =
    ( Term.PVar yvar,
      patTy,
      Term.CastComp (ysub trgCmp, Constraint.BangCoercion (omega1, omega2)) )
  in

  (* 5: Combine the results *)
  (outExpr, (omegaCt1 :: omegaCt2 :: omegaCt6 :: cs1) @ cs2)

(* NOTE: (a_r : skel_r) \in cs1 *)

(* Handlers(Op Cases) *)
and tcOpCases (inState : state) (lclCtx : TypingEnv.t)
    (eclauses : (Untyped.effect, Untyped.abstraction2) Assoc.t)
    (tyOut : Type.ty) (dirtOut : Type.dirt) :
    (Term.effect, Term.abstraction2) Assoc.t tcOutput =
  let rec go cs =
    match Assoc.to_list cs with
    | [] -> ([], [])
    | c :: cs ->
        let y, cs1 = tcOpCase inState lclCtx c tyOut dirtOut in
        let ys, cs2 = go (Assoc.of_list cs) in
        (y :: ys, cs1 @ cs2)
  in
  let allClauses, allCs = go eclauses in
  (Assoc.of_list allClauses, allCs)

(* Handlers(Op Case) *)
and tcOpCase (inState : state) (lclCtx : TypingEnv.t)
    ((eff, abs2) : Untyped.effect * Untyped.abstraction2) (* Op clause *)
    (tyOut : Type.ty) (* Expected output value type *)
    (dirtOut : Type.dirt) : (Term.effect * Term.abstraction2) tcOutput =
  (* Expected output dirt *)

  (* 1: Lookup the type of Opi *)
  let tyAi, tyBi = Term.EffectMap.find eff inState.effects in

  (* 2: Generate fresh variables for the type of the codomain of the continuation *)
  let alphai, alphaiSkel = Constraint.fresh_ty_with_fresh_skel () in
  let deltai = Type.fresh_dirt () in

  (* 3: Typecheck the clause *)
  let ((xop, kop, trgCop), (_, _, (tyBOpi, dirtDOpi))), csi
      (* GEORGE: I don't like the unused types *) =
    tcTypedAbstraction2 inState lclCtx abs2 tyAi
      (Type.Arrow (tyBi, (alphai, deltai)))
  in

  (* 4: Make sure that the pattern for k is a variable one.
   *    We do not support anything else at the moment *)
  let k =
    match kop with
    | Term.PVar k -> k
    | _ -> failwith "tcOpCase: only varpats allowed"
  in

  (* 5: Generate all the needed constraints *)
  let omega3i, omegaCt3i = Constraint.fresh_ty_coer (tyBOpi, tyOut) in
  let omega4i, omegaCt4i = Constraint.fresh_dirt_coer (dirtDOpi, dirtOut) in
  let omega5i, omegaCt5i =
    let leftty = Type.Arrow (tyBi, (tyOut, dirtOut)) in
    let rightty = Type.Arrow (tyBi, (alphai, deltai)) in
    Constraint.fresh_ty_coer (leftty, rightty)
  in

  (* 6: Create the elaborated clause *)
  let lvar = CoreTypes.Variable.fresh "l" in
  let lsub =
    Term.subst_comp (Assoc.of_list [ (k, Term.CastExp (Var lvar, omega5i)) ])
  in
  let outExpr =
    ( ((eff, (tyAi, tyBi)) : Term.effect) (* Opi *),
      ( xop,
        Term.PVar lvar,
        Term.CastComp (lsub trgCop, Constraint.BangCoercion (omega3i, omega4i))
      ) )
  in

  (* 7: Combine the results *)
  let outCs = alphaiSkel :: omegaCt3i :: omegaCt4i :: omegaCt5i :: csi in
  (outExpr, outCs)

(* Handlers *)
and tcHandler (inState : state) (lclCtx : TypingEnv.t) (h : Untyped.handler) :
    tcExprOutput =
  (* 1: Generate fresh variables for the input and output types *)
  let alphaIn, alphaInSkel = Constraint.fresh_ty_with_fresh_skel () in
  let deltaIn = Type.fresh_dirt () in
  let alphaOut, alphaOutSkel = Constraint.fresh_ty_with_fresh_skel () in
  let deltaOut = Type.fresh_dirt () in

  (* 2: Process the return and the operation clauses *)
  let trgRet, cs1 =
    tcReturnCase inState lclCtx h.value_clause alphaIn alphaOut deltaOut
  in
  let trgCls, cs2 =
    tcOpCases inState lclCtx h.effect_clauses alphaOut deltaOut
  in

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
    Constraint.HandlerCoercion
      ( Constraint.BangCoercion (Constraint.ReflTy alphaIn, omega7),
        Constraint.BangCoercion
          (Constraint.ReflTy alphaOut, Constraint.ReflDirt deltaOut) )
  in

  let outExpr =
    Term.CastExp
      (Handler { effect_clauses = trgCls; value_clause = trgRet }, handlerCo)
  in
  let outType = Type.Handler ((alphaIn, deltaIn), (alphaOut, deltaOut)) in
  let outCs = (omegaCt7 :: alphaInSkel :: alphaOutSkel :: cs1) @ cs2 in
  (* 7, ain : skelin, aout : skelout && 1, 2, 6 && 3i, 4i, 5i *)
  ((outExpr, outType), outCs)

(* Dispatch: Type inference for a plain value (expression) *)
and tcExpr' (inState : state) (lclCtx : TypingEnv.t) :
    Untyped.plain_expression -> tcExprOutput = function
  | Untyped.Var x -> tcVar inState lclCtx x
  | Untyped.Const c -> tcConst inState lclCtx c
  | Untyped.Annotated (e, ty) -> tcAnnotated inState lclCtx (e, ty)
  | Untyped.Tuple es -> tcTuple inState lclCtx es
  | Untyped.Record lst -> tcRecord inState lclCtx lst
  | Untyped.Variant (lbl, mbe) -> tcVariant inState lclCtx (lbl, mbe)
  | Untyped.Lambda abs -> tcLambda inState lclCtx abs
  | Untyped.Effect eff -> tcEffect inState lclCtx eff
  | Untyped.Handler hand -> tcHandler inState lclCtx hand

(* Type inference for a located value (expression) *)
and tcExpr (inState : state) (lclCtx : TypingEnv.t) (e : Untyped.expression) :
    tcExprOutput =
  tcExpr' inState lclCtx e.it

(* ************************************************************************* *)
(*                          COMPUTATION TYPING                               *)
(* ************************************************************************* *)

(* Dispatch: Type inference for a plan computation *)
and tcComp' (inState : state) (lclCtx : TypingEnv.t) :
    Untyped.plain_computation -> tcCompOutput = function
  | Value exp -> tcValue inState lclCtx exp
  (* Nest a list of let-bindings *)
  | Let ([], c2) -> tcComp inState lclCtx c2
  | Let ([ (pat, c1) ], c2) -> tcLet inState lclCtx pat c1 c2
  | Let ((pat, c1) :: rest, c2) ->
      let subCmp = { it = Untyped.Let (rest, c2); at = c2.at } in
      tcComp' inState lclCtx (Untyped.Let ([ (pat, c1) ], subCmp))
  (* Nest a list of letrec-bindings; MUTUAL RECURSION NOT ALLOWED AT THE MOMENT *)
  | LetRec ([], c2) -> tcComp inState lclCtx c2
  | LetRec ([ (var, abs) ], c2) -> tcLetRecNoGen inState lclCtx var abs c2
  | LetRec ((var, abs) :: rest, c2) ->
      let subCmp = { it = Untyped.LetRec (rest, c2); at = c2.at } in
      tcComp' inState lclCtx (Untyped.LetRec ([ (var, abs) ], subCmp))
  (* Pattern Matching: Special Case 2: Variable-binding *)
  | Match (scr, [ (p, c) ]) when isLocatedVarPat p ->
      tcComp' inState lclCtx
        (Untyped.Let ([ (p, { it = Untyped.Value scr; at = p.at }) ], c))
  (* Pattern Matching: General Case: Monomorphic patterns *)
  | Match (scr, cases) -> tcMatch inState lclCtx scr cases
  | Apply (val1, val2) -> tcApply inState lclCtx val1 val2
  | Handle (hand, cmp) -> tcHandle inState lclCtx hand cmp
  | Check cmp -> tcCheck inState lclCtx cmp

(* Type inference for a located computation *)
and tcComp (inState : state) (lclCtx : TypingEnv.t) (c : Untyped.computation) :
    tcCompOutput =
  tcComp' inState lclCtx c.it

(* Typecheck a value wrapped in a return *)
and tcValue (inState : state) (lclCtxt : TypingEnv.t) (exp : Untyped.expression)
    : tcCompOutput =
  let (outExpr, outType), outCs = tcExpr inState lclCtxt exp in
  ((Term.Value outExpr, (outType, Type.empty_dirt)), outCs)

(* Typecheck a let where c1 is a value *)
and tcLetValNoGen (inState : state) (lclCtxt : TypingEnv.t)
    (patIn : Untyped.pattern) (e1 : Untyped.expression)
    (c2 : Untyped.computation) : tcCompOutput =
  (* 1: Typecheck e1 *)
  let (trgE1, tyA1), cs1 = tcExpr inState lclCtxt e1 in

  (* (v',A, Qv, Sigma1) *)

  (* 2: Typecheck c2 *)
  let x =
    match patIn.it with
    | Untyped.PVar x -> x (* GEORGE: Support nothing else at the moment *)
    | _ -> failwith "tcLetValNoGen: only varpats allowed"
  in
  let (trgC2, (tyB2, dirtD2)), cs2 =
    tcComp inState (extendLclCtxt lclCtxt x tyA1) c2
  in

  (* 3: Combine the results *)
  let outExpr =
    Term.LetVal (trgE1, Term.abstraction_with_ty (Term.PVar x) tyA1 trgC2)
  in
  let outType = (tyB2, dirtD2) in
  let outCs = cs1 @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a let when c1 is a computation (== do binding) *)
and tcLetCmp (inState : state) (lclCtxt : TypingEnv.t) (pat : Untyped.pattern)
    (c1 : Untyped.computation) (c2 : Untyped.computation) : tcCompOutput =
  (* 1: Typecheck c1, the pattern, and c2 *)
  let (trgC1, (tyA1, dirtD1)), cs1 = tcComp inState lclCtxt c1 in
  let trgPat, midCtx, hack = tcLocatedTypedVarPat lclCtxt pat tyA1 in
  let (trgC2, (tyA2, dirtD2)), cs2 = tcComp inState midCtx c2 in

  (* 2: Generate a fresh dirt variable for the result *)
  let delta = Type.fresh_dirt () in

  (* 3: Generate the coercions for the dirts *)
  let omega1, omegaCt1 = Constraint.fresh_dirt_coer (dirtD1, delta) in
  (* s2(D1) <= delta *)
  let omega2, omegaCt2 = Constraint.fresh_dirt_coer (dirtD2, delta) in

  (*    D2  <= delta *)
  let cresC1 =
    Term.CastComp
      (trgC1, Constraint.BangCoercion (Constraint.ReflTy tyA1, omega1))
  in
  let cresC2 =
    Term.CastComp
      (trgC2, Constraint.BangCoercion (Constraint.ReflTy tyA2, omega2))
  in

  let outExpr = Term.Bind (cresC1, (trgPat, cresC2)) in
  let outType = (tyA2, delta) in
  let outCs = hack @ (omegaCt1 :: omegaCt2 :: cs1) @ cs2 in

  ((outExpr, outType), outCs)

(* Typecheck a non-recursive let *)
and tcLet (inState : state) (lclCtxt : TypingEnv.t) (pdef : Untyped.pattern)
    (c1 : Untyped.computation) (c2 : Untyped.computation) : tcCompOutput =
  match c1.it with
  | Untyped.Value e1 -> tcLetValNoGen inState lclCtxt pdef e1 c2
  | _other_computation -> tcLetCmp inState lclCtxt pdef c1 c2

(* Typecheck a (potentially) recursive let *)
and tcLetRecNoGen (inState : state) (lclCtxt : TypingEnv.t)
    (var : Untyped.variable) (abs : Untyped.abstraction)
    (c2 : Untyped.computation) : tcCompOutput =
  (* 1: Generate fresh variables for everything *)
  let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let beta, betaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let delta = Type.fresh_dirt () in

  (* 2: Typecheck the abstraction *)
  let ((trgPat, trgC1), (trgPatTy, (tyA1, dirtD1))), cs1 =
    tcTypedAbstraction inState
      (extendLclCtxt lclCtxt var (Type.Arrow (alpha, (beta, delta))))
      abs alpha
  in

  (* 3: Typecheck c2 *)
  let (trgC2, (tyA2, dirtD2)), cs2 =
    tcComp inState
      (extendLclCtxt lclCtxt var (Type.Arrow (alpha, (tyA1, dirtD1))))
      c2
  in

  (* 3: The assumed type should be at least as general as the inferred one *)
  let omega1, omegaCt1 = Constraint.fresh_ty_coer (tyA1, beta) in
  let omega2, omegaCt2 = Constraint.fresh_dirt_coer (dirtD1, delta) in

  (* 4: Create the (complicated) c1''. *)
  let c1'' =
    let f_coercion =
      Constraint.ArrowCoercion
        (Constraint.ReflTy alpha, Constraint.BangCoercion (omega1, omega2))
    in
    let subst_fn =
      Term.subst_comp
        (Assoc.of_list [ (var, Term.CastExp (Term.Var var, f_coercion)) ])
    in

    subst_fn trgC1
  in

  (* 5: Combine the results *)
  let outExpr =
    Term.LetRec ([ (var, trgPatTy, (tyA1, dirtD1), (trgPat, c1'')) ], trgC2)
  in

  let outType = (tyA2, dirtD2) in
  let outCs = (alphaSkel :: betaSkel :: omegaCt1 :: omegaCt2 :: cs1) @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a case expression *)
and tcMatch (inState : state) (lclCtxt : TypingEnv.t) (scr : Untyped.expression)
    (alts : Untyped.abstraction list) : tcCompOutput =
  if List.length alts > 0 then tcNonEmptyMatch inState lclCtxt scr alts
  else tcEmptyMatch inState lclCtxt scr

(* Typecheck a non-empty case expression *)
and tcNonEmptyMatch (inState : state) (lclCtxt : TypingEnv.t)
    (scr : Untyped.expression) (alts : Untyped.abstraction list) : tcCompOutput
    =
  (* 0: Make sure that we have at least one alternative *)
  assert (List.length alts > 0);

  (* 1: Generate fresh variables for the result *)
  let alphaOut, alphaOutSkel = Constraint.fresh_ty_with_fresh_skel () in
  let deltaOut = Type.fresh_dirt () in

  (* 2: Infer a type for the patterns *)
  let patTy = inferCheckLocatedClosedPatAlts inState alts in

  (* 4: Typecheck the scrutinee and the alternatives *)
  let (trgScr, scrTy), cs1 = tcExpr inState lclCtxt scr in
  let trgAlts, cs2 =
    mapAndUnzipTcOutputs
      (fun alt -> tcAlternative inState lclCtxt patTy alt (alphaOut, deltaOut))
      alts
  in

  (* 5: Generate the coercion for casting the scrutinee *)
  (* NOTE: The others should be already included in 'altRes' *)
  let omegaScr, omegaCtScr = Constraint.fresh_ty_coer (scrTy, patTy) in

  (* 6: Combine the results *)
  let outType = (alphaOut, deltaOut) in
  let outExpr =
    Term.Match (Term.CastExp (trgScr, omegaScr), outType, trgAlts)
  in
  let outCs = (alphaOutSkel :: omegaCtScr :: cs1) @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck an empty case expression *)
and tcEmptyMatch (inState : state) (lclCtxt : TypingEnv.t)
    (scr : Untyped.expression) : tcCompOutput =
  (* 1: Generate fresh variables for the result *)
  let alphaOut, alphaOutSkel = Constraint.fresh_ty_with_fresh_skel () in
  let deltaOut = Type.fresh_dirt () in

  (* 2: Typecheck the scrutinee *)
  let (trgScr, _scrTy), cs1 = tcExpr inState lclCtxt scr in

  (* 3: Combine the results *)
  let outType = (alphaOut, deltaOut) in
  let outExpr = Term.Match (trgScr, outType, []) in
  let outCs = alphaOutSkel :: cs1 in
  ((outExpr, outType), outCs)

(* Typecheck a function application *)
and tcApply (inState : state) (lclCtxt : TypingEnv.t)
    (val1 : Untyped.expression) (val2 : Untyped.expression) : tcCompOutput =
  (* Infer the types of val1 and val2 *)
  let (trgVal1, valTy1), cs1 = tcExpr inState lclCtxt val1 in
  let (trgVal2, valTy2), cs2 = tcExpr inState lclCtxt val2 in

  (* Generate fresh variables for the result *)
  let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let delta = Type.fresh_dirt () in

  (* Create the constraint and the cast elaborated expression *)
  let omega, omegaCt =
    Constraint.fresh_ty_coer (valTy1, Type.Arrow (valTy2, (alpha, delta)))
  in
  let castVal1 = Term.CastExp (trgVal1, omega) in

  let outExpr = Term.Apply (castVal1, trgVal2) in
  let outType = (alpha, delta) in
  let outCs = (alphaSkel :: omegaCt :: cs1) @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a handle-computation *)
and tcHandle (inState : state) (lclCtxt : TypingEnv.t)
    (hand : Untyped.expression) (cmp : Untyped.computation) : tcCompOutput =
  (* Typecheck the handler and the computation *)
  let (trgHand, tyA1), cs1 = tcExpr inState lclCtxt hand in
  (* Typecheck the handler *)
  let (trgCmp, (tyA2, dirtD2)), cs2 = tcComp inState lclCtxt cmp in

  (* Typecheck the computation *)

  (* Generate fresh variables *)
  let alpha1, alphaSkel1 = Constraint.fresh_ty_with_fresh_skel () in
  let delta1 = Type.fresh_dirt () in
  let alpha2, alphaSkel2 = Constraint.fresh_ty_with_fresh_skel () in
  let delta2 = Type.fresh_dirt () in

  (* Create all constraints *)
  let omega1, omegaCt1 =
    Constraint.fresh_ty_coer
      (tyA1, Type.Handler ((alpha1, delta1), (alpha2, delta2)))
  in
  let omega2, omegaCt2 = Constraint.fresh_ty_coer (tyA2, alpha1) in
  let omega3, omegaCt3 = Constraint.fresh_dirt_coer (dirtD2, delta1) in

  (* Combine all the outputs *)
  let outExpr =
    let castHand = Term.CastExp (trgHand, omega1) in
    let castCmp =
      Term.CastComp (trgCmp, Constraint.BangCoercion (omega2, omega3))
    in
    Term.Handle (castHand, castCmp)
  in
  let outType = (alpha2, delta2) in
  let outCs =
    (alphaSkel1 :: alphaSkel2 :: omegaCt1 :: omegaCt2 :: omegaCt3 :: cs1) @ cs2
  in
  ((outExpr, outType), outCs)

(* Typecheck a "Check" expression (GEORGE does not know what this means yet *)
and tcCheck (_inState : state) (_lclCtxt : TypingEnv.t)
    (_cmp : Untyped.computation) : tcCompOutput =
  failwith __LOC__

(* GEORGE: Planned TODO for the future I guess?? *)

(* ************************************************************************* *)
(*                               UTILITIES                                   *)
(* ************************************************************************* *)

(* Given the expected type of the pattern and the expected result type,
 * typecheck a single case alternative. *)
and tcAlternative (inState : state) (lclCtx : TypingEnv.t)
    (patTy : Type.ty) (* Expected pattern type *)
    ((pat, cmp) : Untyped.abstraction) (* Case alternative *)
    ((tyAout, dirtDout) : Type.dirty) : Term.abstraction tcOutput =
  (* Expected output type *)

  (* Typecheck the pattern and the right-hand side *)
  let trgPat, midCtxt = checkLocatedPatTy inState lclCtx pat patTy in
  let (trgCmp, (tyA, dirtD)), cs = tcComp inState midCtxt cmp in
  (* Generate coercions to cast the RHS *)
  let omegaL, omegaCtL = Constraint.fresh_ty_coer (tyA, tyAout) in
  let omegaR, omegaCtR = Constraint.fresh_dirt_coer (dirtD, dirtDout) in
  (* Combine the results *)
  let outExpr =
    (trgPat, Term.CastComp (trgCmp, Constraint.BangCoercion (omegaL, omegaR)))
  in
  let outCs = omegaCtL :: omegaCtR :: cs in
  (outExpr, outCs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and tcTypedAbstraction (inState : state) (lclCtx : TypingEnv.t) (pat, cmp) patTy
    =
  let trgPat, midLclCtx, hack = tcLocatedTypedVarPat lclCtx pat patTy in
  let (trgCmp, cmpTy), cs = tcComp inState midLclCtx cmp in
  (((trgPat, trgCmp), (patTy, cmpTy)), hack @ cs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and tcTypedAbstraction2 (inState : state) (lclCtx : TypingEnv.t)
    (pat1, pat2, cmp) patTy1 patTy2 =
  let trgPat1, midCtx1, hack1 = tcLocatedTypedVarPat lclCtx pat1 patTy1 in
  let trgPat2, midCtx2, hack2 = tcLocatedTypedVarPat midCtx1 pat2 patTy2 in
  let (trgCmp, cmpTy), cs = tcComp inState midCtx2 cmp in
  (((trgPat1, trgPat2, trgCmp), (patTy1, patTy2, cmpTy)), hack1 @ hack2 @ cs)

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
    (fun (omega, pi) qual -> Term.LambdaDirtCoerVar (omega, pi, qual))
    dirtCs
  |> (* 2: Add the constraint abstractions (type) *)
  List.fold_right
    (fun (omega, pi) qual -> Term.LambdaTyCoerVar (omega, pi, qual))
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
  let (exp', ty'), outCs = tcExpr inState TypingEnv.empty exp in
  let sub, residuals = Unification.solve outCs in
  let exp'' = subInExp sub exp' and ty'' = subInValTy sub ty' in
  generalize residuals ty'' exp''

(* This is currently unused, top lets are translated into local lets *)
let tcTopLetRec (inState : state) (var : Untyped.variable)
    (pat : Untyped.pattern) (cmp : Untyped.computation) =
  (* 1: Generate fresh variables for everything *)
  let alpha, alphaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let beta, betaSkel = Constraint.fresh_ty_with_fresh_skel () in
  let delta = Type.fresh_dirt () in

  (* 2: Typecheck the abstraction *)
  let ((trgPat, trgC1), (trgPatTy, (tyA1, dirtD1))), cs =
    tcTypedAbstraction inState
      (extendLclCtxt initial_lcl_ty_env var (Type.Arrow (alpha, (beta, delta))))
      (pat, cmp) alpha
  in

  (* 3: The assumed type should be at least as general as the inferred one *)
  let omega1, omegaCt1 = Constraint.fresh_ty_coer (tyA1, beta) in
  let omega2, omegaCt2 = Constraint.fresh_dirt_coer (dirtD1, delta) in

  (* 4: Create the (complicated) c1''. *)
  let c1'' =
    let f_coercion =
      Constraint.ArrowCoercion
        (Constraint.ReflTy alpha, Constraint.BangCoercion (omega1, omega2))
    in
    Term.subst_comp
      (Assoc.of_list [ (var, Term.CastExp (Term.Var var, f_coercion)) ])
      trgC1
  in

  (* 5: Solve (simplify, actually) the generated constraints *)
  let subst, residuals =
    Unification.solve (alphaSkel :: betaSkel :: omegaCt1 :: omegaCt2 :: cs)
  in

  (* 6: Substitute back into everything *)
  let trgPatTy = subInValTy subst trgPatTy in
  let tyA1 = subInValTy subst tyA1 in
  let dirtD1 = subInDirt subst dirtD1 in
  (* trgPat needs not a substitution *)
  let trgC1 = subInCmp subst c1'' in

  (* 7: Partition the residual constraints and abstract over them *)
  let outTy, _ =
    generalize residuals (Type.Arrow (trgPatTy, (tyA1, dirtD1))) (Term.Tuple [])
  (* Matija: Make sure to generalize the expression as well *)
  and outExpr = ([ (var, trgPatTy, (tyA1, dirtD1), (trgPat, c1'')) ], trgC1) in
  (outExpr, outTy)

(* ************************************************************************* *)
(* ************************************************************************* *)

let monomorphize free_ty_params cnstrs =
  let free_cnstrs_params = Constraint.free_params_constraints cnstrs in
  let free_params = Type.FreeParams.union free_ty_params free_cnstrs_params in
  let monomorphize_skeletons =
    List.map
      (fun sk -> Constraint.SkelEq (Type.SkelParam sk, Type.SkelTuple []))
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
  let (comp', drty), cnstrs = tcComp state initial_lcl_ty_env comp in
  let sub, residuals = Unification.solve cnstrs in
  ((subInCmp sub comp', subInCmpTy sub drty), residuals)

let infer_expression state expr =
  let (expr', ty), cnstrs = tcExpr state initial_lcl_ty_env expr in
  let sub, residuals = Unification.solve cnstrs in
  ((subInExp sub expr', subInValTy sub ty), residuals)

let infer_rec_abstraction state f abs =
  match
    tcLetRecNoGen state initial_lcl_ty_env f abs
      (unlocated @@ Untyped.Value (unlocated @@ Untyped.Tuple []))
  with
  | ( (Term.LetRec ([ (_f, ty_in, drty_out, (p, c)) ], _ret_unit), _unit_drty),
      cnstrs ) ->
      let abs' = (p, ty_in, c)
      and abs_ty' = (ty_in, drty_out)
      and sub, residuals = Unification.solve cnstrs in
      ((subInAbs sub abs', subInAbsTy sub abs_ty'), residuals)
  | _ -> assert false

(* Typecheck a top-level expression *)
let top_level_computation state comp =
  let (comp, drty), residuals = infer_computation state comp in
  let free_ty_params = Type.free_params_dirty drty in
  let mono_sub = monomorphize free_ty_params residuals in
  let mono_comp = subInCmp mono_sub comp
  and mono_drty = subInCmpTy mono_sub drty in
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (Type.FreeParams.is_empty (Term.free_params_computation mono_comp));
  (mono_comp, mono_drty)

let top_level_rec_abstraction state x (abs : Untyped.abstraction) =
  let (abs, abs_ty), residuals = infer_rec_abstraction state x abs in
  let free_ty_params = Type.free_params_abstraction_ty abs_ty in
  let mono_sub = monomorphize free_ty_params residuals in
  let mono_abs = subInAbs mono_sub abs
  and mono_abs_ty = subInAbsTy mono_sub abs_ty in
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (
    Type.FreeParams.is_empty (Term.free_params_abstraction_with_ty mono_abs));
  (mono_abs, mono_abs_ty)

let top_level_expression state expr =
  let (expr, ty), residuals = infer_expression state expr in
  let free_ty_params = Type.free_params_ty ty in
  let mono_sub = monomorphize free_ty_params residuals in
  let mono_expr = subInExp mono_sub expr and mono_ty = subInValTy mono_sub ty in
  (* We assume that all free variables in the term already appeared in its type or constraints *)
  assert (Type.FreeParams.is_empty (Term.free_params_expression mono_expr));
  (mono_expr, mono_ty)

(* Add an external binding to the typing environment *)
let addExternal ctx x ty =
  {
    ctx with
    gblCtxt =
      TypingEnv.update ctx.gblCtxt x (Type.source_to_target ctx.tctx_st ty);
  }

let add_type ctx x ty = { ctx with gblCtxt = TypingEnv.update ctx.gblCtxt x ty }

let add_type_definitions state tydefs =
  {
    state with
    tctx_st =
      TypeDefinitionContext.extend_type_definitions ~loc:Location.unknown tydefs
        state.tctx_st;
  }
