open CoreUtils
module Untyped = UntypedSyntax
open Typed

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

let georgeTODO () = failwith __LOC__

let warnAddConstraints s cs =
  Print.debug "%s: Added %d constraints: " s (List.length cs);
  Unification.print_c_list cs

(* [WRITER] SUBSTITUTION *)

(* Extend the generated substitution *)
let extendGenSub acc sub = Substitution.merge acc sub (* GEORGE: I hope to God for the order to be correct here *)
let flippedExtendGenSub sub acc = extendGenSub acc sub

(* [STATE] INFERENCE STATE *)

type state =
  { gblCtxt: TypingEnv.t                                            (* Global Typing Environment *)
  ; effects: (Types.target_ty * Types.target_ty) Typed.EffectMap.t  (* Valid Effects             *)
  ; constraints: Typed.omega_ct list                                (* Type Constraints          *)
  }

(* Add a single constraint to the state *)
let add_constraint cons st =
  {st with constraints = cons :: st.constraints}

(* Add a batch of constraints to the state *)
let add_constraints const st =
  List.fold_left (fun st' x -> add_constraint x st') st const

(* Add a single term binding to the global typing environment *)
let add_gbl_def env x ty_sch =
  {env with gblCtxt = TypingEnv.update env.gblCtxt x ty_sch}

(* Apply a substitution to the global typing environment *)
let apply_sub_to_gblCtxt env sub =
  {env with gblCtxt = TypingEnv.apply_sub env.gblCtxt sub}

(* Extend the global typing environment with multiple term bindings *)
let extend_env vars env =
  List.fold_right
    (fun (x, ty_sch) env ->
      {env with gblCtxt = TypingEnv.update env.gblCtxt x ty_sch} )
    vars env

type computation_typing_result =
  { computation: Typed.computation
  ; dtype: Types.target_dirty
  }

type expression_typing_result =
  { expression: Typed.expression
  ; ttype: Types.target_ty
  }

(* Initial type inference state: everything is empty *)
let initial_state : state
                  = { gblCtxt       = TypingEnv.empty
                    ; effects       = Typed.EffectMap.empty
                    ; constraints   = []
                    }

let print_env env =
  List.iter
    (fun (x, ty_sch) ->
      Print.debug "%t : %t" (Typed.print_variable x)
        (Types.print_target_ty ty_sch) )
    env


let add_effect eff (ty1, ty2) st =
  let ty1 = Types.source_to_target ty1 in
  let ty2 = Types.source_to_target ty2 in
  {st with effects= EffectMap.add eff (ty1, ty2) st.effects}

(* ... *)

let rec state_free_ty_vars st =
  List.fold_right
    (fun (_, ty) acc -> Types.TyParamSet.union (Types.ftvsOfTargetValTy ty) acc)
    st Types.TyParamSet.empty


let rec state_free_dirt_vars st =
  List.fold_right
    (fun (_, ty) acc ->
      Types.DirtParamSet.union (Types.fdvsOfTargetValTy ty) acc )
    st Types.DirtParamSet.empty

(* ************************************************************************* *)
(*                              DEBUGGING                                    *)
(* ************************************************************************* *)

let showInputEnv (rule : string) (ctx : TypingEnv.t)
  = Print.debug "Rule [%s]: Input Env:" rule
  ; print_env (TypingEnv.return_context ctx)

let showInputCs (rule : string) (inState : state)
  = Print.debug "Rule [%s]: Input State:" rule
  ; Unification.print_c_list inState.constraints

(* ************************************************************************* *)
(*                            SUBSTITUTIONS                                  *)
(* ************************************************************************* *)

(* Substitute in typing environments *)
let subInEnv sub env = TypingEnv.apply_sub env sub

(* Substitute in target values and computations *)
let subInCmp sub cmp = Substitution.apply_substitutions_to_computation sub cmp
let subInExp sub exp = Substitution.apply_substitutions_to_expression sub exp

(* Substitute in target value types, computation types, and dirts *)
let subInValTy sub ty        = Substitution.apply_substitutions_to_type sub ty
let subInDirt  sub dirt      = Substitution.apply_substitutions_to_dirt sub dirt
let subInCmpTy sub (ty,dirt) = (subInValTy sub ty, subInDirt sub dirt)

(* Substitute in value, dirt, and computation coercions *)
let subInValCo  sub co = Substitution.apply_sub_tycoer sub co
let subInDirtCo sub co = Substitution.apply_sub_dirtcoer sub co
let subInCmpCo  sub co = Substitution.apply_sub_dirtycoer sub co

(* Substitute in skeletons *)
let subInSkel sub skel = Substitution.apply_substitutions_to_skeleton sub skel

(* Substitute in type and dirt inequalities *)
let subInTyCt sub (ty1,ty2) = (subInValTy sub ty1, subInValTy sub ty2)
let subInDirtCt sub (d1,d2) = (subInDirt sub d1, subInDirt sub d2)

(* ************************************************************************* *)

(* Apply a term to all possible arguments *)
let applyTerm skeletons types dirts tyCoercions dirtCoercions exp : Typed.expression =
  let foldLeft f xs x0 = List.fold_left f x0 xs in (* GEORGE: Just for convenience *)
  exp
  |> (* 1: Apply to the skeletons *)
     foldLeft (fun e s -> Typed.ApplySkelExp (e, s)) skeletons
  |> (* 2: Apply to the types *)
     foldLeft (fun e a -> Typed.ApplyTyExp (e, a)) types
  |> (* 3: Apply to the dirts *)
     foldLeft (fun e d -> Typed.ApplyDirtExp (e, d)) dirts
  |> (* 4: Apply to the type coercions *)
     foldLeft (fun e c -> Typed.ApplyTyCoercion (e, c)) tyCoercions
  |> (* 5: Apply to the dirt coercions *)
     foldLeft (fun e c -> Typed.ApplyDirtCoercion (e, c)) dirtCoercions

(* ************************************************************************* *)
(*                           PARTITION TYPES                                 *)
(* ************************************************************************* *)

(* Partition a HM-like type into its corresponding abstractions. We follow the
 * original publication and expect the abstractions in this strict order:
 * skeleton variables, type variables, dirt variables, type inequalities, and
 * dirt inequalities. At the end, there should be a HM-monotype (that is, no
 * qualification or quantification in nested positions). If the type is not in
 * that exact form, [stripHindleyMilnerLikeTy] will return [None]. *)
let stripHindleyMilnerLikeTy : Types.target_ty ->
    ( CoreTypes.SkelParam.t list                  (* Skeleton variables *)
    * (CoreTypes.TyParam.t * Types.skeleton) list (* Skeleton-annotated type variables *)
    * CoreTypes.DirtParam.t list                  (* Dirt variables *)
    * Types.ct_ty list                            (* Type inequalities *)
    * Types.ct_dirt list                          (* Dirt inequalities *)
    * Types.target_ty ) option =                  (* Remaining monotype *)
  let rec stripSkelAbs = function
    | Types.TySchemeSkel (s,ty) ->
        let skels, rem = stripSkelAbs ty in (s :: skels, rem)
    | other_type -> ([], other_type) in
  let rec stripTyAbs = function
    | Types.TySchemeTy (a,s,ty) ->
        let alphaSkels, rem = stripTyAbs ty in ((a,s) :: alphaSkels, rem)
    | other_type -> ([], other_type) in
  let rec stripDirtAbs = function
    | Types.TySchemeDirt (d, ty) ->
        let ds, rem = stripDirtAbs ty in (d :: ds, rem)
    | other_type -> ([], other_type) in
  let rec stripTyQual = function
    | Types.QualTy (ct, ty) ->
        let cs, rem = stripTyQual ty in (ct :: cs, rem)
    | other_type -> ([], other_type) in
  let rec stripDirtQual = function
    | Types.QualDirt (ct, ty) ->
        let cs, rem = stripDirtQual ty in (ct :: cs, rem)
    | other_type -> ([], other_type) in
  function inTy ->
    let allSkelVars, ty1 = stripSkelAbs  inTy in  (* 1: Strip off the skeleton abstractions *)
    let allTyVars  , ty2 = stripTyAbs    ty1  in  (* 2: Strip off the type abstractions *)
    let allDirtVars, ty3 = stripDirtAbs  ty2  in  (* 3: Strip off the dirt abstractions *)
    let allTyCs    , ty4 = stripTyQual   ty3  in  (* 4: Strip off the type inequality qualification *)
    let allDirtCs  , ty5 = stripDirtQual ty4  in  (* 5: Strip off the dirt inequality qualification *)
    if Types.isMonoTy ty5                         (* 6: Ensure the remainder is a monotype *)
      then Some (allSkelVars,allTyVars,allDirtVars,allTyCs,allDirtCs,ty5)
      else None

(* ************************************************************************* *)
(*                       VARIABLE INSTANTIATION                              *)
(* ************************************************************************* *)

let instantiateVariable (x : variable) (scheme : Types.target_ty)
  : (Typed.expression * Types.target_ty * Typed.omega_ct list) =
  (* 1: Take the type signature apart *)
  let skelVars, tyVarsWithSkels, dirtVars, tyCs, dirtCs, monotype =
    (match stripHindleyMilnerLikeTy scheme with
     | Some (a,b,c,d,e,f) -> (a,b,c,d,e,f)
     | None -> failwith "instantiateVariable: Non-HM type in the environment!") in

  (* 2: Generate fresh skeleton, type, and dirt variables *)
  let newSkelVars = List.map (fun _ -> CoreTypes.SkelParam.fresh ()) skelVars in
  let newTyVars   = List.map (fun _ -> CoreTypes.TyParam.fresh ()) tyVarsWithSkels in
  let newDirtVars = List.map (fun _ -> Types.fresh_dirt ()) dirtVars in

  (* 3: Generate the freshening substitution *)
  let foldLeft f xs x0 = List.fold_left f x0 xs in (* GEORGE: Just for convenience *)
  let sub = Substitution.empty
            |> (* Substitute the old skeleton variables for the fresh ones *)
               foldLeft
                 (fun sub (oldS, newSkelVar) ->
                    let newS = Types.SkelParam newSkelVar in
                    sub |> Substitution.add_skel_param_substitution oldS newS)
                 (List.combine skelVars newSkelVars)
            |> (* Substitute the old type variables for the fresh ones *)
               foldLeft
                 (fun sub (oldA, newTyVar) ->
                    let newA = Types.TyParam newTyVar in
                    sub |> Substitution.add_type_substitution oldA newA)
                 (List.combine (List.map fst tyVarsWithSkels) newTyVars)
            |> (* Substitute the old dirt variables for the fresh ones *)
               foldLeft
                 (fun sub (oldD, newD) ->
                    sub |> Substitution.add_dirt_substitution oldD newD)
                 (List.combine dirtVars newDirtVars)
  in

  (* 4: Generate the wanted skeleton constraints *)
  let wantedSkelCs = List.map (* a' : sigma(tau) *)
                       (fun (a,s) -> Typed.TyParamHasSkel (a, subInSkel sub s))
                       (List.combine newTyVars (List.map snd tyVarsWithSkels)) in

  (* 5: Generate the wanted type inequality constraints *)
  let tyOmegas, wantedTyCs =
    tyCs |> List.map (fun ct -> fresh_ty_coer (subInTyCt sub ct))
         |> List.split in

  (* 5: Generate the wanted dirt inequality constraints *)
  let dirtOmegas, wantedDirtCs =
    dirtCs |> List.map (fun ct -> fresh_dirt_coer (subInDirtCt sub ct))
           |> List.split in

  (* 6: Apply x to all its fresh arguments *)
  let targetX = applyTerm
                  (List.map (fun s -> Types.SkelParam s) newSkelVars)
                  (List.map (fun a -> Types.TyParam a) newTyVars)
                  newDirtVars
                  tyOmegas
                  dirtOmegas
                  (Typed.Var x)

  in
  (* 7: Combine the results *)
  ( targetX
  , subInValTy sub monotype
  , wantedSkelCs @ wantedTyCs @ wantedDirtCs
  )

(* ************************************************************************* *)
(*                           BASIC DEFINITIONS                               *)
(* ************************************************************************* *)

(* Inference rule inputs: constraint state & typing environment/context *)
(* GEORGE: Unused at the moment *)
type tcInputs =
  { inState : state
  ; lclCtx  : TypingEnv.t
  }

(* Inference rule outputs: constraint state & substitution *)
type ('exp, 'ty) tcOutputs =
  { outExpr  : 'exp
  ; outType  : 'ty
  ; outState : state (* GEORGE: Leave only (a) constraints, and (b) global tyenv in here *)
  ; outSubst : Substitution.t
  }

(* Value typing output *)
type tcValOutput = (Typed.expression, Types.target_ty) tcOutputs

(* Computation typing output *)
type tcCmpOutput = (Typed.computation, Types.target_dirty) tcOutputs

(* Typecheck a list of values *)
let rec tcManyVal (inState : state)
                  (lclCtxt : TypingEnv.t)
                  (xss : Untyped.expression list)
                  (tc : state -> TypingEnv.t -> Untyped.expression -> tcValOutput)
    : (Typed.expression list, Types.target_ty list) tcOutputs =
  match xss with
  | []      -> { outExpr  = []
               ; outType  = []
               ; outState = inState (* Unchanged *)
               ; outSubst = Substitution.empty
               }
  | x :: xs -> let xres  = tc inState lclCtxt x in
               let xsres = tcManyVal xres.outState (subInEnv xres.outSubst lclCtxt) xs tc in
               { outExpr  = (subInExp xsres.outSubst xres.outExpr) :: xsres.outExpr
               ; outType  = (subInValTy xsres.outSubst xres.outType) :: xsres.outType
               ; outState = xsres.outState                            (* Keep only the final state *)
               ; outSubst = extendGenSub xres.outSubst xsres.outSubst (* Compose the substitutions *)
               }

(* Typecheck a list of computations *)
let rec tcManyCmp (inState : state)
                  (lclCtxt : TypingEnv.t)
                  (xss : Untyped.computation list)
                  (tc : state -> TypingEnv.t -> Untyped.computation -> tcCmpOutput)
    : (Typed.computation list, Types.target_dirty list) tcOutputs =
  match xss with
  | []      -> { outExpr  = []
               ; outType  = []
               ; outState = inState (* Unchanged *)
               ; outSubst = Substitution.empty
               }
  | x :: xs -> let xres  = tc inState lclCtxt x in
               let xsres = tcManyCmp xres.outState (subInEnv xres.outSubst lclCtxt) xs tc in
               { outExpr  = (subInCmp xsres.outSubst xres.outExpr) :: xsres.outExpr
               ; outType  = (subInCmpTy xsres.outSubst xres.outType) :: xsres.outType
               ; outState = xsres.outState                            (* Keep only the final state *)
               ; outSubst = extendGenSub xres.outSubst xsres.outSubst (* Compose the substitutions *)
               }
  (* GEORGE: I'd kill for some abstraction, having both tcManyVal and tcManyCmp is nasty. *)

(* ************************************************************************* *)
(*                       PATTERN TYPING (REVISED)                            *)
(* ************************************************************************* *)

(** CHECK the type of a (located) pattern. Return the extended typing
 * environment with the additional term bindings. *)
let rec checkLocatedPatTy (lclCtxt : TypingEnv.t) (pat : Untyped.pattern) (patTy : Types.target_ty)
  : (Typed.pattern * TypingEnv.t)
  = checkPatTy lclCtxt pat.it patTy

(** CHECK the type of a pattern. Return the extended typing environment with
 * the additional term bindings. *)
and checkPatTy (lclCtxt : TypingEnv.t) (pat : Untyped.plain_pattern) (patTy : Types.target_ty)
  : (Typed.pattern * TypingEnv.t)
  = match pat with
    (* Variable Case *)
    | Untyped.PVar x             -> (Typed.PVar x, extendLclCtxt lclCtxt x patTy)
    (* Wildcard Case *)
    | Untyped.PNonbinding        -> (Typed.PNonbinding, lclCtxt)
    (* Nullary Constructor Case *)
    | Untyped.PVariant (lbl, None) ->
        let ty_in, ty_out = Types.constructor_signature lbl in
        if (ty_in = Types.Tuple [] && patTy = ty_out)
          then (Typed.PVariant (lbl, Typed.PTuple []), lclCtxt)
          else failwith "checkPatTy: PVariant(None)"
    (* Unary Constructor Case *)
    | Untyped.PVariant (lbl, Some p) ->
        let ty_in, ty_out = Types.constructor_signature lbl in
        if (patTy = ty_out)
          then let p', midCtxt = checkLocatedPatTy lclCtxt p ty_in in
               (Typed.PVariant (lbl, p'), midCtxt)
          else failwith "checkPatTy: PVariant(Some)"
    (* Constant Case *)
    | Untyped.PConst c ->
        if (patTy = Types.type_const c)
          then (Typed.PConst c, lclCtxt)
          else failwith "checkPatTy: PConst"
    (* GEORGE: Not implemented yet cases *)
    | Untyped.PAs (p, v)         -> failwith __LOC__
    | Untyped.PTuple l           -> failwith __LOC__
    | Untyped.PRecord r          -> failwith __LOC__
    | Untyped.PAnnotated (p, ty) -> failwith __LOC__

(** INFER the type of a (located) pattern. Return the extended typing
 * environment with the additional term bindings. Return also the extended
 * constraint set, in case we had to create fresh type variables and skeletons
 * (No other constraints are added). *)
let rec inferLocatedPatTy (inState : state) (lclCtxt : TypingEnv.t) (pat : Untyped.pattern)
  : (Typed.pattern * Types.target_ty * state * TypingEnv.t)
  = inferPatTy inState lclCtxt pat.it

(** INFER the type of a pattern. Return the extended typing environment with the
 * additional term bindings. Return also the extended constraint set, in case
 * we had to create fresh type variables and skeletons (No other constraints
 * are added). *)
and inferPatTy (inState : state) (lclCtxt : TypingEnv.t) (pat : Untyped.plain_pattern)
  : (Typed.pattern * Types.target_ty * state * TypingEnv.t)
  = match pat with
    (* Variable Case *)
    | Untyped.PVar x ->
        let tyVar, tyVarHasSkel = Typed.fresh_ty_with_fresh_skel () in
        warnAddConstraints "inferPatTy" [tyVarHasSkel];
        ( Typed.PVar x
        , tyVar
        , inState |> add_constraint tyVarHasSkel
        , extendLclCtxt lclCtxt x tyVar )
    (* Wildcard Case *)
    | Untyped.PNonbinding ->
        let tyVar, tyVarHasSkel = Typed.fresh_ty_with_fresh_skel () in
        warnAddConstraints "inferPatTy" [tyVarHasSkel];
        ( Typed.PNonbinding
        , tyVar
        , inState |> add_constraint tyVarHasSkel
        , lclCtxt )
    (* Nullary Constructor Case *)
    | Untyped.PVariant (lbl, None) ->
        let ty_in, ty_out = Types.constructor_signature lbl in
        if (ty_in = Types.Tuple [])
          then (Typed.PVariant (lbl, Typed.PTuple []), ty_out, inState, lclCtxt)
          else failwith "inferPatTy: PVariant(None)"
    (* Unary Constructor Case *)
    | Untyped.PVariant (lbl, Some p) ->
        let ty_in, ty_out = Types.constructor_signature lbl in
        let p', midCtxt = checkLocatedPatTy lclCtxt p ty_in in
        (Typed.PVariant (lbl, p'), ty_out, inState, midCtxt)
    (* Constant Case *)
    | Untyped.PConst c -> (Typed.PConst c, Types.type_const c, inState, lclCtxt)
    (* GEORGE: Not implemented yet cases *)
    | Untyped.PAs (p, v)         -> failwith __LOC__
    | Untyped.PTuple l           -> failwith __LOC__
    | Untyped.PRecord r          -> failwith __LOC__
    | Untyped.PAnnotated (p, ty) -> failwith __LOC__

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

(* Typecheck a located pattern given the expected type *)
let rec tcLocatedTypedPat (inState : state) (lclCtxt : TypingEnv.t) pat ty
  = tcTypedPat inState lclCtxt pat.it ty

(* Typecheck a pattern : the bindings introduced by the pattern are included in
 * the output context: Gout = Gin, xs. Any inequalities implied by constants or
 * variants are included in the output state. *)
and tcTypedPat (inState : state) (lclCtxt : TypingEnv.t) pat pat_ty =
  match pat with
  | Untyped.PVar x             -> (Typed.PVar x     , pat_ty, inState, extendLclCtxt lclCtxt x pat_ty)
  | Untyped.PNonbinding        -> (Typed.PNonbinding, pat_ty, inState, lclCtxt)
  | Untyped.PAs (p, v)         -> failwith __LOC__ (* GEORGE: Not implemented yet *)
  | Untyped.PTuple []          -> if Types.types_are_equal (Types.Tuple []) pat_ty
                                    then (Typed.PTuple [], pat_ty, inState, lclCtxt)
                                    else failwith __LOC__ (* GEORGE: Not implemented yet *)
  | Untyped.PTuple l           -> failwith __LOC__ (* GEORGE: Not implemented yet *)
  | Untyped.PRecord r          -> failwith __LOC__ (* GEORGE: Not implemented yet *)
  | Untyped.PAnnotated (p, ty) -> failwith __LOC__ (* GEORGE: Not implemented yet *)

  | Untyped.PVariant (_,_) -> failwith __LOC__
  | Untyped.PConst _       -> failwith __LOC__
(*
  (* GEORGE: The original seemed wrong to me, we compute the midState but we do
   * not use it in the first case. We return inState instead. Here I do it the
   * right way I hope. *)
  | Untyped.PVariant (lbl, p) -> (
      let ty_in, ty_out = Types.constructor_signature lbl in
      (* GEORGE: TODO: Still, we drop the coercion variable. This is not
       * correct (the types might still be different) *)
      let q = snd (Typed.fresh_ty_coer (ty_out, pat_ty)) in
      let midState = add_constraint q inState in
      match p with
      | None   -> (Typed.PVariant (lbl, Typed.PTuple []), pat_ty, midState, lclCtxt)
      | Some p -> let p', _, outState, lclOutCtxt = tcLocatedTypedPat midState lclCtxt p ty_in
                  in  (Typed.PVariant (lbl, p'), pat_ty, outState, lclOutCtxt)
      )
  | Untyped.PConst c ->
      let q = snd (Typed.fresh_ty_coer (Types.type_const c, pat_ty)) in
      (Typed.PConst c, pat_ty, add_constraint q inState, lclCtxt)
*)

(* Typecheck a located pattern without a given type *)
and tcLocatedPat (inState : state) (lclCtxt : TypingEnv.t) pat
  = tcPat inState lclCtxt pat.it

(* Typecheck a pattern without a given type *)
and tcPat (inState : state) (lclCtxt : TypingEnv.t) pat
  = let tyvar, tyvar_skel = Typed.fresh_ty_with_fresh_skel () in
    tcTypedPat (add_constraint tyvar_skel inState) lclCtxt pat tyvar

(* ************************************************************************* *)
(*                             VALUE TYPING                                  *)
(* ************************************************************************* *)

(* Lookup the type of a term variable in the local and the global contexts
 * (local first, global after). George: I wish we had monads.. *)
let lookupTmVar (inState : state) (lclCtxt : TypingEnv.t) x =
  match TypingEnv.lookup lclCtxt x with
  | Some scheme -> Some scheme
  | None        -> match TypingEnv.lookup inState.gblCtxt x with
                   | Some scheme -> Some scheme
                   | None        -> None

(* Term Variables *)
let rec tcVar (inState : state) (lclCtxt : TypingEnv.t) (x : variable) : tcValOutput =
  match lookupTmVar inState lclCtxt x with
  | Some scheme -> Print.debug
                     "tcVar: Just found that variable %t has type %t, Yay!"
                     (Typed.print_variable x)
                     (Types.print_target_ty scheme) ;
                   let target_x, x_monotype, constraints = instantiateVariable x scheme
                   in  warnAddConstraints "tcVar" constraints;
                       { outExpr  = target_x
                       ; outType  = x_monotype
                       ; outState = add_constraints constraints inState
                       ; outSubst = Substitution.empty
                       }
  | None -> Print.debug "Variable not found: %t" (Typed.print_variable x) ;
            assert false

(* Constants *)
and tcConst (inState : state) (lclCtxt : TypingEnv.t) (c : Const.t) : tcValOutput =
  { outExpr  = Typed.Const c
  ; outType  = Types.type_const c
  ; outState = inState            (* Leave as is *)
  ; outSubst = Substitution.empty (* Empty subst *)
  }

(* Type-annotated Expressions *)
and tcAnnotated (inState : state) (lclCtxt : TypingEnv.t) ((e,ty) : Untyped.expression * Type.ty) : tcValOutput =
  failwith __LOC__ (* GEORGE: Planned TODO for the future I guess?? *)

(* Tuples *)
and tcTuple (inState : state) (lclCtxt : TypingEnv.t) (es : Untyped.expression list): tcValOutput =
  let res = tcManyVal inState lclCtxt es tcLocatedVal in
  { outExpr  = Typed.Tuple res.outExpr
  ; outType  = Types.Tuple res.outType
  ; outState = res.outState
  ; outSubst = res.outSubst
  }

(* Records *)
and tcRecord (inState : state) (lclCtx : TypingEnv.t) (lst : (field, Untyped.expression) Assoc.t)
      : tcValOutput =
  failwith __LOC__ (* GEORGE: Planned TODO for the future I guess?? *)

(* Variants *)
and tcVariant (inState : state) (lclCtx : TypingEnv.t) ((lbl,mbe) : label * Untyped.expression option)
      : tcValOutput =
  let ty_in, ty_out = Types.constructor_signature lbl in
  match mbe with
  | None -> { outExpr  = Typed.Variant (lbl, Typed.Tuple [])
            ; outType  = ty_out
            ; outState = inState
            ; outSubst = Substitution.empty }
  | Some e ->
      let res = tcLocatedVal inState lclCtx e in
      (* GEORGE: Investigate how cast_expression works *)
      let castExp, castCt = cast_expression res.outExpr res.outType ty_in in
      warnAddConstraints "tcVariant" [castCt];
      { outExpr  = Typed.Variant (lbl, castExp)
      ; outType  = ty_out
      ; outState = add_constraint castCt res.outState
      ; outSubst = res.outSubst
      }

(* Lambda Abstractions *)
and tcLambda (inState : state) (lclCtx : TypingEnv.t) (abs : Untyped.abstraction) : tcValOutput =
  let res = tcUntypedAbstraction inState lclCtx abs in
  let (trgPat,trgCmp) = res.outExpr in
  let (patTy,cmpTy)   = res.outType in
  { outExpr  = Typed.Lambda (abstraction_with_ty trgPat patTy trgCmp)
  ; outType  = Types.Arrow (patTy,cmpTy)
  ; outState = res.outState
  ; outSubst = res.outSubst }

(* Effects (GEORGE: Isn't this supposed to be in computations? *)
and tcEffect (inState : state) (lclCtx : TypingEnv.t) (eff : Untyped.effect) : tcValOutput =
  (* GEORGE: NOTE: This is verbatim copied from the previous implementation *)
  let in_ty, out_ty = Typed.EffectMap.find eff inState.effects in
  let s = Types.EffectSet.singleton eff in
  { outExpr  = Typed.Effect (eff, (in_ty, out_ty))
  ; outType  = Types.Arrow (in_ty, (out_ty, Types.closed_dirt s))
  ; outState = inState
  ; outSubst = Substitution.empty }

(* Handlers *)
and tcHandler (inState : state) (lclCtx : TypingEnv.t) (h : Untyped.handler) : tcValOutput =
  (* 0: Warn about the current state of the implementation *)
  Print.debug "Ignoring the finally_clause" ;

  (* 2: Generate fresh variables for the input and output types *)
  (* NOTE: We do pass these type variables inside when checking the clauses but
   * that is merely for ease of constraint construction; these variables are
   * not to be added to Q just yet (and so cannot be unified yet). *)
  let alphaIn, alphaInSkel = Typed.fresh_ty_with_fresh_skel () in
  let deltaIn = Types.fresh_dirt () in
  let alphaOut, alphaOutSkel = Typed.fresh_ty_with_fresh_skel () in
  let deltaOut = Types.fresh_dirt () in

  (* How to process the return clause *)
  let rec processReturnClause (tmpState : state) (tmpCtx : TypingEnv.t) (ret_case : Untyped.abstraction)
       : (Substitution.t ->        (* Sigma N *)
           abstraction_with_ty *   (* Elaborated return clause *)
           (state -> state)        (* Add omega1,omega2,omega6 to the state *)
         , unit)                   (* Bad abstraction on my part *)
         tcOutputs
    = let { outExpr  = (xR,cR)
          ; outType  = (alphaR, (betaR,deltaR))
          ; outState = state0
          ; outSubst = substR } = tcUntypedAbstraction tmpState tmpCtx ret_case in
      { outExpr  = ((* GEORGE: we do not support anything else at the moment *)
                    let x = (match xR with
                             | PVar x -> x
                             | _ -> failwith "processReturnClause: only varpats allowed") in
                    fun sub ->
                      let omega1, omegaCt1 = Typed.fresh_ty_coer (subInValTy sub betaR, alphaOut) in
                      let omega2, omegaCt2 = Typed.fresh_dirt_coer (subInDirt sub deltaR, deltaOut) in
                      let omega6, omegaCt6 = Typed.fresh_ty_coer (alphaIn, subInValTy sub alphaR) in
                      ( (* 1: the clause itself *)
                        let yvar = CoreTypes.Variable.fresh "y" in
                        let ysub = Typed.subst_comp (Assoc.of_list [(x, CastExp (Var yvar, omega6))]) in
                        (PVar yvar, subInValTy sub alphaR, Typed.CastComp (ysub (subInCmp sub cR), Typed.BangCoercion (omega1, omega2)))
                        (* 2: the constraints to add to the state *)
                      , ( warnAddConstraints "tcHandler[Ret]" [omegaCt1;omegaCt2;omegaCt6]
                        ; fun st -> st |> add_constraint omegaCt1
                                       |> add_constraint omegaCt2
                                       |> add_constraint omegaCt6
                        )
                      )
                   )
      ; outType  = ()
      ; outState = state0
      ; outSubst = substR }
  in

  (* How to process effect clauses *)
  let rec processOpClauses
            (tmpState : state)      (* Qi-1 *)
            (tmpCtx : TypingEnv.t)  (* sigmai-1 .. sigma0 (Gamma) *)
            (eclauses : (Untyped.effect, Untyped.abstraction2) Assoc.t) (* clauses... *)
    = match Assoc.isCons eclauses with
      | None -> { outExpr  = []
                ; outType  = () (* unit, useless field ==> we need a better representation (that's on me) *)
                ; outState = tmpState
                ; outSubst = Substitution.empty }
      | Some ((eff,abs2),clauses) ->
          (* Lookup the type of Opi *)
          let ai, bi = Typed.EffectMap.find eff tmpState.effects in

          (* Generate fresh variables for the typed of the codomain of the continuation *)
          let alphai, alphaiSkel = Typed.fresh_ty_with_fresh_skel () in
          let deltai = Types.fresh_dirt () in

          (* Typecheck the clause *)
          let { outExpr  = (xop,kop,trgCop)
              ; outType  = (xTy,kTy,(bOpi,deltaOpi))
              ; outState = statei
              ; outSubst = substi } = tcTypedAbstraction2 (tmpState |> add_constraint alphaiSkel) tmpCtx abs2 ai (Types.Arrow (bi, (alphai,deltai))) in

          (* Process the rest recursively *)
          let xsres = processOpClauses statei (subInEnv substi tmpCtx) clauses in

          (* Create the target clause *)
          let omega3i, omegaCt3i = Typed.fresh_ty_coer (subInValTy xsres.outSubst bOpi, alphaOut) in
          let omega4i, omegaCt4i = Typed.fresh_dirt_coer (subInDirt xsres.outSubst deltaOpi, deltaOut) in
          let omega5i, omegaCt5i = Typed.fresh_ty_coer (Types.Arrow (bi, (alphaOut,deltaOut)), subInValTy xsres.outSubst kTy) in

          (* GEORGE: we do not support anything else at the moment *)
          let k = (match kop with
                   | PVar k -> k
                   | _ -> failwith "processOpClauses: only varpats allowed") in
          let lvar = CoreTypes.Variable.fresh "l" in
          let lsub = Typed.subst_comp (Assoc.of_list [(k, CastExp (Var lvar, omega5i))]) in

          let trgClause = ( ((eff,(ai,bi)) : Typed.effect) (* Opi *)
                          , (xop, PVar lvar, CastComp (lsub (subInCmp xsres.outSubst trgCop), Typed.BangCoercion (omega3i,omega4i)))
                          ) in

          { outExpr  = trgClause :: xsres.outExpr
          ; outType  = ()
          ; outState = ( warnAddConstraints "tcHandler[Op]" [omegaCt3i;omegaCt4i;omegaCt5i]
                       ; xsres.outState
                           |> add_constraint omegaCt3i
                           |> add_constraint omegaCt4i
                           |> add_constraint omegaCt5i
                       )
          ; outSubst = extendGenSub substi xsres.outSubst (* Compose the substitutions *)
          }
  in

  (* Process all the clauses *)
  let retRes = processReturnClause inState lclCtx h.value_clause in
  let clsRes = processOpClauses retRes.outState (subInEnv retRes.outSubst lclCtx) h.effect_clauses in

  let omega7, omegaCt7 =
    let allOps = Types.EffectSet.of_list (List.map (fun ((eff, _), _) -> eff) clsRes.outExpr) in

    (* GEORGE: Unsafely match against deltaOut to get a representation as a dirt variable *)
    let deltaOutVar = (match deltaOut with
                       | Types.{effect_set=_;row=ParamRow deltaOutVar} ->
                           deltaOutVar
                       | Types.{effect_set=_;row=EmptyRow} ->
                           failwith "deltaOut: IMPOSSIBLE") in

    Typed.fresh_dirt_coer (deltaIn, Types.{effect_set = allOps; row= ParamRow deltaOutVar})
  in

  warnAddConstraints "tcHandler[7,in,out]" [omegaCt7;alphaInSkel;alphaOutSkel];

  let retClause,state_fn = retRes.outExpr clsRes.outSubst in

  let handlerCo = Typed.HandlerCoercion ( Typed.BangCoercion (Typed.ReflTy alphaIn, omega7)
                                        , Typed.BangCoercion (Typed.ReflTy alphaOut, Typed.ReflDirt deltaOut) ) in
  Print.debug "I am the HandlerCo : %t" (Typed.print_ty_coercion handlerCo) ;

  { outExpr  = CastExp ( Handler ({ effect_clauses = Assoc.of_list clsRes.outExpr
                                  ; value_clause   = retClause  })
                       , handlerCo )
  ; outType  = Types.Handler ((alphaIn, deltaIn), (alphaOut, deltaOut))
  ; outState = state_fn clsRes.outState            (* 3i, 4i, 5i && 1, 2, 6 *)
                 |> add_constraint omegaCt7        (* 7 *)
                 |> add_constraint alphaInSkel     (* ain : skelin *)
                 |> add_constraint alphaOutSkel    (* aout : skelout *)
  ; outSubst = extendGenSub retRes.outSubst clsRes.outSubst
  }

(* Dispatch: Type inference for a plain value (expression) *)
and tcVal (inState : state) (lclCtx : TypingEnv.t) : Untyped.plain_expression -> tcValOutput = function
  | Untyped.Var x              -> (* showInputEnv "Var" lclCtx; showInputCs "Var" inState; *)
                                  tcVar       inState lclCtx x
  | Untyped.Const c            -> (* showInputEnv "Const" lclCtx; showInputCs "Const" inState; *)
                                  tcConst     inState lclCtx c
  | Untyped.Annotated (e,ty)   -> (* showInputEnv "Annotated" lclCtx; showInputCs "Annotated" inState; *)
                                  tcAnnotated inState lclCtx (e,ty)
  | Untyped.Tuple es           -> (* showInputEnv "Tuple" lclCtx; showInputCs "Tuple" inState; *)
                                  tcTuple     inState lclCtx es
  | Untyped.Record lst         -> (* showInputEnv "Record" lclCtx; showInputCs "Record" inState; *)
                                  tcRecord    inState lclCtx lst
  | Untyped.Variant (lbl,mbe)  -> (* showInputEnv "Variant" lclCtx; showInputCs "Variant" inState; *)
                                  tcVariant   inState lclCtx (lbl,mbe)
  | Untyped.Lambda abs         -> (* showInputEnv "Lambda" lclCtx; showInputCs "Lambda" inState; *)
                                  tcLambda    inState lclCtx abs
  | Untyped.Effect eff         -> (* showInputEnv "Effect" lclCtx; showInputCs "Effect" inState; *)
                                  tcEffect    inState lclCtx eff
  | Untyped.Handler hand       -> (* showInputEnv "Handler" lclCtx; showInputCs "Handler" inState; *)
                                  tcHandler   inState lclCtx hand

(* Type inference for a located value (expression) *)
and tcLocatedVal (inState : state) (lclCtx : TypingEnv.t) (e : Untyped.expression) : tcValOutput
  = tcVal inState lclCtx e.it

(* ************************************************************************* *)
(*                          COMPUTATION TYPING                               *)
(* ************************************************************************* *)

(* Dispatch: Type inference for a plan computation *)
and tcCmp (inState : state) (lclCtx : TypingEnv.t) : Untyped.plain_computation -> tcCmpOutput = function
  | Value exp                -> tcValue  inState lclCtx exp

  (* Nest a list of let-bindings *)
  | Let ([],c2)               -> tcLocatedCmp inState lclCtx c2
  | Let ([(pat,c1)],c2)       -> tcLet    inState lclCtx pat c1 c2
  | Let ((pat,c1) :: rest,c2) -> let subCmp = {it = Untyped.Let (rest, c2); at = c2.at} in
                                 tcCmp inState lclCtx (Untyped.Let ([(pat, c1)], subCmp))

  (* Nest a list of letrec-bindings; mutual recursion not allowed *)
  | LetRec ([],c2)                -> tcLocatedCmp inState lclCtx c2
  | LetRec ([(var,abs)],c2)       -> tcLetRecNoGen inState lclCtx var abs c2
  | LetRec ((var,abs) :: rest,c2) -> let subCmp = {it = Untyped.LetRec (rest,c2); at = c2.at} in
                                     tcCmp inState lclCtx (Untyped.LetRec ([(var,abs)], subCmp))

  (* GEORGE:TODO: Deal with pattern matching properly *)
  | Match (scr, [ ({it = Untyped.PConst (Boolean true )}, c1)
                ; ({it = Untyped.PConst (Boolean false)}, c2) ] )
      -> tcIfThenElse inState lclCtx scr c1 c2
  | Match (scr, [(p,c)]) -> let tmp = { it = Untyped.Value scr ; at = p.at } (* { it = Untyped.Value scr.it ; at = scr.at } *)
                            in  tcCmp inState lclCtx (Untyped.Let ([(p,tmp)],c))
  | Match (scr, cases)       -> failwith __LOC__
                                (* tcMatch  inState lclCtx scr cases (* GEORGE: TODO: Bogus right now? *) *)

  | Apply (val1, val2)       -> tcApply  inState lclCtx val1 val2
  | Handle (hand, cmp)       -> tcHandle inState lclCtx hand cmp
  | Check cmp                -> tcCheck  inState lclCtx cmp

(* Type inference for a located computation *)
and tcLocatedCmp (inState : state) (lclCtx : TypingEnv.t) (c : Untyped.computation) : tcCmpOutput
  = tcCmp inState lclCtx c.it

(* Typecheck a value wrapped in a return *)
and tcValue (inState : state) (lclCtxt : TypingEnv.t) (exp : Untyped.expression) : tcCmpOutput =
  let res = tcLocatedVal inState lclCtxt exp in
  { outExpr  = Typed.Value res.outExpr
  ; outType  = (res.outType, Types.empty_dirt)
  ; outState = res.outState
  ; outSubst = res.outSubst }

(* Typecheck a let where c1 is a value *)
and tcLetValNoGen (inState : state) (lclCtxt : TypingEnv.t)
      (patIn : Untyped.pattern)
      (e1 : Untyped.expression)
      (c2 : Untyped.computation) : tcCmpOutput =
  (* 1: Typecheck e1 *)
  let { outExpr  = trgE1
      ; outType  = tyA1
      ; outState = state1
      ; outSubst = sigma1
      } = tcLocatedVal inState lclCtxt e1 in (* (v',A, Qv, Sigma1) *)

  (* 2: Typecheck c2 *)
  let x = (match patIn.it with
           | Untyped.PVar x -> x (* GEORGE: Support nothing else at the moment *)
           | _ -> failwith "tcLetValNoGen: only varpats allowed") in
  let { outExpr  = trgC2
      ; outType  = (tyB2,dirtD2)
      ; outState = state2
      ; outSubst = sigma2
      } = tcLocatedCmp
            state1
            (extendLclCtxt (subInEnv sigma1 lclCtxt) x tyA1)
            c2 in

  (* 3: Combine the results *)
  { outExpr  = Typed.LetVal
                 ( subInExp sigma2 trgE1
                 , Typed.abstraction_with_ty (Typed.PVar x) (subInValTy sigma2 tyA1) trgC2 )
  ; outType  = (tyB2,dirtD2)
  ; outState = state2
  ; outSubst = extendGenSub sigma1 sigma2
  }

(* Typecheck a let when c1 is a computation (== do binding) *)
and tcLetCmp (inState : state) (lclCtxt : TypingEnv.t) (pdef : Untyped.pattern) (c1 : Untyped.computation) (c2 : Untyped.computation) : tcCmpOutput =
  let c1res = tcLocatedCmp inState lclCtxt c1 in (* typecheck c1 *)
  (* {outExpr = c1'; outType = (A1,D1); outState = state1; outSubst = sigma1} *)
  let c2res = tcTypedAbstraction c1res.outState (subInEnv c1res.outSubst lclCtxt) (pdef, c2) (fst c1res.outType) in
  (* {outExpr = (pat',c2'); outType = (s2(A1),(A2,D2)); outState = state2; outSubst = sigma2} *)

  let delta = Types.fresh_dirt () in
  let omega1, omegaCt1 = Typed.fresh_dirt_coer (subInDirt c2res.outSubst (snd c1res.outType), delta) in (* s2(D1) <= delta *)
  let omega2, omegaCt2 = Typed.fresh_dirt_coer (snd (snd c2res.outType), delta)                      in (*    D2  <= delta *)

  let cresC1 = CastComp
                 ( (subInCmp c2res.outSubst c1res.outExpr)
                 , Typed.BangCoercion
                     ( Typed.ReflTy (subInValTy c2res.outSubst (fst c1res.outType))
                     , omega1
                     )
                 ) in

  let cresAbs = ( fst c2res.outExpr
                , CastComp
                    ( snd c2res.outExpr
                    , Typed.BangCoercion
                        ( Typed.ReflTy (fst (snd c2res.outType))
                        , omega2
                        )
                    )
                 ) in

  warnAddConstraints "tcLetCmp" [omegaCt1;omegaCt2];

  { outExpr  = Typed.Bind (cresC1, cresAbs)
  ; outType  = (fst (snd c2res.outType),delta)
  ; outState = c2res.outState
                 |> add_constraint omegaCt1
                 |> add_constraint omegaCt2
  ; outSubst = extendGenSub c1res.outSubst c2res.outSubst }

(* Typecheck a non-recursive let *)
and tcLet (inState : state) (lclCtxt : TypingEnv.t) (pdef : Untyped.pattern) (c1 : Untyped.computation) (c2 : Untyped.computation) : tcCmpOutput =
  match c1.it with
  | Untyped.Value e1   -> tcLetValNoGen inState lclCtxt pdef e1 c2
  | _other_computation -> tcLetCmp inState lclCtxt pdef c1 c2

(* Typecheck a (potentially) recursive let *)
and tcLetRecNoGen (inState : state) (lclCtxt : TypingEnv.t)
      (var : Untyped.variable)
      (abs : Untyped.abstraction)
      (c2 : Untyped.computation) : tcCmpOutput =

  (* 1: Generate fresh variables for everything *)
  let alpha, alphaSkel = fresh_ty_with_fresh_skel () in
  let beta , betaSkel  = fresh_ty_with_fresh_skel () in
  let delta = Types.fresh_dirt () in

  (* 2: Typecheck the abstraction *)
  let { outExpr  = (trgPat, trgC1)
      ; outType  = (trgPatTy,(tyA1, dirtD1))
      ; outState = state1
      ; outSubst = sigma1
      } = tcTypedAbstraction
            (inState |> add_constraint alphaSkel |> add_constraint betaSkel)
            (extendLclCtxt lclCtxt var (Types.Arrow (alpha, (beta, delta))))
            abs alpha in

  (* 3: Typecheck c2 *)
  let { outExpr  = trgC2
      ; outType  = (tyA2, dirtD2)
      ; outState = state2
      ; outSubst = sigma2
      } = tcLocatedCmp
            state1
            (extendLclCtxt (lclCtxt |> subInEnv sigma1) var (Types.Arrow (subInValTy sigma1 alpha, (tyA1,dirtD1))))
            c2
  in

  (* 3: The assumed type should be at least as general as the inferred one *)
  let omega1, omegaCt1 = Typed.fresh_ty_coer (subInValTy sigma2 tyA1, subInValTy sigma2 (subInValTy sigma1 beta)) in
  let omega2, omegaCt2 = Typed.fresh_dirt_coer (subInDirt sigma2 dirtD1, subInDirt sigma2 (subInDirt sigma1 delta)) in

  (* 4: Create the (complicated) c1''. *)
  let c1'' = (
    let f_coercion = Typed.ArrowCoercion
                       ( Typed.ReflTy (subInValTy sigma2 (subInValTy sigma1 alpha))
                       , Typed.BangCoercion (omega1, omega2)
                       ) in
    let subst_fn   = Typed.subst_comp (Assoc.of_list [(var, Typed.CastExp(Typed.Var var, f_coercion))]) in

    subst_fn (subInCmp sigma2 trgC1)
  ) in

  (* 5: Create the (monomorphic) type of f *)
  let ftype = subInValTy sigma2 (Types.Arrow (subInValTy sigma1 alpha, (tyA1, dirtD1))) in

  (* 6: Create the generated term *)
  let genTerm = Typed.Lambda
                  (Typed.abstraction_with_ty
                     trgPat
                     (subInValTy sigma2 (subInValTy sigma1 trgPatTy))
                     c1''
                  ) in

  (* 7: Combine the results *)
  { outExpr  = Typed.LetRec ([(var, ftype, genTerm)], trgC2)
  ; outType  = (tyA2, dirtD2)
  ; outState = state2 |> add_constraint omegaCt1 |> add_constraint omegaCt2
  ; outSubst = extendGenSub sigma1 sigma2
  }

and tcIfThenElse (inState : state) (lclCtxt : TypingEnv.t)
      (scr : Untyped.expression)
      (trueC  : Untyped.computation)
      (falseC : Untyped.computation) : tcCmpOutput =

  (* 1: Generate fresh variables for the result *)
  let alphaOut, alphaOutSkel = fresh_ty_with_fresh_skel () in
  let deltaOut = Types.fresh_dirt () in

  (* 2: Typecheck everything *)
  let scrRes = tcLocatedVal inState lclCtxt scr in
  let truRes = tcLocatedCmp scrRes.outState (subInEnv scrRes.outSubst lclCtxt) trueC in
  let flsRes = tcLocatedCmp truRes.outState (subInEnv truRes.outSubst (subInEnv scrRes.outSubst lclCtxt)) falseC in

  (* 3: Create the new constraints *)
  let tyAtru,dirtDtru = truRes.outType in
  let tyAfls,dirtDfls = flsRes.outType in
  let omega1, omegaCt1 = Typed.fresh_ty_coer (subInValTy flsRes.outSubst tyAtru, alphaOut) in
  let omega2, omegaCt2 = Typed.fresh_dirt_coer (subInDirt flsRes.outSubst dirtDtru, deltaOut) in
  let omega3, omegaCt3 = Typed.fresh_ty_coer (fst flsRes.outType, alphaOut) in
  let omega4, omegaCt4 = Typed.fresh_dirt_coer (snd flsRes.outType, deltaOut) in
  let omega0, omegaCt0 = Typed.fresh_ty_coer ( subInValTy flsRes.outSubst
                                                 (subInValTy truRes.outSubst scrRes.outType)
                                             , Types.type_const Const.of_true ) in (* Bool *)

  (* 4: Create the resulting expression *)
  let trgCmp = (
    let trgScr = Typed.CastExp ( scrRes.outExpr
                                 |> subInExp truRes.outSubst
                                 |> subInExp flsRes.outSubst
                               , omega0 ) in
    let trgTruRhs = Typed.CastComp ( subInCmp flsRes.outSubst truRes.outExpr
                                   , Typed.BangCoercion (omega1, omega2) ) in
    let trgFlsRhs = Typed.CastComp ( flsRes.outExpr
                                   , Typed.BangCoercion (omega3, omega4) ) in
    Typed.Match
      ( trgScr
      , [ (Typed.PConst Const.of_true , trgTruRhs)
        ; (Typed.PConst Const.of_false, trgFlsRhs)
        ]
      )
  ) in

  warnAddConstraints "tcIfThenElse" [alphaOutSkel; omegaCt1; omegaCt2; omegaCt3; omegaCt4; omegaCt0];

  (* 5: Combine the results *)
  { outExpr  = trgCmp
  ; outType  = (alphaOut, deltaOut)
  ; outState = flsRes.outState
               |> add_constraint alphaOutSkel
               |> add_constraint omegaCt1
               |> add_constraint omegaCt2
               |> add_constraint omegaCt3
               |> add_constraint omegaCt4
               |> add_constraint omegaCt0
  ; outSubst = extendGenSub
                 (extendGenSub scrRes.outSubst truRes.outSubst)
                 flsRes.outSubst
  }

(* Typecheck a case expression *)
(* GEORGE: There are multiple ways to typecheck a case expression, depending on
 * what semantics one wants. We choose this for now cause it is easier to
 * implement *)
and tcMatch (inState : state) (lclCtxt : TypingEnv.t) (scr : Untyped.expression) (cases : Untyped.abstraction list) : tcCmpOutput =
  (* 1: Typecheck the scrutinee *)
  let resScr = tcLocatedVal inState lclCtxt scr in

  (* 2: Generate fresh variables for the result *)
  let alphaOut, alphaOutSkel = fresh_ty_with_fresh_skel () in
  let deltaOut = Types.fresh_dirt () in

  (* 3: How to typecheck the clauses *)
  let rec tcMatchCases (tmpState : state) (tmpCtxt : TypingEnv.t) (clauses : Untyped.abstraction list) = (
    match clauses with
    | [] -> { outExpr  = None
            ; outType  = () (* () *)
            ; outState = tmpState
            ; outSubst = Substitution.empty
            }
    | (pat,rhs) :: clauses ->
        (* Infer a type for the pattern *)
        let trgPat,patTy,extState,extCtxt = inferLocatedPatTy tmpState tmpCtxt pat in
        (* Typecheck the right-hand side *)
        let resRhs = tcLocatedCmp extState extCtxt rhs in
        (* Typecheck the rest of the clauses *)
        let resRest = tcMatchCases resRhs.outState (subInEnv resRhs.outSubst tmpCtxt) clauses in

        (* Create the target clause *)
        let tyBi, dirtDi = resRhs.outType in

        let omegaOutLeft, omegaOutLeftCt = Typed.fresh_ty_coer (subInValTy resRest.outSubst tyBi, alphaOut) in
        let omegaOutRight, omegaOutRightCt = Typed.fresh_dirt_coer (subInDirt resRest.outSubst dirtDi, deltaOut) in
        let omegaIn, omegaInCt = Typed.fresh_ty_coer
                                   ( subInValTy resRest.outSubst
                                       (subInValTy resRhs.outSubst resScr.outType)
                                   , subInValTy resRest.outSubst patTy) in

        let trgClause = (
          let scrutinee = Typed.CastExp
                            ( resScr.outExpr
                                |> subInExp resRhs.outSubst
                                |> subInExp resRest.outSubst
                            , omegaIn
                            ) in

          let firstClause = ( trgPat
                            , Typed.CastComp ( subInCmp resRest.outSubst resRhs.outExpr
                                             , Typed.BangCoercion (omegaOutLeft, omegaOutRight)
                                             )
                            ) in

          let nextClauses = (match resRest.outExpr with
                             | None   -> []
                             | Some c -> [(Typed.PNonbinding, c)]
                            ) in

          Typed.Match (scrutinee, firstClause :: nextClauses)
        ) in

        (* Combine the results *)
        { outExpr  = Some trgClause
        ; outType  = () (* () : GEORGE's BAD MODELLING *)
        ; outState = resRest.outState
                       |> add_constraint omegaOutLeftCt
                       |> add_constraint omegaOutRightCt
                       |> add_constraint omegaInCt
        ; outSubst = extendGenSub resRhs.outSubst resRest.outSubst (* Compose the substitutions *)
        }
  ) in

  (* 4: Actually typecheck the clauses (GEORGE: Awful name; change it) *)
  let almostThere = tcMatchCases resScr.outState (subInEnv resScr.outSubst lclCtxt) cases in

  let finalComputation = (match almostThere.outExpr with
       | None -> Typed.Match (resScr.outExpr, []) (* Only if alternative list is empty *)
       | Some c -> c ) in

  { outExpr  = finalComputation
  ; outType  = (alphaOut, deltaOut)
  ; outState = almostThere.outState |> add_constraint alphaOutSkel
  ; outSubst = extendGenSub resScr.outSubst almostThere.outSubst
  }

(* Typecheck a function application *)
and tcApply (inState : state) (lclCtxt : TypingEnv.t) (val1 : Untyped.expression) (val2 : Untyped.expression) : tcCmpOutput =
  (* Infer the types of val1 and val2 *)
  let res1 = tcLocatedVal inState lclCtxt val1 in
  let res2 = tcLocatedVal res1.outState (subInEnv res1.outSubst lclCtxt) val2 in

  (* Generate fresh variables for the result *)
  let alpha, alpha_skel = Typed.fresh_ty_with_fresh_skel () in
  let delta = Types.fresh_dirt () in

  (* Create the constraint and the cast elaborated expression *)
  let omega, omegaCt = Typed.fresh_ty_coer ( subInValTy res2.outSubst res1.outType
                                           , Types.Arrow (res2.outType, (alpha,delta)) ) in
  let castVal1 = Typed.CastExp (subInExp res2.outSubst res1.outExpr, omega) in

  warnAddConstraints "tcApply" [alpha_skel; omegaCt];
  { outExpr  = Typed.Apply (castVal1, res2.outExpr)
  ; outType  = (alpha, delta)
  ; outState = res2.outState |> add_constraint alpha_skel |> add_constraint omegaCt
  ; outSubst = extendGenSub res1.outSubst res2.outSubst
  }

(* Typecheck a handle-computation *)
and tcHandle (inState : state) (lclCtxt : TypingEnv.t) (hand : Untyped.expression) (cmp : Untyped.computation) : tcCmpOutput =

  let res1 = tcLocatedVal inState lclCtxt hand in                                (* Typecheck the handler *)
  let res2 = tcLocatedCmp res1.outState (subInEnv res1.outSubst lclCtxt) cmp in  (* Typecheck the computation *)

  let dirty_1, cons_skel_1 = Typed.fresh_dirty_with_fresh_skel () in
  let dirty_2, cons_skel_2 = Typed.fresh_dirty_with_fresh_skel () in

  let castHand, omega_cons_1 =
    Typed.cast_expression
      (subInExp   res2.outSubst res1.outExpr)
      (subInValTy res2.outSubst res1.outType)
      (Types.Handler (dirty_1, dirty_2)) in

  let castComp, omega_cons_23 =
     Typed.cast_computation res2.outExpr res2.outType dirty_1 in

  { outExpr  = Typed.Handle (castHand, castComp)
  ; outType  = dirty_2
  ; outState = res2.outState
               |> add_constraint cons_skel_1
               |> add_constraint cons_skel_2
               |> add_constraint omega_cons_1
               |> add_constraint omega_cons_23
  ; outSubst = extendGenSub res1.outSubst res2.outSubst }

(* Typecheck a "Check" expression (GEORGE does not know what this means yet *)
and tcCheck (inState : state) (lclCtxt : TypingEnv.t) (cmp : Untyped.computation) : tcCmpOutput =
  failwith __LOC__ (* GEORGE: Planned TODO for the future I guess?? *)

(* ************************************************************************* *)
(*                               UTILITIES                                   *)
(* ************************************************************************* *)

(* Type any kind of binding structure (e.g. \x. c) *)
(* GEORGE: This is "equivalent" of "type_abstraction" *)
and tcUntypedAbstraction (inState : state) (lclCtx : TypingEnv.t) (pat,cmp) =
  (* Typecheck the pattern *)
  let trgPat, patTy, midState, midLclCtx = tcLocatedPat inState lclCtx pat in
  (* Typecheck the computation in the extended environment *)
  let res = tcLocatedCmp midState midLclCtx cmp in
  { outExpr  = (trgPat, res.outExpr)
  ; outType  = (subInValTy res.outSubst patTy, res.outType)
  ; outState = res.outState
  ; outSubst = res.outSubst
  }

and tcTypedAbstraction (inState : state) (lclCtx : TypingEnv.t) (pat,cmp) patTy =
  (* Typecheck the pattern *)
  let trgPat, _, midState, midLclCtx = tcLocatedTypedPat inState lclCtx pat patTy in
  (* Typecheck the computation in the extended environment *)
  let res = tcLocatedCmp midState midLclCtx cmp in
  { outExpr  = (trgPat, res.outExpr)
  ; outType  = (subInValTy res.outSubst patTy, res.outType)
  ; outState = res.outState
  ; outSubst = res.outSubst
  }

and tcTypedAbstraction2 (inState : state) (lclCtx : TypingEnv.t) (pat1,pat2,cmp) patTy1 patTy2 =
  (* Typecheck the first pattern *)
  let trgPat1, _, midState1, midLclCtx1 = tcLocatedTypedPat inState lclCtx pat1 patTy1 in
  (* Typecheck the second pattern *)
  let trgPat2, _, midState2, midLclCtx2 = tcLocatedTypedPat midState1 midLclCtx1 pat2 patTy2 in
  (* Typecheck the computation in the extended environment *)
  let res = tcLocatedCmp midState2 midLclCtx2 cmp in
  { outExpr  = (trgPat1, trgPat2, res.outExpr)
  ; outType  = (subInValTy res.outSubst patTy1, subInValTy res.outSubst patTy2, res.outType)
  ; outState = res.outState
  ; outSubst = res.outSubst
  }

(* ************************************************************************* *)
(* ************************************************************************* *)

(* Finalize a list of constraints, setting all dirt variables to the empty set. *)

let finalize_constraint sub ct =
  match ct with
  | Typed.TyOmega (tcp, ctty) ->
      Error.typing ~loc:Location.unknown
        "Unsolved type inequality in top-level computation: %t"
        (Typed.print_omega_ct (Typed.TyOmega (tcp, ctty)))
  | Typed.DirtOmega
      ( dcp
      , ( {Types.effect_set= s1; Types.row= row1}
        , {Types.effect_set= s2; Types.row= row2} ) ) ->
      assert (Types.EffectSet.subset s1 s2) ;
      let sub' = Substitution.add_dirt_var_coercion dcp (Typed.UnionDirt
              (s1, Typed.Empty (Types.closed_dirt (Types.EffectSet.diff s2 s1)))) sub in
      let subs'' =
        match (row1, row2) with
        | Types.EmptyRow, Types.ParamRow dv2 ->
            Substitution.add_dirt_substitution dv2 Types.empty_dirt sub'
        | Types.ParamRow dv1, Types.EmptyRow ->
            Substitution.add_dirt_substitution dv1 Types.empty_dirt sub'
        | Types.ParamRow dv1, Types.ParamRow dv2 ->
            Substitution.add_dirt_substitution dv1 Types.empty_dirt sub' |>
            Substitution.add_dirt_substitution dv2 Types.empty_dirt
        | Types.EmptyRow, Types.EmptyRow -> sub'
      in
      subs''
  | Typed.SkelEq (sk1, sk2) -> failwith __LOC__
  | Typed.TyParamHasSkel (tp, sk) ->
      Error.typing ~loc:Location.unknown
        "Unsolved param-has-skel constraint in top-level computation: %t"
        (Typed.print_omega_ct (Typed.TyParamHasSkel (tp, sk)))
  | Typed.DirtyOmega ((_,_),_) -> failwith __LOC__ (* GEORGE: I think this is unused *)

let finalize_constraints c_list = List.fold_left (fun subs ct -> finalize_constraint subs ct) Substitution.empty c_list

(* GEORGE: Document *)
let mkCmpDirtGroundSubst cmp =
  List.fold_left
    (fun subs dp -> Substitution.add_dirt_substitution dp Types.empty_dirt subs)
    Substitution.empty
    (Types.DirtParamSet.elements (free_dirt_vars_computation cmp))

(* Typecheck a top-level expression *)
let tcTopLevel ~loc inState cmp =
  Print.debug "tcTopLevel [0]: %t" (Untyped.print_computation cmp) ;
  (* 1: Constraint generation *)
  let { outExpr  = trgCmp
      ; outType  = (ttype,dirt)
      ; outState = tmpState
      ; outSubst = tmpSubst } = tcLocatedCmp inState initial_lcl_ty_env cmp in

  Print.debug "tcTopLevel [1]: INFERRED (BEFORE SUBST): %t" (Types.print_target_dirty (ttype,dirt)) ;

  Print.debug "tcTopLevel [1]: ELABORATED COMP (BEFORE SUBST): %t" (Typed.print_computation trgCmp) ;

  (* 2: Constraint solving *)
  let solverSigma, residualCs = (
    (* A: Solve the constraints as they are *)
    let initialSigma, initialResiduals = Unification.unify (Substitution.empty, [], tmpState.constraints) in
    (* B: Ground the free skeleton variables *)
    let skelGroundResiduals = List.map
                                (function
                                 | TyParamHasSkel (tyvar,Types.SkelParam s) ->
                                     TyParamHasSkel (tyvar,Types.SkelTuple [])
                                 | TyParamHasSkel (tyvar,skel) ->
                                     Error.typing ~loc:Location.unknown
                                       "[1] Unsolved param-has-skel constraint in top-level computation: %t"
                                       (Typed.print_omega_ct (Typed.TyParamHasSkel (tyvar, skel)))
                                 | ct -> ct
                                ) initialResiduals in
    (* C: Solve again *)
    let secondSigma, secondResiduals = Unification.unify (Substitution.empty, [], skelGroundResiduals) in
    (* Combine the results *)
    (extendGenSub initialSigma secondSigma, secondResiduals)
  ) in

  Print.debug "tcTopLevel [2]: INFERRED (AFTER  SUBST): %t" (Types.print_target_dirty (subInCmpTy solverSigma (ttype,dirt))) ;

  Print.debug "tcTopLevel [2]: RESIDUAL CONSTRAINTS:"; Unification.print_c_list residualCs ;

  (* 3: Substitute back into the elaborated expression *)
  let ct' = subInCmp solverSigma trgCmp in

  (* 4: Create the dirt-grounding substitution *)
  let dirtZonker = mkCmpDirtGroundSubst (subInCmp solverSigma trgCmp) in

  (* 5: Zonk and finalize the residual constraints *)
  let sub3 = Substitution.apply_substitutions_to_constraints dirtZonker residualCs
               |> finalize_constraints in

  let targetComputation =
    trgCmp
      |> subInCmp solverSigma (* Solver's result *)
      |> subInCmp dirtZonker  (* Dirt-zonker's result *)
      |> subInCmp sub3 in     (* georgeTODO *)

  Print.debug "ELABORATED COMP (COMPLETE): %t" (Typed.print_computation targetComputation) ;

  ( targetComputation
  , inState (* Untouched! *)
  )

(* Add an external binding to the typing environment *)
let addExternal ctx x ty = { ctx with gblCtxt = TypingEnv.update ctx.gblCtxt x ty }
