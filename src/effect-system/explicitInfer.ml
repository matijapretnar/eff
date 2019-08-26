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

(* [STATE] INFERENCE STATE *)

type state =
  { gblCtxt: TypingEnv.t                                            (* Global Typing Environment *)
  ; effects: (Types.target_ty * Types.target_ty) Typed.EffectMap.t  (* Valid Effects             *)
  }

(* A bag/list of constraints *)
type constraints = Typed.omega_ct list;;

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
                  = { gblCtxt = TypingEnv.empty
                    ; effects = Typed.EffectMap.empty
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
(*                     LET-GENERALIZATION UTILITIES                          *)
(* ************************************************************************* *)

(* GEORGE: Shall we use filter_map? That would bump the requirements for
 * installation (OCaml 4.08.0). Also, I would suggest adding more checks here;
 * only a few kinds of constraints are expected after constraint solving. *)
let partitionResidualCs : Typed.omega_ct list
                        -> ( (CoreTypes.TyParam.t * CoreTypes.SkelParam.t) list
                           * (CoreTypes.TyCoercionParam.t * Types.ct_ty) list
                           * (CoreTypes.DirtCoercionParam.t * Types.ct_dirt) list )
   = let rec aux = function
       | [] -> ([],[],[])
       | (Typed.TyParamHasSkel (a,Types.SkelParam s)) :: rest ->
           let alphaSkels, tyCs, dirtCs = aux rest
           in  ((a,s) :: alphaSkels, tyCs, dirtCs)
       | (TyOmega (o,ct)) :: rest ->
           let alphaSkels, tyCs, dirtCs = aux rest
           in  (alphaSkels, (o,ct) :: tyCs, dirtCs)
       | (DirtOmega (o,ct)) :: rest ->
           let alphaSkels, tyCs, dirtCs = aux rest
           in  (alphaSkels, tyCs, (o,ct) :: dirtCs)
       | cs -> failwith "partitionResidualCs: malformed"
     in aux

(* Detect the components to abstract over from the residual constraints. To be
 * used in let-generalization. *)
(* GEORGE NOTE: We might have "dangling" dirt variables at the end. In the end
 * check whether this is the case and if it is compute the dirt variables from
 * the elaborated expression and pass them in. *)
let mkGenParts (cs : Typed.omega_ct list)
  : ( CoreTypes.SkelParam.t list
    * (CoreTypes.TyParam.t * Types.skeleton) list
    * CoreTypes.DirtParam.t list
    * (CoreTypes.TyCoercionParam.t   * Types.ct_ty)   list
    * (CoreTypes.DirtCoercionParam.t * Types.ct_dirt) list)
  = let alphasSkelVars, tyCs, dirtCs = partitionResidualCs cs in
    let skelVars = alphasSkelVars
                   |> List.map snd                   (* Keep only the skeleton variables *)
                   |> Types.SkelParamSet.of_list     (* Convert to a set *)
                   |> Types.SkelParamSet.elements in (* Convert back to a list *)

    let alphaSkels = List.map (fun (a,s) -> (a, Types.SkelParam s)) alphasSkelVars in
    let dirtVars   = List.fold_right
                       (fun ct dvs -> Types.DirtParamSet.union (fdvsOfOmegaCt ct) dvs)
                       cs Types.DirtParamSet.empty
                     |> Types.DirtParamSet.elements in
    (*let tyDirtVars  = Types.fdvsOfTargetValTy valTy in (* fv(A) *) *)
    (skelVars, alphaSkels, dirtVars, tyCs, dirtCs)

(* Create a generalized type from parts (as delivered from "mkGenParts"). *)
let mkGeneralizedType
    (freeSkelVars  : CoreTypes.SkelParam.t list)
    (annFreeTyVars : (CoreTypes.TyParam.t * Types.skeleton) list)
    (freeDirtVars  : CoreTypes.DirtParam.t list)
    (tyCs   : (CoreTypes.TyCoercionParam.t   * Types.ct_ty)   list)
    (dirtCs : (CoreTypes.DirtCoercionParam.t * Types.ct_dirt) list)
    (monotype : Types.target_ty) (* expected to be a monotype! *)
  : Types.target_ty =
  monotype
  |> (* 1: Add the constraint abstractions (dirt) *)
     List.fold_right
       (fun (_,pi) qual -> Types.QualDirt (pi, qual))
       dirtCs
  |> (* 2: Add the constraint abstractions (type) *)
     List.fold_right
       (fun (_,pi) qual -> Types.QualTy (pi, qual))
       tyCs
  |> (* 3: Add the dirt variable abstractions *)
     List.fold_right
       (fun delta scheme -> Types.TySchemeDirt (delta, scheme))
       freeDirtVars
  |> (* 4: Add the type variable abstractions *)
     List.fold_right
       (fun (a,s) scheme -> Types.TySchemeTy (a, s, scheme))
       annFreeTyVars
  |> (* 5: Add the skeleton abstractions *)
     List.fold_right
       (fun skel scheme -> Types.TySchemeSkel (skel, scheme))
       freeSkelVars

(* Create a generalized term from parts (as delivered from "mkGenParts"). *)
(* GEORGE NOTE: We might have "dangling" dirt variables at the end. In the end
 * check whether this is the case and if it is compute the dirt variables from
 * the elaborated expression and pass them in. *)
let mkGeneralizedTerm
    (freeSkelVars  : CoreTypes.SkelParam.t list)
    (annFreeTyVars : (CoreTypes.TyParam.t * Types.skeleton) list)
    (freeDirtVars  : CoreTypes.DirtParam.t list)
    (tyCs   : (CoreTypes.TyCoercionParam.t   * Types.ct_ty)   list)
    (dirtCs : (CoreTypes.DirtCoercionParam.t * Types.ct_dirt) list)
    (exp : Typed.expression)
  : Typed.expression =
  exp
  |> (* 1: Add the constraint abstractions (dirt) *)
     List.fold_right
       (fun (omega,pi) qual -> Typed.LambdaDirtCoerVar (omega, pi, qual))
       dirtCs
  |> (* 2: Add the constraint abstractions (type) *)
     List.fold_right
       (fun (omega,pi) qual -> Typed.LambdaTyCoerVar (omega, pi, qual))
       tyCs
  |> (* 3: Add the dirt variable abstractions *)
     List.fold_right
       (fun delta e -> Typed.BigLambdaDirt (delta, e))
       freeDirtVars
  |> (* 4: Add the type variable abstractions *)
     List.fold_right
       (fun (a,s) e -> Typed.BigLambdaTy (a, s, e))
       annFreeTyVars
  |> (* 5: Add the skeleton abstractions *)
     List.fold_right
       (fun skel e -> Typed.BigLambdaSkel (skel, e))
       freeSkelVars

(* ************************************************************************* *)
(*                           BASIC DEFINITIONS                               *)
(* ************************************************************************* *)

(* Constraint generation output *)
type 'a tcOutput = ('a * constraints)

let rec mapAndUnzipTcOutputs (f : 'a -> 'b tcOutput)
  : 'a list -> ('b list) tcOutput = function
  | []      -> ([],[])
  | x :: xs -> let (y , cs1) = f x in
               let (ys, cs2) = mapAndUnzipTcOutputs f xs in
               (y :: ys, cs1 @ cs2)

(* Value typing output *)
type tcValOutput = (Typed.expression * Types.target_ty) tcOutput

(* Computation typing output *)
type tcCmpOutput = (Typed.computation * Types.target_dirty) tcOutput

(* Typecheck a list of things *)
let rec tcMany (inState : state) (lclCtxt : TypingEnv.t)
  (xss : 'a list) (tc : state -> TypingEnv.t -> 'a -> ('b * 'c) tcOutput)
  : ('b list * 'c list) tcOutput =
  match xss with
  | []      -> (([],[]),[])
  | x :: xs -> let ((y ,ty ),cs1) = tc inState lclCtxt x in
               let ((ys,tys),cs2) = tcMany inState lclCtxt xs tc in
               ((y :: ys, ty :: tys), cs1 @ cs2)

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
    (* Tuple Case *)
    | Untyped.PTuple pats ->
        (match patTy with
         | Types.Tuple tys -> let outPats, outCtxt = checkLocatedPatTys lclCtxt pats tys in
                              (Typed.PTuple outPats, outCtxt)
         | _ -> failwith "checkPatTy: PTuple")

    (* GEORGE: Not implemented yet cases *)
    | Untyped.PAs (p, v)         -> failwith __LOC__
    | Untyped.PRecord r          -> failwith __LOC__
    | Untyped.PAnnotated (p, ty) -> failwith __LOC__

and checkLocatedPatTys (lclCtxt : TypingEnv.t) (pats : Untyped.pattern list) (patTys : Types.target_ty list)
  : (Typed.pattern list * TypingEnv.t)
  = match pats, patTys with
    | [], [] -> ([], lclCtxt)
    | pat :: pats, ty :: tys ->
        let newPat , newCtxt = checkLocatedPatTy  lclCtxt pat  ty  in
        let newPats, outCtxt = checkLocatedPatTys newCtxt pats tys in
        (newPat :: newPats, outCtxt)
   | _, _ -> failwith "checkLocatedPatTys: length mismatch"

(* ************************************************************************* *)
(*                            PATTERN TYPING                                 *)
(* ************************************************************************* *)

(* mapAndUnzip :: (a -> (b, c)) -> [a] -> ([b], [c]) *)

let optionBind (x : 'a option) (f : 'a -> 'b option) : 'b option
  = match x with
    | None    -> None
    | Some x' -> f x'

let optionBind_ (x : 'a option) (y : 'b option) : 'b option
  = optionBind x (fun _ -> y)

let rec optionMapM (f : 'a -> 'b option) : 'a list -> ('b list) option = function
  | []      -> Some []
  | x :: xs -> optionBind (f x)             (fun y  ->
               optionBind (optionMapM f xs) (fun ys ->
               Some (y :: ys) ))

(* Infer a ground monotype for a pattern, if possible. *)
let rec inferClosedPatTy : Untyped.plain_pattern -> Types.target_ty option = function
  | Untyped.PVar _      -> None
  | Untyped.PNonbinding -> None
  | Untyped.PVariant (lbl, None) ->
      let ty_in, ty_out = Types.constructor_signature lbl in
      if (ty_in = Types.Tuple [] && Types.isClosedMonoTy ty_out)
        then (assert (Types.isClosedMonoTy ty_out); Some ty_out)
        else failwith "inferClosedPatTy: PVariant(None)"
  | Untyped.PVariant (lbl, Some p) ->
      let ty_in, ty_out = Types.constructor_signature lbl in
      checkLocatedClosedPatTy p ty_in ; assert (Types.isClosedMonoTy ty_out) ;
      Some ty_out
  | Untyped.PConst c           -> Some (Types.type_const c)
  | Untyped.PAs (p, _)         -> inferLocatedClosedPatTy p
  | Untyped.PTuple l           -> optionBind
                                    (optionMapM inferLocatedClosedPatTy l)
                                    (fun tys -> Some (Types.Tuple tys))
  | Untyped.PRecord r          -> None (* TODO: Not implemented yet *)
  | Untyped.PAnnotated (p, ty) -> failwith __LOC__ (* TODO: Not implemented yet *)
                                  (* if Types.isClosedMonoTy ty (* TODO: This is not an elaborated type *)
                                   *  then checkClosedPatTy p ty
                                   *  else None
                                   *)

and inferLocatedClosedPatTy (inpat : Untyped.pattern) : Types.target_ty option
  = inferClosedPatTy inpat.it

and checkLocatedClosedPatTy (inpat : Untyped.pattern) (patTy : Types.target_ty) : unit
  = checkClosedPatTy inpat.it patTy

(* Check a pattern against a ground monotype. Fail if not possible. *)
and checkClosedPatTy (inpat : Untyped.plain_pattern) (patTy : Types.target_ty) : unit
  = match inpat with
    | Untyped.PVar _      -> () (* Always possible *)
    | Untyped.PNonbinding -> () (* Always possible *)
    | Untyped.PVariant (lbl, None) ->
        let ty_in, ty_out = Types.constructor_signature lbl in
        if (ty_in = Types.Tuple [] && patTy = ty_out)
          then ()
          else failwith "checkClosedPatTy: PVariant(None)"
    | Untyped.PVariant (lbl, Some p) ->
        let ty_in, ty_out = Types.constructor_signature lbl in
        if (patTy = ty_out)
          then checkLocatedClosedPatTy p ty_in
          else failwith "checkClosedPatTy: PVariant(Some)"
    | Untyped.PConst c    -> if (patTy = Types.type_const c)
                               then ()
                               else failwith "checkClosedPatTy: PConst"
    | Untyped.PAs (p, v)  -> checkLocatedClosedPatTy p patTy
    | Untyped.PTuple pats ->
        (match patTy with
         | Types.Tuple tys -> List.iter2 checkLocatedClosedPatTy pats tys
         | _               -> failwith "checkClosedPatTy: PTuple")
    | Untyped.PRecord r          -> failwith __LOC__ (* TODO: Not implemented yet *)
    | Untyped.PAnnotated (p, ty) -> failwith __LOC__ (* TODO: Not implemented yet *)

let rec inferCheckLocatedClosedPatTys (pats : Untyped.pattern list)
  : Types.target_ty option
  = inferCheckClosedPatTys (List.map (fun p -> p.it) pats)

and inferCheckClosedPatTys (pats : Untyped.plain_pattern list)
  : Types.target_ty option
  = let rec filterMap f = (function
      | [] -> []
      | x :: xs -> match f x with
                   | None   -> filterMap f xs
                   | Some y -> y :: filterMap f xs
    ) in
    match filterMap inferClosedPatTy pats with
    (* Case 1: We cannot infer a ground type for any of the patterns *)
    | []      -> None
    (* Case 2: We can infer a type for at least a pattern. Verify that all
     * other patterns can be typed against this type and return it *)
    | ty :: _ -> List.iter (fun p -> checkClosedPatTy p ty) pats; Some ty

and inferCheckLocatedClosedPatAlts alts
  = match inferCheckLocatedClosedPatTys (List.map fst alts) with
    | None   -> failwith "inferCheckLocatedClosedPatAlts: Could not infer the type of the patterns"
    | Some t -> t

(* ************************************************************************* *)
(* ************************************************************************* *)
(* ************************************************************************* *)
let tcUntypedVarPat (lclCtxt : TypingEnv.t)
  : Untyped.plain_pattern -> (Typed.pattern * Types.target_ty * TypingEnv.t * constraints)
  = function
  | Untyped.PVar x      -> let alpha, alphaSkel = Typed.fresh_ty_with_fresh_skel ()
                           in  (Typed.PVar x, alpha, extendLclCtxt lclCtxt x alpha, [alphaSkel])
  | Untyped.PNonbinding -> let alpha, alphaSkel = Typed.fresh_ty_with_fresh_skel ()
                           in  (Typed.PNonbinding, alpha, lclCtxt, [alphaSkel])
  | Untyped.PConst c    -> (Typed.PConst c, Types.type_const c, lclCtxt, [])
  | Untyped.PTuple []   -> (Typed.PTuple [], Types.Tuple [], lclCtxt, [])
  (* GEORGE: TODO: Unhandled cases *)
  | _other_pattern      -> failwith "tcUntypedVarPat: Please no pattern matching in lambda abstractions!"

let tcLocatedUntypedVarPat (lclCtxt : TypingEnv.t) (pat : Untyped.pattern)
  : (Typed.pattern * Types.target_ty * TypingEnv.t * constraints)
  = tcUntypedVarPat lclCtxt pat.it

(* NOTE: We do not really want to return ANY constraints but given the current
 * elaboration strategy we do not want to fail when matching against a literal
 * or unit or something. Feels hacky but one does what one can. *)
let tcTypedVarPat (lclCtxt : TypingEnv.t)
      (pat : Untyped.plain_pattern)
      (patTy : Types.target_ty)
  : (Typed.pattern * TypingEnv.t * constraints)
  = match pat with
    | Untyped.PVar x      -> (Typed.PVar x, extendLclCtxt lclCtxt x patTy, [])
    | Untyped.PNonbinding -> (Typed.PNonbinding, lclCtxt, [])
    | Untyped.PConst c    -> let _, omegaCt = Typed.fresh_ty_coer (patTy, Types.type_const c) in
                             (Typed.PConst c, lclCtxt, [omegaCt])
    | Untyped.PTuple []   -> let _, omegaCt = Typed.fresh_ty_coer (patTy, Types.Tuple []) in
                             (Typed.PTuple [], lclCtxt, [omegaCt])
    (* Do not worry about the coercion variable not being used in this case;
     * the shape of the constraint will turn this into unification *)
    (* GEORGE: TODO: Unhandled cases *)
    | _other_pattern      -> failwith "tcTypedVarPat: Please no pattern matching in lambda abstractions!"

(* NOTE: We do not really want to return ANY constraints but given the current
 * elaboration strategy we do not want to fail when matching against a literal
 * or unit or something. Feels hacky but one does what one can. *)
let tcLocatedTypedVarPat (lclCtxt : TypingEnv.t)
      (pat : Untyped.pattern)
      (patTy : Types.target_ty)
  : (Typed.pattern * TypingEnv.t * constraints)
  = tcTypedVarPat lclCtxt pat.it patTy

let isLocatedVarPat (pat : Untyped.pattern) : bool
  = match pat.it with
    | Untyped.PVar _ -> true
    | _other_pattern -> false

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
                       ((target_x, x_monotype), constraints)
  | None -> Print.debug "Variable not found: %t" (Typed.print_variable x) ;
            assert false

(* Constants *)
and tcConst (inState : state) (lclCtxt : TypingEnv.t) (c : Const.t) : tcValOutput =
  ((Typed.Const c, Types.type_const c), [])

(* Type-annotated Expressions *)
and tcAnnotated (inState : state) (lclCtxt : TypingEnv.t) ((e,ty) : Untyped.expression * Type.ty) : tcValOutput =
  failwith __LOC__ (* GEORGE: Planned TODO for the future I guess?? *)

(* Tuples *)
and tcTuple (inState : state) (lclCtxt : TypingEnv.t) (es : Untyped.expression list): tcValOutput =
  let ((es, tys), cs) = tcMany inState lclCtxt es tcLocatedVal in
  ((Typed.Tuple es, Types.Tuple tys), cs)

(* Records *)
and tcRecord (inState : state) (lclCtx : TypingEnv.t) (lst : (field, Untyped.expression) Assoc.t)
      : tcValOutput =
  failwith __LOC__ (* GEORGE: Planned TODO for the future I guess?? *)

(* Variants *)
and tcVariant (inState : state) (lclCtx : TypingEnv.t) ((lbl,mbe) : label * Untyped.expression option)
      : tcValOutput =
  let ty_in, ty_out = Types.constructor_signature lbl in
  match mbe with
  | None   -> ((Typed.Variant (lbl, Typed.Tuple []), ty_out), [])
  | Some e ->
      let (e',ety),cs1 = tcLocatedVal inState lclCtx e in
      (* GEORGE: Investigate how cast_expression works *)
      let castExp, castCt = cast_expression e' ety ty_in in
      warnAddConstraints "tcVariant" [castCt];
      ((Typed.Variant (lbl, castExp), ty_out), castCt :: cs1)

(* Lambda Abstractions *)
and tcLambda (inState : state) (lclCtx : TypingEnv.t) ((pat,cmp) : Untyped.abstraction) : tcValOutput =
  let trgPat, patTy, midCtx, cs1 = tcLocatedUntypedVarPat lclCtx pat in
  let (trgCmp,cmpTy),        cs2 = tcLocatedCmp inState midCtx cmp in
  let outVal  = Typed.Lambda (abstraction_with_ty trgPat patTy trgCmp) in
  let outType = Types.Arrow (patTy, cmpTy) in
  ((outVal, outType), cs1 @ cs2)

(* Effects (GEORGE: Isn't this supposed to be in computations? *)
and tcEffect (inState : state) (lclCtx : TypingEnv.t) (eff : Untyped.effect) : tcValOutput =
  (* GEORGE: NOTE: This is verbatim copied from the previous implementation *)
  let in_ty, out_ty = Typed.EffectMap.find eff inState.effects in
  let s = Types.EffectSet.singleton eff in
  let outVal  = Typed.Effect (eff, (in_ty, out_ty)) in
  let outType = Types.Arrow (in_ty, (out_ty, Types.closed_dirt s)) in
  ((outVal, outType), [])

(* Handlers(Return Case) *)
and tcReturnCase (inState : state) (lclCtx : TypingEnv.t)
      ((pat, cmp) : Untyped.abstraction) (* Return clause *)
      (tyIn : Types.target_ty)           (* Expected input value type *)
      (tyOut : Types.target_ty)          (* Expected output value type *)
      (dirtOut : Types.dirt)             (* Expected output dirt *)
  : Typed.abstraction_with_ty tcOutput
  = (* 1: Typecheck the pattern and the body of the return clause *)
    let trgPat, patTy, midCtx, cs1 = tcLocatedUntypedVarPat lclCtx pat in
    let (trgCmp, (tyB,dirtD)), cs2 = tcLocatedCmp inState midCtx cmp in

    (* 2: Make sure that the pattern is a variable one.
     *    We do not support anything else at the moment *)
    let x = (match trgPat with
             | PVar x -> x
             | _      -> failwith "tcReturnCase: only varpats allowed") in

    (* 3: Generate all wanted constraints *)
    let omega1, omegaCt1 = Typed.fresh_ty_coer (tyB, tyOut) in
    let omega2, omegaCt2 = Typed.fresh_dirt_coer (dirtD, dirtOut) in
    let omega6, omegaCt6 = Typed.fresh_ty_coer (tyIn, patTy) in

    (* 4: Create the elaborated clause *)
    let yvar = CoreTypes.Variable.fresh "y" in
    let ysub = Typed.subst_comp (Assoc.of_list [(x, CastExp (Var yvar, omega6))]) in
    let outExpr = (PVar yvar, patTy, Typed.CastComp (ysub trgCmp, Typed.BangCoercion (omega1, omega2))) in

    (* 5: Combine the results *)
    (outExpr, omegaCt1 :: omegaCt2 :: omegaCt6 :: cs1 @ cs2) (* NOTE: (a_r : skel_r) \in cs1 *)

(* Handlers(Op Cases) *)
and tcOpCases (inState : state) (lclCtx : TypingEnv.t)
      (eclauses : (Untyped.effect, Untyped.abstraction2) Assoc.t)
      (tyOut : Types.target_ty) (dirtOut : Types.dirt)
  : ((Typed.effect, Typed.abstraction2) Assoc.t) tcOutput
  = let rec go cs
      = (match Assoc.isCons cs with
         | None        -> ([], [])
         | Some (c,cs) -> let y,  cs1 = tcOpCase inState lclCtx c tyOut dirtOut in
                          let ys, cs2 = go cs in
                          (y :: ys, cs1 @ cs2)
        ) in
    let allClauses, allCs = go eclauses in
    (Assoc.of_list allClauses, allCs)

(* Handlers(Op Case) *)
and tcOpCase (inState : state) (lclCtx : TypingEnv.t)
      ((eff,abs2) : Untyped.effect * Untyped.abstraction2) (* Op clause *)
      (tyOut : Types.target_ty)                   (* Expected output value type *)
      (dirtOut : Types.dirt)                      (* Expected output dirt *)
  : (Typed.effect * Typed.abstraction2) tcOutput
  = (* 1: Lookup the type of Opi *)
    let tyAi, tyBi = Typed.EffectMap.find eff inState.effects in

    (* 2: Generate fresh variables for the type of the codomain of the continuation *)
    let alphai, alphaiSkel = Typed.fresh_ty_with_fresh_skel () in
    let deltai = Types.fresh_dirt () in

    (* 3: Typecheck the clause *)
    let ((xop,kop,trgCop),(_,_,(tyBOpi,dirtDOpi))), csi (* GEORGE: I don't like the unused types *)
      = tcTypedAbstraction2 inState lclCtx abs2 tyAi (Types.Arrow (tyBi, (alphai,deltai))) in

    (* 4: Make sure that the pattern for k is a variable one.
     *    We do not support anything else at the moment *)
    let k = (match kop with
             | PVar k -> k
             | _ -> failwith "tcOpCase: only varpats allowed") in

    (* 5: Generate all the needed constraints *)
    let omega3i, omegaCt3i = Typed.fresh_ty_coer   (tyBOpi, tyOut) in
    let omega4i, omegaCt4i = Typed.fresh_dirt_coer (dirtDOpi, dirtOut) in
    let omega5i, omegaCt5i = (let leftty  = Types.Arrow (tyBi,(tyOut,dirtOut)) in
                              let rightty = Types.Arrow (tyBi,(alphai,deltai)) in
                              Typed.fresh_ty_coer (leftty, rightty)) in

    (* 6: Create the elaborated clause *)
    let lvar = CoreTypes.Variable.fresh "l" in
    let lsub = Typed.subst_comp (Assoc.of_list [(k, CastExp (Var lvar, omega5i))]) in
    let outExpr = ( ((eff,(tyAi,tyBi)) : Typed.effect) (* Opi *)
                  , (xop, PVar lvar, CastComp (lsub trgCop, Typed.BangCoercion (omega3i,omega4i)))
                  ) in

    (* 7: Combine the results *)
    let outCs = alphaiSkel :: omegaCt3i :: omegaCt4i :: omegaCt5i :: csi in
    (outExpr, outCs)

(* Handlers *)
and tcHandler (inState : state) (lclCtx : TypingEnv.t) (h : Untyped.handler) : tcValOutput =
  (* 0: Warn about the current state of the implementation *)
  Print.debug "Ignoring the finally_clause" ;

  (* 1: Generate fresh variables for the input and output types *)
  let alphaIn, alphaInSkel = Typed.fresh_ty_with_fresh_skel () in
  let deltaIn = Types.fresh_dirt () in
  let alphaOut, alphaOutSkel = Typed.fresh_ty_with_fresh_skel () in
  let deltaOut = Types.fresh_dirt () in

  (* 2: Process the return and the operation clauses *)
  let trgRet, cs1 = tcReturnCase inState lclCtx h.value_clause alphaIn alphaOut deltaOut in
  let trgCls, cs2 = tcOpCases inState lclCtx h.effect_clauses alphaOut deltaOut in

  (* 3: Create the omega7 coercion (cast the whole handler) *)
  let omega7, omegaCt7 =
    let allOps = trgCls
                 |> Assoc.to_list
                 |> List.map (fun ((eff, _), _) -> eff)
                 |> Types.EffectSet.of_list in

    (* GEORGE: This should be done in a cleaner way but let's leave it for later *)
    let deltaOutVar = (match deltaOut.row with
                       | ParamRow deltaOutVar -> deltaOutVar
                       | EmptyRow -> failwith "deltaOut: IMPOSSIBLE") in

    Typed.fresh_dirt_coer (deltaIn, Types.{effect_set = allOps; row= ParamRow deltaOutVar})
  in

  warnAddConstraints "tcHandler[7,in,out]" [omegaCt7;alphaInSkel;alphaOutSkel];

  let handlerCo = Typed.HandlerCoercion ( Typed.BangCoercion (Typed.ReflTy alphaIn, omega7)
                                        , Typed.BangCoercion (Typed.ReflTy alphaOut, Typed.ReflDirt deltaOut) ) in
  Print.debug "I am the HandlerCo : %t" (Typed.print_ty_coercion handlerCo) ;

  let outExpr = CastExp ( Handler ({ effect_clauses = trgCls
                                   ; value_clause   = trgRet })
                        , handlerCo ) in
  let outType = Types.Handler ((alphaIn, deltaIn), (alphaOut, deltaOut)) in
  let outCs   = omegaCt7 :: alphaInSkel :: alphaOutSkel :: cs1 @ cs2 in (* 7, ain : skelin, aout : skelout && 1, 2, 6 && 3i, 4i, 5i *)
  ((outExpr, outType), outCs)

(* Dispatch: Type inference for a plain value (expression) *)
and tcVal (inState : state) (lclCtx : TypingEnv.t) : Untyped.plain_expression -> tcValOutput = function
  | Untyped.Var x              -> tcVar       inState lclCtx x
  | Untyped.Const c            -> tcConst     inState lclCtx c
  | Untyped.Annotated (e,ty)   -> tcAnnotated inState lclCtx (e,ty)
  | Untyped.Tuple es           -> tcTuple     inState lclCtx es
  | Untyped.Record lst         -> tcRecord    inState lclCtx lst
  | Untyped.Variant (lbl,mbe)  -> tcVariant   inState lclCtx (lbl,mbe)
  | Untyped.Lambda abs         -> tcLambda    inState lclCtx abs
  | Untyped.Effect eff         -> tcEffect    inState lclCtx eff
  | Untyped.Handler hand       -> tcHandler   inState lclCtx hand

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

  (* Nest a list of letrec-bindings; MUTUAL RECURSION NOT ALLOWED AT THE MOMENT *)
  | LetRec ([],c2)                -> tcLocatedCmp inState lclCtx c2
  | LetRec ([(var,abs)],c2)       -> tcLetRecNoGen inState lclCtx var abs c2
  | LetRec ((var,abs) :: rest,c2) -> let subCmp = {it = Untyped.LetRec (rest,c2); at = c2.at} in
                                     tcCmp inState lclCtx (Untyped.LetRec ([(var,abs)], subCmp))

  (* Pattern Matching: Special Case 2: Variable-binding *)
  | Match (scr, [(p,c)]) when isLocatedVarPat p ->
      tcCmp inState lclCtx (Untyped.Let ([(p, {it = Untyped.Value scr; at = p.at})],c))
  (* Pattern Matching: General Case: Monomorphic patterns *)
  | Match (scr, cases)       -> tcMatch  inState lclCtx scr cases
  | Apply (val1, val2)       -> tcApply  inState lclCtx val1 val2
  | Handle (hand, cmp)       -> tcHandle inState lclCtx hand cmp
  | Check cmp                -> tcCheck  inState lclCtx cmp

(* Type inference for a located computation *)
and tcLocatedCmp (inState : state) (lclCtx : TypingEnv.t) (c : Untyped.computation) : tcCmpOutput
  = tcCmp inState lclCtx c.it

(* Typecheck a value wrapped in a return *)
and tcValue (inState : state) (lclCtxt : TypingEnv.t) (exp : Untyped.expression) : tcCmpOutput =
  let ((outExpr, outType), outCs) = tcLocatedVal inState lclCtxt exp in
  ((Typed.Value outExpr, (outType, Types.empty_dirt)), outCs)

(* Typecheck a let where c1 is a value *)
and tcLetValNoGen (inState : state) (lclCtxt : TypingEnv.t)
      (patIn : Untyped.pattern)
      (e1 : Untyped.expression)
      (c2 : Untyped.computation) : tcCmpOutput =
  (* 1: Typecheck e1 *)
  let (trgE1,tyA1), cs1 = tcLocatedVal inState lclCtxt e1 in (* (v',A, Qv, Sigma1) *)

  (* 2: Typecheck c2 *)
  let x = (match patIn.it with
           | Untyped.PVar x -> x (* GEORGE: Support nothing else at the moment *)
           | _ -> failwith "tcLetValNoGen: only varpats allowed") in
  let (trgC2, (tyB2,dirtD2)), cs2 = tcLocatedCmp inState (extendLclCtxt lclCtxt x tyA1) c2 in

  (* 3: Combine the results *)
  let outExpr = Typed.LetVal
                  ( trgE1
                  , Typed.abstraction_with_ty (Typed.PVar x) tyA1 trgC2 ) in
  let outType = (tyB2,dirtD2) in
  let outCs   = cs1 @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a let when c1 is a computation (== do binding) *)
and tcLetCmp (inState : state) (lclCtxt : TypingEnv.t) (pat : Untyped.pattern) (c1 : Untyped.computation) (c2 : Untyped.computation) : tcCmpOutput =
  (* 1: Typecheck c1, the pattern, and c2 *)
  let (trgC1, (tyA1, dirtD1)), cs1 = tcLocatedCmp inState lclCtxt c1 in
  let trgPat, midCtx, hack = tcLocatedTypedVarPat lclCtxt pat tyA1 in
  let (trgC2, (tyA2, dirtD2)), cs2 = tcLocatedCmp inState midCtx c2 in

  (* 2: Generate a fresh dirt variable for the result *)
  let delta = Types.fresh_dirt () in

  (* 3: Generate the coercions for the dirts *)
  let omega1, omegaCt1 = Typed.fresh_dirt_coer (dirtD1, delta) in (* s2(D1) <= delta *)
  let omega2, omegaCt2 = Typed.fresh_dirt_coer (dirtD2, delta) in (*    D2  <= delta *)

  let cresC1 = CastComp (trgC1, Typed.BangCoercion (Typed.ReflTy tyA1, omega1)) in
  let cresC2 = CastComp (trgC2, Typed.BangCoercion (Typed.ReflTy tyA2, omega2)) in

  let outExpr = Typed.Bind
                  ( cresC1
                  , ( trgPat
                    , cresC2 )
                  ) in
  let outType = (tyA2, delta) in
  let outCs   = hack @ (omegaCt1 :: omegaCt2 :: cs1 @ cs2) in

  warnAddConstraints "tcLetCmp" [omegaCt1;omegaCt2];
  ((outExpr,outType), outCs)

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
  let ((trgPat, trgC1), (trgPatTy,(tyA1, dirtD1))), cs1
    = tcTypedAbstraction
        inState
        (extendLclCtxt lclCtxt var (Types.Arrow (alpha, (beta, delta))))
        abs alpha in

  (* 3: Typecheck c2 *)
  let (trgC2, (tyA2, dirtD2)), cs2
    = tcLocatedCmp
        inState
        (extendLclCtxt lclCtxt var (Types.Arrow (alpha, (tyA1,dirtD1))))
        c2
  in

  (* 3: The assumed type should be at least as general as the inferred one *)
  let omega1, omegaCt1 = Typed.fresh_ty_coer (tyA1, beta) in
  let omega2, omegaCt2 = Typed.fresh_dirt_coer (dirtD1, delta) in

  (* 4: Create the (complicated) c1''. *)
  let c1'' = (
    let f_coercion = Typed.ArrowCoercion
                       ( Typed.ReflTy alpha
                       , Typed.BangCoercion (omega1, omega2)
                       ) in
    let subst_fn   = Typed.subst_comp (Assoc.of_list [(var, Typed.CastExp(Typed.Var var, f_coercion))]) in

    subst_fn trgC1
  ) in

  (* 5: Combine the results *)
  let outExpr = Typed.LetRec ([(var, trgPatTy, (tyA1, dirtD1), (trgPat,c1''))], trgC2) in

  let outType = (tyA2, dirtD2) in
  let outCs   = alphaSkel :: betaSkel :: omegaCt1 :: omegaCt2 :: cs1 @ cs2 in
  ((outExpr, outType), outCs)

and tcMatch (inState : state) (lclCtxt : TypingEnv.t)
      (scr : Untyped.expression)
      (alts : Untyped.abstraction list) : tcCmpOutput =
  (* 1: Generate fresh variables for the result *)
  let alphaOut, alphaOutSkel = fresh_ty_with_fresh_skel () in
  let deltaOut = Types.fresh_dirt () in

  (* 2: Infer a type for the patterns *)
  let patTy = inferCheckLocatedClosedPatAlts alts in

  (* 4: Typecheck the scrutinee and the alternatives *)
  let (trgScr, scrTy), cs1 = tcLocatedVal inState lclCtxt scr in
  let trgAlts, cs2 = mapAndUnzipTcOutputs
                       (fun alt -> tcAlternative inState lclCtxt patTy alt (alphaOut, deltaOut))
                       alts in

  (* 5: Generate the coercion for casting the scrutinee *)
  (* NOTE: The others should be already included in 'altRes' *)
  let omegaScr, omegaCtScr = Typed.fresh_ty_coer (scrTy, patTy) in

  (* 6: Combine the results *)
  (* STIEN: using the scr location here is a bit of a hack *)
  let outExpr = Typed.Match (Typed.CastExp (trgScr, omegaScr), trgAlts, scr.at) in
  let outType = (alphaOut, deltaOut) in
  let outCs   = alphaOutSkel :: omegaCtScr :: cs1 @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a function application *)
and tcApply (inState : state) (lclCtxt : TypingEnv.t) (val1 : Untyped.expression) (val2 : Untyped.expression) : tcCmpOutput =
  (* Infer the types of val1 and val2 *)
  let (trgVal1, valTy1), cs1 = tcLocatedVal inState lclCtxt val1 in
  let (trgVal2, valTy2), cs2 = tcLocatedVal inState lclCtxt val2 in

  (* Generate fresh variables for the result *)
  let alpha, alphaSkel = Typed.fresh_ty_with_fresh_skel () in
  let delta = Types.fresh_dirt () in

  (* Create the constraint and the cast elaborated expression *)
  let omega, omegaCt = Typed.fresh_ty_coer ( valTy1
                                           , Types.Arrow (valTy2, (alpha,delta)) ) in
  let castVal1 = Typed.CastExp (trgVal1, omega) in

  warnAddConstraints "tcApply" [alphaSkel; omegaCt];
  let outExpr = Typed.Apply (castVal1, trgVal2) in
  let outType = (alpha, delta) in
  let outCs   = alphaSkel :: omegaCt :: cs1 @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a handle-computation *)
and tcHandle (inState : state) (lclCtxt : TypingEnv.t) (hand : Untyped.expression) (cmp : Untyped.computation) : tcCmpOutput =
  (* Typecheck the handler and the computation *)
  let (trgHand, tyA1), cs1 = tcLocatedVal inState lclCtxt hand in (* Typecheck the handler *)
  let (trgCmp, (tyA2, dirtD2)), cs2 = tcLocatedCmp inState lclCtxt cmp in (* Typecheck the computation *)

  (* Generate fresh variables *)
  let alpha1, alphaSkel1 = Typed.fresh_ty_with_fresh_skel () in
  let delta1 = Types.fresh_dirt () in
  let alpha2, alphaSkel2 = Typed.fresh_ty_with_fresh_skel () in
  let delta2 = Types.fresh_dirt () in

  (* Create all constraints *)
  let omega1, omegaCt1 = Typed.fresh_ty_coer (tyA1, Types.Handler ((alpha1, delta1), (alpha2, delta2))) in
  let omega2, omegaCt2 = Typed.fresh_ty_coer (tyA2, alpha1) in
  let omega3, omegaCt3 = Typed.fresh_dirt_coer (dirtD2, delta1) in

  (* Combine all the outputs *)
  let outExpr = (
    let castHand = Typed.CastExp (trgHand, omega1) in
    let castCmp  = Typed.CastComp (trgCmp, Typed.BangCoercion (omega2, omega3)) in
    Typed.Handle (castHand, castCmp)
  ) in
  let outType = (alpha2, delta2) in
  let outCs   =  alphaSkel1 :: alphaSkel2
              :: omegaCt1 :: omegaCt2 :: omegaCt3
              :: cs1 @ cs2 in
  ((outExpr, outType), outCs)

(* Typecheck a "Check" expression (GEORGE does not know what this means yet *)
and tcCheck (inState : state) (lclCtxt : TypingEnv.t) (cmp : Untyped.computation) : tcCmpOutput =
  failwith __LOC__ (* GEORGE: Planned TODO for the future I guess?? *)

(* ************************************************************************* *)
(*                               UTILITIES                                   *)
(* ************************************************************************* *)

(* Given the expected type of the pattern and the expected result type,
 * typecheck a single case alternative. *)
and tcAlternative (inState : state) (lclCtx : TypingEnv.t)
  (patTy : Types.target_ty)                 (* Expected pattern type *)
  ((pat,cmp) : Untyped.abstraction)         (* Case alternative *)
  ((tyAout, dirtDout) : Types.target_dirty) (* Expected output type *)
  : Typed.abstraction tcOutput
  = (* Typecheck the pattern and the right-hand side *)
    let trgPat, midCtxt = checkLocatedPatTy lclCtx pat patTy in
    let (trgCmp,(tyA, dirtD)), cs = tcLocatedCmp inState midCtxt cmp in
    (* Generate coercions to cast the RHS *)
    let omegaL, omegaCtL = Typed.fresh_ty_coer (tyA, tyAout) in
    let omegaR, omegaCtR = Typed.fresh_dirt_coer (dirtD, dirtDout) in
    (* Combine the results *)
    let outExpr = (trgPat, Typed.CastComp (trgCmp, Typed.BangCoercion (omegaL, omegaR))) in
    let outCs   = omegaCtL :: omegaCtR :: cs in
    (outExpr, outCs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and tcTypedAbstraction (inState : state) (lclCtx : TypingEnv.t) (pat,cmp) patTy =
  let trgPat, midLclCtx,hack = tcLocatedTypedVarPat lclCtx pat patTy in
  let (trgCmp, cmpTy), cs    = tcLocatedCmp inState midLclCtx cmp in
  (((trgPat, trgCmp), (patTy, cmpTy)), hack @ cs)

(* Typecheck an abstraction where we *know* the type of the pattern. By *know*
 * we mean that we have inferred "some" type (could be instantiated later).
 * Hence, we conservatively ask for the pattern to be a variable pattern (cf.
 * tcTypedVarPat) *)
and tcTypedAbstraction2 (inState : state) (lclCtx : TypingEnv.t) (pat1,pat2,cmp) patTy1 patTy2 =
  let trgPat1, midCtx1, hack1 = tcLocatedTypedVarPat lclCtx  pat1 patTy1 in
  let trgPat2, midCtx2, hack2 = tcLocatedTypedVarPat midCtx1 pat2 patTy2 in
  let (trgCmp, cmpTy), cs     = tcLocatedCmp inState midCtx2 cmp in
  (((trgPat1, trgPat2, trgCmp), (patTy1, patTy2, cmpTy)), hack1 @ hack2 @ cs)

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
let tcTopLevelMono ~loc inState cmp =
  Print.debug "tcTopLevelMono [0]: %t" (Untyped.print_computation cmp) ;
  (* 1: Constraint generation *)
  let (trgCmp, (ttype, dirt)), generatedCs
    = tcLocatedCmp inState initial_lcl_ty_env cmp in

  Print.debug "tcTopLevelMono [1]: INFERRED (BEFORE SUBST): %t" (Types.print_target_dirty (ttype,dirt)) ;
  Print.debug "tcTopLevelMono [1]: ELABORATED COMP (BEFORE SUBST): %t" (Typed.print_computation trgCmp) ;

  (* 2: Constraint solving *)
  let solverSigma, residualCs = (
    (* A: Solve the constraints as they are *)
    let initialSigma, initialResiduals = Unification.unify (Substitution.empty, [], generatedCs) in
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

  Print.debug "tcTopLevelMono [2]: INFERRED (AFTER  SUBST): %t" (Types.print_target_dirty (subInCmpTy solverSigma (ttype,dirt))) ;
  Print.debug "tcTopLevelMono [2]: RESIDUAL CONSTRAINTS:"; Unification.print_c_list residualCs ;

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

  let targetType =
    (ttype, dirt)
      |> subInCmpTy solverSigma
      |> subInCmpTy dirtZonker
      |> subInCmpTy sub3 in

  Print.debug "ELABORATED COMP (COMPLETE): %t" (Typed.print_computation targetComputation) ;

  (* 6: Return the ExEff computation *)
  (targetComputation, targetType)

(* Add an external binding to the typing environment *)
let addExternal ctx x ty = { ctx with gblCtxt = TypingEnv.update ctx.gblCtxt x ty }
