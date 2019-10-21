open NoEffSyntax
open Types
open Typed

module TypeCheck = TypeChecker
module NoEff = NoEffSyntax
module ExEffTypes = Types
module ExEff = Typed
module EffectSet = Set.Make (CoreTypes.Effect)

type effect_set = EffectSet.t

type environment = TypeCheck.state

let rec extend_pattern_type env pat ty =
  match pat with
  | PVar x -> TypeCheck.extend_var_types env x ty
  | PAs (p, x) -> extend_pattern_type (TypeCheck.extend_var_types env x ty) p ty
  | PTuple ps -> (
    match ty with 
    | ExEffTypes.Tuple tys ->
                    if (List.length tys == List.length ps)
                    then (if (List.length tys==0) 
                          then env
                          else (extend_pattern_type (extend_pattern_type env (List.hd ps) (List.hd tys)) 
                                        (PTuple (List.tl ps)) (ExEffTypes.Tuple (List.tl tys))))
                    else failwith "Ill-typed tuple"
    | _ -> failwith "Ill-typed tuple" )
  (* STIEN: todo: Check c-type with ty *)
  | PConst c -> env
  | PNonbinding -> env

let rec type_elab state (env : environment) (ty : ExEffTypes.target_ty) =
  match ty with
  | ExEffTypes.TyParam x -> ( 
    match (Assoc.lookup x env.ty_param_skeletons) with
    | Some xtype -> (xtype, NoEff.NTyParam x)
    | None -> failwith "Ill-typed environment" )
  | ExEffTypes.Apply (name, lst) -> failwith "Should not be needed"
  | ExEffTypes.Arrow (t, dirty) -> 
    let (ty1, elab1) = type_elab state env t in
    let (ty2, elab2) = dirty_elab state env dirty in
    (ExEffTypes.SkelArrow (ty1, ty2), NoEff.NTyArrow (elab1, elab2))
  | ExEffTypes.Handler ((type1, dirt1), (type2, dirt2)) ->
    let (ty1, elab1) = type_elab state env type1 in
    if (ExEffTypes.is_empty_dirt dirt1)
    (* Handler type - Case 1: empty input dirt *)
    then (
      let (ty2, elab2) = dirty_elab state env (type2, dirt2) in
      (ExEffTypes.SkelHandler (ty1, ty2), NoEff.NTyArrow (elab1, elab2))
    )
    (* Handler type - Case 2: non-empty input dirt *)
    else (
      let (ty2, elab2) = type_elab state env type2 in
      (ExEffTypes.SkelHandler (ty1, ty2), NoEff.NTyHandler (elab1, elab2))
    )
  | ExEffTypes.Tuple tys ->
    let ty_elab_list = List.map (type_elab state env) tys in
    (ExEffTypes.SkelTuple (List.map (fun (x,_) -> x) ty_elab_list),
     NoEff.NTyTuple (List.map (fun (_,x) -> x) ty_elab_list))
  | ExEffTypes.QualTy ( (t1, t2), ty) ->
    let (type1, elab1) = type_elab state env t1 in
    let (type2, elab2) = type_elab state env t2 in
    let (type3, elab3) = type_elab state env ty in
    (type3, NoEff.NTyQual ((elab1, elab2), elab3))
  | ExEffTypes.QualDirt (_, ty) -> type_elab state env ty
  | ExEffTypes.TySchemeTy (par, skel, ty) -> 
    let env' = TypeCheck.extend_ty_param_skeletons env par skel in
    let (t, elab) = type_elab state env' ty in
    (t, NoEff.NTyForall (par, elab))
  | ExEffTypes.TySchemeDirt (par, ty) -> type_elab state env ty
  | ExEffTypes.TySchemeSkel (par, ty) -> 
    let (t, elab) = type_elab state env ty in
    (ExEffTypes.ForallSkel (par, t), elab)
  | ExEffTypes.PrimTy ty ->
    match ty with
    | ExEffTypes.IntTy -> (ExEffTypes.PrimSkel ty, NoEff.NTyPrim NInt)
    | ExEffTypes.BoolTy -> (ExEffTypes.PrimSkel ty, NoEff.NTyPrim NBool)
    | ExEffTypes.StringTy -> (ExEffTypes.PrimSkel ty, NoEff.NTyPrim NString)
    | ExEffTypes.FloatTy -> (ExEffTypes.PrimSkel ty, NoEff.NTyPrim NFloat)

and dirty_elab state env (ty, dirt) =
  let (skel, elab) = type_elab state env ty in
  if (ExEffTypes.is_empty_dirt dirt)
  then (skel, elab)
  else (skel, NoEff.NTyComp elab)

and pattern_elab p =
  match p with
  | PVar x -> NVar x
  | PAs (p, x) -> NAs (pattern_elab p, x)
  | PTuple ps -> NTuple (List.map pattern_elab ps)
  | PConst c -> NConst c
  | PNonbinding -> NNonBinding

and value_elab (state : ExplicitInfer.state) (env : environment) v =
  match v with
  | ExEff.Var x -> (
    match Assoc.lookup x env.var_types with
    | Some ty -> (ty, NoEff.NVar x)
    | None -> ( match TypingEnv.lookup state.gblCtxt x with
                     | Some ty -> (ty, NoEff.NVar x)
                     | None -> failwith "No type for variable found" ) )
  | ExEff.Const c -> (ExEffTypes.type_const c, NoEff.NConst c)
  | ExEff.Tuple vs -> 
    let type_elab_list = List.map (value_elab state env) vs in
    (ExEffTypes.Tuple (List.map (fun (x,_) -> x) type_elab_list),
     NoEff.NTuple (List.map (fun (_,x) -> x) type_elab_list))
  | ExEff.Lambda (p, t, c) -> 
    let (_, elab1) = type_elab state env t in
    let env' = extend_pattern_type env p t in
    let (type2, elab2) = comp_elab state env' c in
    (ExEffTypes.Arrow (t, type2),
     NoEff.NFun (pattern_elab p, elab1, elab2))
  | ExEff.Effect (e, (t1, t2)) ->
    let (_, elab1) = type_elab state env t1 in
    let (_, elab2) = type_elab state env t2 in
    (ExEffTypes.Arrow (t1, (t2, ExEffTypes.closed_dirt (EffectSet.singleton e))), 
     NoEff.NEffect (e, (elab1, elab2)))
  | ExEff.Handler h ->
    let (p, t, c) = h.value_clause in
    let (_, elabt) = type_elab state env t in
    let env' = extend_pattern_type env p t in
    let (typec, elabc) = comp_elab state env' c in

    if (Assoc.length h.effect_clauses = 0)
    (* Handler - Case 1 *)
    then (
      (ExEffTypes.Handler ( (t, ExEffTypes.empty_dirt), typec),
       NoEff.NFun (pattern_elab p, elabt, elabc))
      )
    else (
      let (ty, dirt) = typec in
      if (ExEffTypes.is_empty_dirt dirt)
      (* Handler - Case 2 *)
      then (
        let subst_cont_effect ((eff, (ty1, ty2)), (p1, p2, comp)) = 
          ( let (_, elab1) = type_elab state env ty1 in
          let (_, elab2) = type_elab state env ty2 in
          let env' = extend_pattern_type env p1 ty1 in
          let env'' = extend_pattern_type env' p2 (ExEffTypes.Arrow (ty2, (t, ExEffTypes.empty_dirt))) in
          let (_, elabcomp) = comp_elab state env'' comp in
            ((eff, (elab1, elab2)), (pattern_elab p1, NoEff.NCast ((pattern_elab p2), 
            (NoEff.NCoerArrow (NoEff.NCoerRefl (elab1),
             NoEff.NCoerUnsafe (NoEff.NCoerRefl (elab2))))), NoEff.NReturn elabcomp)) ) in
          let effectset = get_effectset EffectSet.empty (Assoc.to_list h.effect_clauses) in
          (  ExEffTypes.Handler ( (t, ExEffTypes.closed_dirt effectset), typec ),  
             NoEff.NHandler 
            {return_clause= (pattern_elab p, elabt, NoEff.NReturn elabc);
             effect_clauses= Assoc.map_of_list subst_cont_effect (Assoc.to_list h.effect_clauses)}
          )
      )
      (* Handler - Case 3 *)
      else (
        let elab_effect_clause ((eff, (ty1, ty2)), (p1, p2, comp)) = 
          let (_, elab1) = type_elab state env ty1 in
          let (_, elab2) = type_elab state env ty2 in
          let env' = extend_pattern_type env p1 ty1 in
          let env'' = extend_pattern_type env' p2 (ExEffTypes.Arrow (ty2, (t, ExEffTypes.empty_dirt))) in
          let (_, elabcomp) = comp_elab state env'' comp in
          ((eff, (elab1, elab2)), (pattern_elab p1, pattern_elab p2, elabcomp)) in

          let effectset = get_effectset EffectSet.empty (Assoc.to_list h.effect_clauses) in
          ( 
            ExEffTypes.Handler ( (t, ExEffTypes.closed_dirt effectset), typec ),
            NoEff.NHandler {return_clause= (pattern_elab p, elabt, elabc);
            effect_clauses= (Assoc.map_of_list elab_effect_clause (Assoc.to_list h.effect_clauses))}    
          )
      )
    )
  | ExEff.BigLambdaTy (par, skel, value) -> 
    let env' = TypeCheck.extend_ty_param_skeletons env par skel in
    let (ty, elab) = value_elab state env' value in
    (ExEffTypes.TySchemeTy (par, skel, ty), NoEff.NBigLambdaTy (par, elab))
  | ExEff.BigLambdaDirt (par, value) -> 
    let env' = TypeCheck.extend_dirt_params env par in
    let (ty, elab) = value_elab state env' value in
    (ExEffTypes.TySchemeDirt (par, ty), elab)
  | ExEff.BigLambdaSkel (par, value) -> 
    let env' = TypeCheck.extend_skel_params env par in
    let (ty, elab) = value_elab state env' value in
    (ExEffTypes.TySchemeSkel (par, ty), elab)
  | ExEff.CastExp (value, coer) -> 
    let (ty1, elab1) = value_elab state env value in
    let ((ty2, r), elab2) = coercion_elab_ty state env coer in
    if (ty1 = ty2) 
    then (r, NoEff.NCast (elab1, elab2))
    else failwith "Ill-typed cast"
  | ExEff.ApplyTyExp (value, ty) -> 
    let (tyv, elabv) = (
      match (value_elab state env value) with
      | (ExEffTypes.TySchemeTy (p,t,v), elab) -> (ExEffTypes.TySchemeTy (p,t,v), elab)
      | _ -> failwith "Ill-typed type application value"
    ) in
    let (skel, elabt) = type_elab state env ty in
    let (pat, s, bigt) =
    ( 
      match tyv with
      | ExEffTypes.TySchemeTy (p, t, v) -> (p, t, v)
      | _ -> failwith "Ill-typed type application value"
    ) in
    ( subst_ty_param ty pat bigt,  NoEff.NTyAppl (elabv, elabt) )
  | ExEff.LambdaTyCoerVar (par, (ty1, ty2), value) ->
    let (_, elab1) = type_elab state env ty1 in
    let (_, elab2) = type_elab state env ty2 in
    let env' = TypeCheck.extend_ty_coer_types env par (ty1, ty2) in
    let (typev, elabv) = value_elab state env' v in
    ( ExEffTypes.QualTy ((ty1, ty2), typev),
      NoEff.NBigLambdaCoer (par, (elab1, elab2), elabv) )
  | ExEff.LambdaDirtCoerVar (par, (dirt1, dirt2), value) -> 
    let env' = TypeCheck.extend_dirt_coer_types env par (dirt1, dirt2) in
    let (typev, elabv) = value_elab state env' value
    in (ExEffTypes.QualDirt ((dirt1, dirt2), typev), elabv) 
  | ExEff.ApplyDirtExp (value, dirt) -> failwith "STIEN: This should not be needed"
  | ExEff.ApplySkelExp (value, skel) -> failwith "STIEN: Start here when you come back, use typecheck"

  | ExEff.ApplyTyCoercion (value, coer) -> 
    let ((ty1, ty2), elabc) = coercion_elab_ty state env coer in
    let (ty, elabv) = value_elab state env value in
      (
        match ty with
        | ExEffTypes.QualTy ((ty1, ty2), t) -> (t, NoEff.NApplyCoer (elabv, elabc))
        | _ -> failwith "Ill-typed coercion application"
      ) 
  | ExEff.ApplyDirtCoercion (value, coer) ->
    let (ty, elabv) = value_elab state env value in
    (
        match ty with
        | ExEffTypes.QualDirt ((dirt1, dirt2), t) -> (t, elabv)
        | _ -> failwith "Ill-typed coercion application"
    )


and coercion_elab_ty = failwith "TODO"

and coercion_elab_dirty = failwith "TODO"

and coercion_elab_dirt = failwith "TODO"

and get_effectset set effects =
  match effects with
  | (((eff, _), abs)::es) -> get_effectset (EffectSet.add eff set) es
  | [] -> set

and subst_ty_param tysub par ty =
  match ty with
  | ExEffTypes.TyParam x -> if (x = par) then (tysub) else (ty)
  | ExEffTypes.Apply (n, ls) -> ExEffTypes.Apply (n, List.map (subst_ty_param tysub par) ls)
  | ExEffTypes.Arrow (l, (rt, rd)) -> ExEffTypes.Arrow (subst_ty_param tysub par l, (subst_ty_param tysub par rt, rd))
  | ExEffTypes.Tuple ls -> ExEffTypes.Tuple (List.map (subst_ty_param tysub par) ls)
  | ExEffTypes.Handler ((lt, ld), (rt, rd)) -> ExEffTypes.Handler ((subst_ty_param tysub par lt, ld), (subst_ty_param tysub par rt, rd))
  | ExEffTypes.PrimTy p -> ExEffTypes.PrimTy p
  | ExEffTypes.QualTy ((ty1, ty2), ty3) ->
    ExEffTypes.QualTy ((subst_ty_param tysub par ty1, subst_ty_param tysub par ty2), 
        subst_ty_param tysub par ty3)
  | ExEffTypes.QualDirt (dirts, t) -> ExEffTypes.QualDirt (dirts, subst_ty_param tysub par t)
  | ExEffTypes.TySchemeTy (p, skel, t) -> ExEffTypes.TySchemeTy (p, skel, subst_ty_param tysub par t)
  | ExEffTypes.TySchemeDirt (p, t) -> ExEffTypes.TySchemeDirt (p, subst_ty_param tysub par t)
  | ExEffTypes.TySchemeSkel (p, t) -> ExEffTypes.TySchemeSkel (p, subst_ty_param tysub par t)
 
and comp_elab state env c = 
  match c with 
  | ExEff.Value value ->
    let (t, elab) = value_elab state env value in
    ((t, ExEffTypes.empty_dirt), elab)
  | ExEff.LetVal (value, (pat, _, comp)) -> 
    let (tyv, elabv) = value_elab state env value in
    let env' = extend_pattern_type env pat tyv in
    let (tyc, elabc) = comp_elab state env' comp in
    (tyc, NoEff.NLet (elabv, (pattern_elab pat, elabc)))
  | ExEff.LetRec (abs_list, comp) ->
    let rec extend_env env ls = 
      ( match ls with
        | [] -> env
        | ( (var, ty1, ty2, (p, comp)) :: rest ) ->
        let env' = TypeChecker.extend_var_types env var (ExEffTypes.Arrow (ty1, ty2)) in
        let env'' = extend_pattern_type env' p ty1 in
        extend_env env'' rest ) in
      let elab_letrec_abs ( (var, ty1, ty2, (p, compt)) ) =
              ( let (_, t1) = type_elab state env ty1 in
              let (_, t2) = dirty_elab state env ty2 in
              let (_, elabc) = comp_elab state env compt in
              ( (var, t1, t2, (pattern_elab p, elabc)) ) ) in
      let (tycomp, elabcomp) = comp_elab state (extend_env env abs_list) comp in
      ( tycomp, NoEff.NLetRec (List.map (elab_letrec_abs) abs_list, elabcomp) )
  | ExEff.Match (value, abs_lst, loc) ->
    let (tyv, elabv) = value_elab state env value in
    let elab_abs (pat, comp) = 
            ( let (tyc, elabc) = comp_elab state env comp in (pattern_elab pat, elabc) ) in
    ( if ( (List.length abs_lst) = 0)
    then ( failwith "Empty match statement" )
    else ( let ((p1,c1) :: _ ) = abs_lst in
           let (tyc, elabc) = comp_elab state env c1 in 
           (tyc, NoEff.NMatch (elabv, List.map elab_abs abs_lst, loc)) ) )
  | ExEff.Apply (v1, v2) -> 
    let (ty1, elab1) = value_elab state env v1 in
    ( match ty1 with
      | ExEffTypes.Arrow (t1, t2) -> 
        let (ty2, elab2) = value_elab state env v2 in
          if (ty2 = t1)
          then (t2, NoEff.NApplyTerm (elab1, elab2))
          else (failwith "Improper argument type")
      | _ -> failwith "Improper function type" )
  | ExEff.Handle (value, comp) -> 
    let ( (ctype, cdirt), elabc ) = comp_elab state env comp in 
    let ( vtype, velab ) = value_elab state env value in
    ( match vtype with
      | ExEffTypes.Handler ( (vty1, vdirt1), (vty2, vdirt2) ) ->
        if (vty1 = ctype && vdirt1 = cdirt) then (
          if (Types.is_empty_dirt cdirt)
          (* Handle - Case 1 *)
          then ( (vty2, vdirt2), NoEff.NApplyTerm (velab, elabc))
          else (
               if (Types.is_empty_dirt vdirt2)
               (* Handle - Case 2 *)
               then ( let (_, telab) = type_elab state env vty2 in
                 ( (vty2, vdirt2), 
                 NoEff.NCast (NoEff.NHandle (elabc, velab),
                 NoEff.NCoerUnsafe (NoEff.NCoerRefl (telab)))) )
               (* Handle - Case 3 *)
               else ( (vty2, vdirt2), NoEff.NHandle (elabc, velab))
               )
        )
        else failwith "Handler source type and handled computation type do not match"
      | _ -> failwith "Ill-typed handler" )
  | ExEff.Call ((eff, (ty1, ty2)), value, (p, ty, comp)) ->
    let (_, t1) = type_elab state env ty1 in
    let (_, t2) = type_elab state env ty2 in
    let (_, tt) = type_elab state env ty in
    let (vty, velab) = value_elab state env value in
    if (vty = ty1) 
    then (
      let env' = extend_pattern_type env p ty in
      let (cty, celab) = comp_elab state env' comp in
      ( cty, NoEff.NCall ((eff, (t1, t2)), velab, (pattern_elab p, tt, celab)) )
    )
    else failwith "Ill-typed call"
  | ExEff.Op ((eff, (ty1, ty2)), value) -> 
    let (_, t1) = type_elab state env ty1 in
    let (_, t2) = type_elab state env ty2 in
    let (vty, velab) = value_elab state env value in    
    if (vty = ty1)
    then ( ((ty2, ExEffTypes.empty_dirt), NoEff.NOp ((eff, (t1,t2)), velab)) )
    else failwith "Ill-typed operation"
  | ExEff.Bind (c1, (p, c2)) ->
    let ((ty1, dirt1), elab1) = comp_elab state env c1 in
    let env' = extend_pattern_type env p ty1 in
    let ((ty2, dirt2), elab2) = comp_elab state env' c2 in
    if (ExEffTypes.is_empty_dirt dirt1 && ExEffTypes.is_empty_dirt dirt2)
    (* Bind - Case 1 *)
    then ( (ty2, dirt2), NoEff.NLet (elab1, (pattern_elab p, elab2)) )
    (* Bind - Case 2 *)
    else ( (ty2, dirt2), NoEff.NBind (elab1, (pattern_elab p, elab2)) )
  | ExEff.CastComp (comp, coer) -> 
    let ( (t1, t2), elabc ) = coercion_elab_dirty state env coer in
    let ( cty, coelab ) = comp_elab state env comp in
    if (cty = t1) 
    then ( (t2, NoEff.NCast (coelab, elabc) ) )
    else failwith "Ill-typed casting"

