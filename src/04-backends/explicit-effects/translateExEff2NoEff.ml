open Utils
open SyntaxNoEff
open Type
open Term
module TypeCheck = TypeChecker
module NoEff = SyntaxNoEff
module ExEffTypes = Type
module ExEff = Term
module EffectSet = Set.Make (CoreTypes.Effect)
module Sub = Substitution

type effect_set = EffectSet.t

type environment = TypeCheck.state

let typefail str =
  let message = "ExEff-to-NoEff: " ^ str in
  failwith message

let rec extend_pattern_type env pat ty =
  match pat with
  | PVar x -> TypeCheck.extend_var_types env x ty
  | PAs (p, x) -> extend_pattern_type (TypeCheck.extend_var_types env x ty) p ty
  | PTuple ps -> (
      match ty with
      | ExEffTypes.Tuple tys -> extend_multiple_pats env ps tys
      | _ -> failwith "ill-typed tuple")
  | PConst c ->
      if ExEffTypes.type_const c = ty then env
      else typefail "Ill-typed constant"
  | PRecord recs -> (
      match ty with
      | ExEffTypes.Tuple tys ->
          extend_multiple_pats env (Assoc.values_of recs) tys
      | _ -> typefail "Ill-typed record")
  | PVariant (lbl, p) ->
      let ty_in, ty_out = Type.constructor_signature env.tctx_st lbl in
      extend_pattern_type env p ty_in
  | PNonbinding -> env

and extend_multiple_pats env ps tys =
  match (ps, tys) with
  | [], [] -> env
  | x :: xs, ty :: tys ->
      let env' = extend_pattern_type env x ty in
      extend_multiple_pats env' xs tys
  | _, _ -> typefail "Ill-typed tuple"

let rec type_elab state (env : environment) (ty : ExEffTypes.target_ty) =
  match ty with
  | ExEffTypes.TyParam x -> (
      match Assoc.lookup x env.ty_param_skeletons with
      | Some xtype -> (xtype, NoEff.NTyParam x)
      | None -> (Type.SkelBasic Const.IntegerTy, NoEff.NTyParam x))
  | ExEffTypes.Apply (name, lst) ->
      let get_skel x =
        let s, _ = type_elab state env x in
        s
      in
      let get_elab x =
        let _, e = type_elab state env x in
        e
      in
      let skels = List.map get_skel lst in
      let elabs = List.map get_elab lst in
      (ExEffTypes.SkelApply (name, skels), NoEff.NTyApply (name, elabs))
  | ExEffTypes.Arrow (t, dirty) ->
      let ty1, elab1 = type_elab state env t in
      let ty2, elab2 = dirty_elab state env dirty in
      (ExEffTypes.SkelArrow (ty1, ty2), NoEff.NTyArrow (elab1, elab2))
  | ExEffTypes.Handler ((type1, dirt1), (type2, dirt2)) ->
      let ty1, elab1 = type_elab state env type1 in
      if
        ExEffTypes.is_empty_dirt dirt1
        (* Handler type - Case 1: empty input dirt *)
      then
        let ty2, elab2 = dirty_elab state env (type2, dirt2) in
        (ExEffTypes.SkelHandler (ty1, ty2), NoEff.NTyArrow (elab1, elab2))
        (* Handler type - Case 2: non-empty input dirt *)
      else
        let ty2, elab2 = type_elab state env type2 in
        (ExEffTypes.SkelHandler (ty1, ty2), NoEff.NTyHandler (elab1, elab2))
  | ExEffTypes.Tuple tys ->
      let ty_elab_list = List.map (type_elab state env) tys in
      ( ExEffTypes.SkelTuple (List.map fst ty_elab_list),
        NoEff.NTyTuple (List.map snd ty_elab_list) )
  | ExEffTypes.QualTy ((t1, t2), ty) ->
      let type1, elab1 = type_elab state env t1 in
      let type2, elab2 = type_elab state env t2 in
      let type3, elab3 = type_elab state env ty in
      (type3, NoEff.NTyQual ((elab1, elab2), elab3))
  | ExEffTypes.QualDirt (_, ty) -> type_elab state env ty
  | ExEffTypes.TyBasic ty -> (ExEffTypes.SkelBasic ty, NoEff.NTyBasic ty)

and dirty_elab state env (ty, dirt) =
  let skel, elab = type_elab state env ty in
  if ExEffTypes.is_empty_dirt dirt then (skel, elab)
  else (skel, NoEff.NTyComp elab)

and pattern_elab p =
  match p with
  | PVar x -> PNVar x
  | PAs (p, x) -> PNAs (pattern_elab p, x)
  | PTuple ps -> PNTuple (List.map pattern_elab ps)
  | PConst c -> PNConst c
  | PRecord recs -> NoEff.PNRecord (Assoc.map pattern_elab recs)
  | PVariant (l, p) -> NoEff.PNVariant (l, Some (pattern_elab p))
  | PNonbinding -> PNNonbinding

and value_elab (state : ExplicitInfer.state) (env : environment) v =
  match v with
  | ExEff.Var x -> (
      match Assoc.lookup x env.var_types with
      | Some ty -> (ty, NoEff.NVar x)
      | None -> (
          match TypingEnv.lookup state.gblCtxt x with
          | Some ty -> (ty, NoEff.NVar x)
          | None -> failwith "Found no type for variable"))
  | ExEff.Const c -> (ExEffTypes.type_const c, NoEff.NConst c)
  | ExEff.Tuple vs ->
      let type_elab_list = List.map (value_elab state env) vs in
      ( ExEffTypes.Tuple (List.map fst type_elab_list),
        NoEff.NTuple (List.map snd type_elab_list) )
  | ExEff.Lambda (p, t, c) ->
      let _, elab1 = type_elab state env t in
      let env' = extend_pattern_type env p t in
      let type2, elab2 = comp_elab state env' c in
      (ExEffTypes.Arrow (t, type2), NoEff.NFun (pattern_elab p, elab1, elab2))
  | ExEff.Effect (e, (t1, t2)) ->
      let _, elab1 = type_elab state env t1 in
      let _, elab2 = type_elab state env t2 in
      ( ExEffTypes.Arrow
          (t1, (t2, ExEffTypes.closed_dirt (EffectSet.singleton e))),
        NoEff.NEffect (e, (elab1, elab2)) )
  | ExEff.Handler h ->
      let p, t, c = h.value_clause in
      let _, elabt = type_elab state env t in
      let env' = extend_pattern_type env p t in
      let typec, elabc = comp_elab state env' c in

      if Assoc.length h.effect_clauses = 0 (* Handler - Case 1 *) then
        ( ExEffTypes.Handler ((t, ExEffTypes.empty_dirt), typec),
          NoEff.NFun (pattern_elab p, elabt, elabc) )
      else
        let ty, dirt = typec in
        if ExEffTypes.is_empty_dirt dirt (* Handler - Case 2 *) then
          let subst_cont_effect ((eff, (ty1, ty2)), (p1, p2, comp)) =
            let _, elab1 = type_elab state env ty1 in
            let _, elab2 = type_elab state env ty2 in
            let env' = extend_pattern_type env p1 ty1 in
            let env'' =
              extend_pattern_type env' p2
                (ExEffTypes.Arrow (ty2, (ty, ExEffTypes.empty_dirt)))
            in
            let _, elabcomp = comp_elab state env'' comp in
            match p2 with
            | PVar x ->
                ( (eff, (elab1, elab2)),
                  ( pattern_elab p1,
                    pattern_elab p2,
                    NReturn
                      (subs_var_in_term x
                         (NCast
                            ( NVar x,
                              NoEff.NCoerArrow
                                ( NoEff.NCoerRefl elab1,
                                  NoEff.NCoerUnsafe (NoEff.NCoerRefl elab2) ) ))
                         elabcomp) ) )
            | _ -> failwith "STIEN: wrong elab handler case 2"
          in
          let effectset = get_effectset (Assoc.to_list h.effect_clauses) in
          ( ExEffTypes.Handler ((t, ExEffTypes.closed_dirt effectset), typec),
            NoEff.NHandler
              {
                return_clause = (pattern_elab p, elabt, elabc);
                effect_clauses =
                  Assoc.map_of_list subst_cont_effect
                    (Assoc.to_list h.effect_clauses);
              } ) (* Handler - Case 3 *)
        else
          let elab_effect_clause ((eff, (ty1, ty2)), (p1, p2, comp)) =
            let _, elab1 = type_elab state env ty1 in
            let _, elab2 = type_elab state env ty2 in
            let env' = extend_pattern_type env p1 ty1 in
            let env'' =
              extend_pattern_type env' p2
                (ExEffTypes.Arrow (ty2, (ty, ExEffTypes.empty_dirt)))
            in
            let _, elabcomp = comp_elab state env'' comp in
            ((eff, (elab1, elab2)), (pattern_elab p1, pattern_elab p2, elabcomp))
          in
          let effectset = get_effectset (Assoc.to_list h.effect_clauses) in
          ( ExEffTypes.Handler ((t, ExEffTypes.closed_dirt effectset), typec),
            NoEff.NHandler
              {
                return_clause = (pattern_elab p, elabt, elabc);
                effect_clauses =
                  Assoc.map_of_list elab_effect_clause
                    (Assoc.to_list h.effect_clauses);
              } )
  | ExEff.CastExp (value, coer) ->
      let ty1, elab1 = value_elab state env value in
      let (ty2, r), elab2 = coercion_elab_ty state env coer in
      if Type.types_are_equal ty1 ty2 then (r, NoEff.NCast (elab1, elab2))
      else typefail "Ill-typed cast"
  | ExEff.LambdaTyCoerVar (par, (ty1, ty2), value) ->
      let _, elab1 = type_elab state env ty1 in
      let _, elab2 = type_elab state env ty2 in
      let env' = TypeCheck.extend_ty_coer_types env par (ty1, ty2) in
      let typev, elabv = value_elab state env' v in
      ( ExEffTypes.QualTy ((ty1, ty2), typev),
        NoEff.NBigLambdaCoer (par, (elab1, elab2), elabv) )
  | ExEff.LambdaDirtCoerVar (par, (dirt1, dirt2), value) ->
      let env' = TypeCheck.extend_dirt_coer_types env par (dirt1, dirt2) in
      let typev, elabv = value_elab state env' value in
      (ExEffTypes.QualDirt ((dirt1, dirt2), typev), elabv)
  | ExEff.ApplyTyCoercion (value, coer) -> (
      let (ty1, ty2), elabc = coercion_elab_ty state env coer in
      let ty, elabv = value_elab state env value in
      match ty with
      | ExEffTypes.QualTy ((ty1', ty2'), t) ->
          if ty1 = ty1' && ty2 = ty2' then (t, NoEff.NApplyCoer (elabv, elabc))
          else typefail "Ill-typed coercion application"
      | _ -> typefail "Ill-typed coercion application")
  | ExEff.ApplyDirtCoercion (value, coer) -> (
      let ty, elabv = value_elab state env value in
      let dirt1, dirt2 = coer_elab_dirt state env coer in
      match ty with
      | ExEffTypes.QualDirt ((dirt1', dirt2'), t) ->
          if dirt1' = dirt1 && dirt2' = dirt2 then (t, elabv)
          else typefail "Ill-typed coercion application"
      | _ -> failwith "Ill-typed coercion application")
  | ExEff.Variant (lbl, exp) ->
      let ty_in, ty_out = Type.constructor_signature env.tctx_st lbl in
      let ty_e, elab_e = value_elab state env exp in
      assert (Type.types_are_equal ty_e ty_in);
      (ty_out, NoEff.NVariant (lbl, Some elab_e))
  | ExEff.Record ass -> failwith "records not supported yet"

and coercion_elab_ty state env coer =
  match coer with
  | Constraint.ReflTy ty ->
      let _, tyelab = type_elab state env ty in
      ((ty, ty), NoEff.NCoerRefl tyelab)
  | Constraint.ArrowCoercion (tycoer, dirtycoer) ->
      let (tycoer2, tycoer1), tyelab = coercion_elab_ty state env tycoer in
      let (dcoer1, dcoer2), dirtyelab = coer_elab_dirty state env dirtycoer in
      ( (ExEffTypes.Arrow (tycoer1, dcoer1), ExEffTypes.Arrow (tycoer2, dcoer2)),
        NoEff.NCoerArrow (tyelab, dirtyelab) )
  | Constraint.HandlerCoercion (coerA, coerB) -> (
      let (coerA2, coerA1), elabA = coer_elab_dirty state env coerA in
      let (coerB1, coerB2), elabB = coer_elab_dirty state env coerB in
      if
        has_empty_dirt coerA1 && has_empty_dirt coerA2
        (* Handler coercion - Case 1 *)
      then
        ( ( ExEffTypes.Handler (coerA1, coerB1),
            ExEffTypes.Handler (coerA2, coerB2) ),
          NoEff.NCoerArrow (elabA, elabB) )
      else
        match coerB with
        | Constraint.BangCoercion (tycoer, dirtcoer) -> (
            let (t1', t2'), elab2 = coercion_elab_ty state env tycoer in
            if
              (not (has_empty_dirt coerA2)) && not (has_empty_dirt coerA2)
              (* Handler coercion - Case 2 *)
            then
              ( ( ExEffTypes.Handler (coerA1, coerB1),
                  ExEffTypes.Handler (coerA2, coerB2) ),
                NoEff.NCoerHandler (elabA, NoEff.NCoerComp elab2) )
            else
              match coerA with
              | Constraint.BangCoercion (tycoerA, dirtcoerA) ->
                  let (t2, t1), elab1 = coercion_elab_ty state env tycoerA in
                  if
                    has_empty_dirt coerB1
                    && (not (has_empty_dirt coerA1))
                    && has_empty_dirt coerA2
                    (* Handler coercion - Case 3 *)
                  then
                    ( ( ExEffTypes.Handler (coerA1, coerB1),
                        ExEffTypes.Handler (coerA2, coerB2) ),
                      NoEff.NCoerHandToFun (elab1, NoEff.NCoerUnsafe elab2) )
                  else if
                    has_empty_dirt coerA2
                    && (not (has_empty_dirt coerA1))
                    && not (has_empty_dirt coerB1)
                    (* Handler coercion - Case 4 *)
                  then
                    ( ( ExEffTypes.Handler (coerA1, coerB1),
                        ExEffTypes.Handler (coerA2, coerB2) ),
                      NoEff.NCoerHandToFun (elab1, elab2) )
                  else failwith "Ill-typed handler coercion"
              | _ -> failwith "Ill-typed handler coercion left side")
        | _ -> failwith "Ill-typed handler coercion right side")
  | Constraint.TyCoercionVar par -> (
      match Assoc.lookup par env.ty_coer_types with
      | Some xtype -> (xtype, NoEff.NCoerVar par)
      | None -> failwith "Coercion variable out of scope")
  | Constraint.SequenceTyCoer (coer1, coer2) ->
      let (coer1ty1, coer1ty2), elab1 = coercion_elab_ty state env coer1 in
      let (coer2ty1, coer2ty2), elab2 = coercion_elab_ty state env coer2 in
      if coer1ty2 = coer2ty1 then
        ((coer1ty1, coer2ty2), NoEff.NCoerTrans (elab1, elab2))
      else failwith "Ill-typed coercion sequencing"
  | Constraint.ApplyCoercion (name, coer_list) ->
      let type_list =
        List.map (fun x -> fst (coercion_elab_ty state env x)) coer_list
      in
      let ty1s = List.map fst type_list in
      let ty2s = List.map snd type_list in
      let elab_list =
        List.map (fun x -> snd (coercion_elab_ty state env x)) coer_list
      in
      ( (ExEffTypes.Tuple ty1s, ExEffTypes.Tuple ty2s),
        NoEff.NCoerApply (name, elab_list) )
  | Constraint.TupleCoercion lst ->
      let elabs = List.map (coercion_elab_ty state env) lst in
      let tylist = List.map fst elabs in
      let elablist = List.map snd elabs in
      ( ( ExEffTypes.Tuple (List.map fst tylist),
          ExEffTypes.Tuple (List.map snd tylist) ),
        NoEff.NCoerTuple elablist )
  | Constraint.LeftArrow c -> (
      match c with
      | Constraint.ArrowCoercion (c1, c2) ->
          let ty, _ = coercion_elab_ty state env c1 in
          let _, elab = coercion_elab_ty state env c in
          (ty, NoEff.NCoerLeftArrow elab)
      | _ -> failwith "Ill-formed left arrow coercion")
  | Constraint.PureCoercion c ->
      let ((ty1, _), (ty2, _)), elabc = coer_elab_dirty state env c in
      ((ty1, ty2), NoEff.NCoerPure elabc)
  | Constraint.QualTyCoer ((ty1, ty2), c) ->
      let (tyc1, tyc2), elabc = coercion_elab_ty state env c in
      let _, ty1elab = type_elab state env ty1 in
      let _, ty2elab = type_elab state env ty2 in
      ( ( ExEffTypes.QualTy ((ty1, ty2), tyc1),
          ExEffTypes.QualTy ((ty1, ty2), tyc2) ),
        NoEff.NCoerQual ((ty1elab, ty2elab), elabc) )
  | Constraint.QualDirtCoer (dirts, c) ->
      let tyc, elabc = coercion_elab_ty state env c in
      ( ( ExEffTypes.QualDirt (dirts, fst tyc),
          ExEffTypes.QualDirt (dirts, snd tyc) ),
        elabc )
  | Constraint.ApplyQualTyCoer (c1, c2) -> (
      let c2ty, c2elab = coercion_elab_ty state env c2 in
      match c1 with
      | Constraint.QualTyCoer (tys, ccty) ->
          if c2ty = tys then
            let (ty1, ty2), ccelab = coercion_elab_ty state env ccty in
            ((ty1, ty2), NoEff.NCoerApp (ccelab, c2elab))
          else failwith "Ill-typed coercion application"
      | _ -> failwith "Ill-typed coercion application")
  | Constraint.ApplyQualDirtCoer (c1, c2) -> (
      match c1 with
      | Constraint.QualDirtCoer (ds, ccd) ->
          if coer_elab_dirt state env c2 = ds then
            coercion_elab_ty state env ccd
          else failwith "Ill-typed coercion application"
      | _ -> failwith "Ill-typed coercion application")

and coer_elab_dirty state env (coer : Constraint.dirty_coercion) =
  match coer with
  | Constraint.BangCoercion (tcoer, dcoer) ->
      let (ty1, ty2), tyelab = coercion_elab_ty state env tcoer in
      let d1, d2 = coer_elab_dirt state env dcoer in
      if is_empty_dirt d1 && is_empty_dirt d2 then
        (((ty1, d1), (ty2, d2)), tyelab)
      else if is_empty_dirt d1 then
        (((ty1, d1), (ty2, d2)), NoEff.NCoerReturn tyelab)
      else if not (is_empty_dirt d2) then
        (((ty1, d1), (ty2, d2)), NoEff.NCoerComp tyelab)
      else failwith "Ill-typed bang coercion"
  | Constraint.RightArrow tycoer -> (
      let (ty1, ty2), tyelab = coercion_elab_ty state env tycoer in
      match ty1 with
      | ExEffTypes.Arrow (a, b) -> (
          match ty2 with
          | ExEffTypes.Arrow (c, d) -> ((b, d), NoEff.NCoerRightArrow tyelab)
          | _ -> failwith "Ill-typed right arrow coercion")
      | _ -> failwith "Ill-typed right arrow coercion")
  | Constraint.RightHandler tycoer -> (
      let (ty1, ty2), tyelab = coercion_elab_ty state env tycoer in
      match ty1 with
      | ExEffTypes.Handler (a, b) -> (
          match ty2 with
          | ExEffTypes.Handler (c, d) -> ((b, d), NoEff.NCoerRightHandler tyelab)
          | _ -> failwith "Ill-typed right handler coercion")
      | _ -> failwith "Ill-typed right handler coercion")
  | Constraint.LeftHandler tycoer -> (
      let (ty1, ty2), tyelab = coercion_elab_ty state env tycoer in
      match ty1 with
      | ExEffTypes.Handler (a, b) -> (
          match ty2 with
          | ExEffTypes.Handler (c, d) -> ((c, a), NoEff.NCoerLeftHandler tyelab)
          | _ -> failwith "Ill-typed left handler coercion")
      | _ -> failwith "Ill-typed left handler coercion")
  | Constraint.SequenceDirtyCoer (c1, c2) ->
      let (ty11, ty12), c1elab = coer_elab_dirty state env c1 in
      let (ty21, ty22), c2elab = coer_elab_dirty state env c2 in
      if ty12 = ty21 then ((ty11, ty22), NoEff.NCoerTrans (c1elab, c2elab))
      else failwith "Ill-typed coercion sequence"

and coer_elab_dirt state env dcoer =
  match dcoer with
  | Constraint.ReflDirt dirt -> (dirt, dirt)
  | Constraint.DirtCoercionVar par -> (
      match Assoc.lookup par env.dirt_coer_types with
      | Some dirts -> dirts
      | None -> failwith "Dirt coercion variable out of scope")
  | Constraint.Empty dirt -> (ExEffTypes.empty_dirt, dirt)
  | Constraint.UnionDirt (set, dc) ->
      let d1, d2 = coer_elab_dirt state env dc in
      let d1' =
        { row = d1.row; effect_set = EffectSet.union set d1.effect_set }
      in
      let d2' =
        { row = d2.row; effect_set = EffectSet.union set d2.effect_set }
      in
      (d1', d2')
  | Constraint.SequenceDirtCoer (d1, d2) ->
      let dirt11, dirt12 = coer_elab_dirt state env d1 in
      let dirt21, dirt22 = coer_elab_dirt state env d2 in
      if dirt12 = dirt21 then (dirt11, dirt22)
      else failwith "Ill-typed dirt coercion sequencing"
  | Constraint.DirtCoercion dirty_coercion ->
      let (dirtyA, dirtyB), _ = coer_elab_dirty state env dirty_coercion in
      let tyA, dA = dirtyA in
      let tyB, dB = dirtyB in
      (dA, dB)

and get_effectset effects = get_effectset_temp EffectSet.empty effects

and get_effectset_temp set effects =
  match effects with
  | ((eff, _), abs) :: es -> get_effectset_temp (EffectSet.add eff set) es
  | [] -> set

and subst_ty_param tysub par ty =
  match ty with
  | ExEffTypes.TyParam x -> if x = par then tysub else ty
  | ExEffTypes.Apply (n, ls) ->
      ExEffTypes.Apply (n, List.map (subst_ty_param tysub par) ls)
  | ExEffTypes.Arrow (l, (rt, rd)) ->
      ExEffTypes.Arrow
        (subst_ty_param tysub par l, (subst_ty_param tysub par rt, rd))
  | ExEffTypes.Tuple ls ->
      ExEffTypes.Tuple (List.map (subst_ty_param tysub par) ls)
  | ExEffTypes.Handler ((lt, ld), (rt, rd)) ->
      ExEffTypes.Handler
        ((subst_ty_param tysub par lt, ld), (subst_ty_param tysub par rt, rd))
  | ExEffTypes.TyBasic p -> ExEffTypes.TyBasic p
  | ExEffTypes.QualTy ((ty1, ty2), ty3) ->
      ExEffTypes.QualTy
        ( (subst_ty_param tysub par ty1, subst_ty_param tysub par ty2),
          subst_ty_param tysub par ty3 )
  | ExEffTypes.QualDirt (dirts, t) ->
      ExEffTypes.QualDirt (dirts, subst_ty_param tysub par t)

and subs_var_in_term par subs term =
  match term with
  | NVar v -> if v = par then subs else term
  | NTuple ls -> NTuple (List.map (subs_var_in_term par subs) ls)
  | NFun (p, t, c) -> NFun (p, t, subs_var_in_term par subs c)
  | NApplyTerm (t1, t2) ->
      NApplyTerm (subs_var_in_term par subs t1, subs_var_in_term par subs t2)
  | NCast (t, c) -> NCast (subs_var_in_term par subs t, c)
  | NReturn t -> NReturn (subs_var_in_term par subs t)
  | NHandler h -> NHandler h
  | NLet (t, (p, c)) ->
      NLet (subs_var_in_term par subs t, (p, subs_var_in_term par subs c))
  | NCall (eff, t, (p, ty, c)) ->
      NCall
        (eff, subs_var_in_term par subs t, (p, ty, subs_var_in_term par subs c))
  | NBind (t, (p, c)) ->
      NBind (subs_var_in_term par subs t, (p, subs_var_in_term par subs c))
  | NHandle (t1, t2) ->
      NHandle (subs_var_in_term par subs t1, subs_var_in_term par subs t2)
  | NConst c -> NConst c
  | NEffect e -> NEffect e
  | NLetRec (abss, t) ->
      let subs_letrec (var, ty1, ty2, (p, c)) =
        (var, ty1, ty2, (p, subs_var_in_term par subs c))
      in
      NoEff.NLetRec (List.map subs_letrec abss, subs_var_in_term par subs t)
  | NMatch (t, ty, abss, loc) ->
      let subs_abs (p, c) = (p, subs_var_in_term par subs c) in
      NoEff.NMatch (subs_var_in_term par subs t, ty, List.map subs_abs abss, loc)
  | NOp (eff, t) -> NOp (eff, subs_var_in_term par subs t)
  | NRecord a -> NRecord (Assoc.map (subs_var_in_term par subs) a)
  | NVariant (lbl, None) -> NVariant (lbl, None)
  | NVariant (lbl, Some t) -> NVariant (lbl, Some (subs_var_in_term par subs t))
  | _ -> failwith __LOC__

and comp_elab state env c =
  match c with
  | ExEff.Value value ->
      let t, elab = value_elab state env value in
      ((t, ExEffTypes.empty_dirt), elab)
  | ExEff.LetVal (value, (pat, _, comp)) ->
      let tyv, elabv = value_elab state env value in
      let env' = extend_pattern_type env pat tyv in
      let tyc, elabc = comp_elab state env' comp in
      (tyc, NoEff.NLet (elabv, (pattern_elab pat, elabc)))
  | ExEff.LetRec (abs_list, comp) ->
      let rec extend_env env ls =
        match ls with
        | [] -> env
        | (var, ty1, ty2, (p, comp)) :: rest ->
            let env' =
              TypeChecker.extend_var_types env var (ExEffTypes.Arrow (ty1, ty2))
            in
            let env'' = extend_pattern_type env' p ty1 in
            extend_env env'' rest
      in
      let elab_letrec_abs (var, ty1, ty2, (p, compt)) =
        let _, t1 = type_elab state env ty1 in
        let _, t2 = dirty_elab state env ty2 in
        let _, elabc = comp_elab state (extend_env env abs_list) compt in
        (var, t1, t2, (pattern_elab p, elabc))
      in
      let tycomp, elabcomp = comp_elab state (extend_env env abs_list) comp in
      (tycomp, NoEff.NLetRec (List.map elab_letrec_abs abs_list, elabcomp))
  | ExEff.Match (value, ty, abs_lst) -> (
      let tyv, elabv = value_elab state env value in
      let tyskel, tyelab = dirty_elab state env ty in
      let elab_abs vty cty (pat, comp) =
        let env' = extend_pattern_type env pat tyv in
        let tyc, elabc = comp_elab state env' comp in
        if Type.types_are_equal (fst tyc) (fst cty) then
          (pattern_elab pat, elabc)
        else typefail "Ill-typed match branch"
      in
      match abs_lst with
      | [] -> (ty, NoEff.NMatch (elabv, tyelab, [], Location.unknown))
      | (p1, c1) :: _ ->
          let env' = extend_pattern_type env p1 tyv in
          let tyc, elabc = comp_elab state env' c1 in
          ( tyc,
            NoEff.NMatch
              ( elabv,
                tyelab,
                List.map (elab_abs tyv tyc) abs_lst,
                Location.unknown ) ))
  | ExEff.Apply (v1, v2) -> (
      let ty1, elab1 = value_elab state env v1 in
      match ty1 with
      | ExEffTypes.Arrow (t1, t2) ->
          let ty2, elab2 = value_elab state env v2 in
          if ty2 = t1 then (t2, NoEff.NApplyTerm (elab1, elab2))
          else failwith "Improper argument type"
      | _ -> failwith "Improper function type")
  | ExEff.Handle (value, comp) -> (
      let (ctype, cdirt), elabc = comp_elab state env comp in
      let vtype, velab = value_elab state env value in
      match (vtype, velab) with
      | ExEffTypes.Handler ((vty1, vdirt1), (vty2, vdirt2)), NHandler handler ->
          (* Filip: I think this tests the wrong type, it is either strange,
             or the computation is wrongly wrapped.
          *)
          (* Format.printf
             "vty1: %t; vty2: %t;\n base_comp: %t \n;; comp: %t \n:: ctype %t\n"
             (Type.print_target_ty vty1)
             (Type.print_target_ty vty2)
             (Typed.print_computation comp)
             (SyntaxNoEff.print_term elabc)
             (Types.print_target_ty ctype); *)
          if true && Type.types_are_equal vty1 ctype then
            if Type.is_empty_dirt cdirt (* Handle - Case 1 *) then
              ((vty2, vdirt2), NoEff.NApplyTerm (velab, elabc))
            else if Type.is_empty_dirt vdirt2 (* Handle - Case 2 *) then
              let _, telab = type_elab state env vty2 in
              ( (vty2, vdirt2),
                NoEff.NCast
                  ( NoEff.NHandle (elabc, velab),
                    NoEff.NCoerUnsafe (NoEff.NCoerRefl telab) ) )
              (* Handle - Case 3 *)
            else ((vty2, vdirt2), NoEff.NHandle (elabc, velab))
          else
            failwith
              "Handler source type and handled computation type do not match"
      | _ -> failwith "Ill-typed handler")
  | ExEff.Call ((eff, (ty1, ty2)), value, (p, ty, comp)) ->
      let _, t1 = type_elab state env ty1 in
      let _, t2 = type_elab state env ty2 in
      let _, tt = type_elab state env ty in
      let vty, velab = value_elab state env value in
      if vty = ty1 then
        let env' = extend_pattern_type env p ty in
        let cty, celab = comp_elab state env' comp in
        (cty, NoEff.NCall ((eff, (t1, t2)), velab, (pattern_elab p, tt, celab)))
      else failwith "Ill-typed call"
  | ExEff.Op ((eff, (ty1, ty2)), value) ->
      let _, t1 = type_elab state env ty1 in
      let _, t2 = type_elab state env ty2 in
      let vty, velab = value_elab state env value in
      if vty = ty1 then
        ((ty2, ExEffTypes.empty_dirt), NoEff.NOp ((eff, (t1, t2)), velab))
      else typefail "Ill-typed operation"
  | ExEff.Bind (c1, (p, c2)) ->
      let (ty1, dirt1), elab1 = comp_elab state env c1 in
      let env' = extend_pattern_type env p ty1 in
      let (ty2, dirt2), elab2 = comp_elab state env' c2 in
      if
        ExEffTypes.is_empty_dirt dirt1 && ExEffTypes.is_empty_dirt dirt2
        (* Bind - Case 1 *)
      then ((ty2, dirt2), NoEff.NLet (elab1, (pattern_elab p, elab2)))
        (* Bind - Case 2 *)
      else ((ty2, dirt2), NoEff.NBind (elab1, (pattern_elab p, elab2)))
  | ExEff.CastComp (comp, coer) ->
      let (t1, t2), elabc = coer_elab_dirty state env coer in
      let cty, coelab = comp_elab state env comp in
      if Type.types_are_equal (fst cty) (fst t1) then
        (t2, NoEff.NCast (coelab, elabc))
      else typefail "Ill-typed cast"

and elab_ty = function
  | Language.Type.Apply (name, ts) -> NoEff.NTyApply (name, List.map elab_ty ts)
  | TyParam p -> NoEff.NTyParam p
  | Basic s -> NoEff.NTyBasic s
  | Tuple tys -> NoEff.NTyTuple (List.map elab_ty tys)
  | Arrow (t1, t2) -> NoEff.NTyArrow (elab_ty t1, elab_ty t2)
  | Handler h -> NoEff.NTyHandler (elab_ty h.value, elab_ty h.finally)

and elab_tydef = function
  | Language.Type.Record assoc -> NoEff.TyDefRecord (Assoc.map elab_ty assoc)
  | Sum assoc ->
      let converter = function None -> None | Some ty -> Some (elab_ty ty) in
      NoEff.TyDefSum (Assoc.map converter assoc)
  | Inline ty -> NoEff.TyDefInline (elab_ty ty)

and has_empty_dirt ((ty, dirt) : ExEffTypes.target_dirty) = is_empty_dirt dirt
