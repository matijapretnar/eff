open Utils
open SyntaxNoEff
open Type
open Term
module NoEff = SyntaxNoEff
module ExEffTypes = Type
module ExEff = Term
module EffectSet = Set.Make (CoreTypes.Effect)
module Sub = Substitution

type effect_set = EffectSet.t

type state = {
  var_types : (Term.variable, Type.ty) Assoc.t;
  ty_params : CoreTypes.TyParam.t list;
  dirt_params : Type.DirtParam.t list;
  skel_params : Type.SkelParam.t list;
  ty_param_skeletons : (CoreTypes.TyParam.t, Type.skeleton) Assoc.t;
  ty_coer_types : (Type.TyCoercionParam.t, Type.ct_ty) Assoc.t;
  dirt_coer_types : (Type.DirtCoercionParam.t, Type.ct_dirt) Assoc.t;
  tctx_st : TypeContext.state;
}

let initial_state =
  {
    var_types = Assoc.empty;
    ty_params = [];
    dirt_params = [];
    skel_params = [];
    ty_param_skeletons = Assoc.empty;
    ty_coer_types = Assoc.empty;
    dirt_coer_types = Assoc.empty;
    tctx_st = TypeContext.initial_state;
  }

let extend_ty_params st ty_var = { st with ty_params = ty_var :: st.ty_params }

let extend_dirt_params st dirt_var =
  { st with dirt_params = dirt_var :: st.dirt_params }

let extend_skel_params st sk_var =
  { st with skel_params = sk_var :: st.skel_params }

let extend_var_types st t_var tty =
  { st with var_types = Assoc.update t_var tty st.var_types }

let extend_ty_coer_types st tcp ctty =
  { st with ty_coer_types = Assoc.update tcp ctty st.ty_coer_types }

let extend_dirt_coer_types st tcp ctdrt =
  { st with dirt_coer_types = Assoc.update tcp ctdrt st.dirt_coer_types }

let extend_ty_param_skeletons st tv sk =
  { st with ty_param_skeletons = Assoc.update tv sk st.ty_param_skeletons }

let typefail str =
  let message = "ExEff-to-NoEff: " ^ str in
  failwith message

let rec elab_ty state (ty : ExEffTypes.ty) =
  match ty with
  | ExEffTypes.TyParam (x, skel) -> (skel, NoEff.NTyParam x)
  | ExEffTypes.Apply (name, lst) ->
      let get_skel x =
        let s, _ = elab_ty state x in
        s
      in
      let get_elab x =
        let _, e = elab_ty state x in
        e
      in
      let skels = List.map get_skel lst in
      let elabs = List.map get_elab lst in
      (ExEffTypes.SkelApply (name, skels), NoEff.NTyApply (name, elabs))
  | ExEffTypes.Arrow (t, dirty) ->
      let ty1, elab1 = elab_ty state t in
      let ty2, elab2 = elab_dirty state dirty in
      (ExEffTypes.SkelArrow (ty1, ty2), NoEff.NTyArrow (elab1, elab2))
  | ExEffTypes.Handler ((type1, dirt1), (type2, dirt2)) ->
      let ty1, elab1 = elab_ty state type1 in
      if
        ExEffTypes.is_empty_dirt dirt1
        (* Handler type - Case 1: empty input dirt *)
      then
        let ty2, elab2 = elab_dirty state (type2, dirt2) in
        (ExEffTypes.SkelHandler (ty1, ty2), NoEff.NTyArrow (elab1, elab2))
        (* Handler type - Case 2: non-empty input dirt *)
      else
        let ty2, elab2 = elab_ty state type2 in
        (ExEffTypes.SkelHandler (ty1, ty2), NoEff.NTyHandler (elab1, elab2))
  | ExEffTypes.Tuple tys ->
      let ty_elab_list = List.map (elab_ty state) tys in
      ( ExEffTypes.SkelTuple (List.map fst ty_elab_list),
        NoEff.NTyTuple (List.map snd ty_elab_list) )
  | ExEffTypes.QualTy ((t1, t2), ty) ->
      let type1, elab1 = elab_ty state t1 in
      let type2, elab2 = elab_ty state t2 in
      let type3, elab3 = elab_ty state ty in
      (type3, NoEff.NTyQual ((elab1, elab2), elab3))
  | ExEffTypes.QualDirt (_, ty) -> elab_ty state ty
  | ExEffTypes.TyBasic ty -> (ExEffTypes.SkelBasic ty, NoEff.NTyBasic ty)

and elab_dirty state (ty, dirt) =
  let skel, elab = elab_ty state ty in
  if ExEffTypes.is_empty_dirt dirt then (skel, elab)
  else (skel, NoEff.NTyComp elab)

let has_empty_dirt ((_ty, dirt) : ExEffTypes.dirty) = is_empty_dirt dirt

let rec get_effectset_temp set effects =
  match effects with
  | ((eff, _), _abs) :: es -> get_effectset_temp (EffectSet.add eff set) es
  | [] -> set

let get_effectset effects = get_effectset_temp EffectSet.empty effects

let rec elab_ty_coercion state coer =
  match coer with
  | Constraint.ReflTy ty ->
      let _, tyelab = elab_ty state ty in
      ((ty, ty), NoEff.NCoerRefl tyelab)
  | Constraint.ArrowCoercion (tycoer, dirtycoer) ->
      let (tycoer2, tycoer1), tyelab = elab_ty_coercion state tycoer in
      let (dcoer1, dcoer2), dirtyelab = elab_dirty_coercion state dirtycoer in
      ( (ExEffTypes.Arrow (tycoer1, dcoer1), ExEffTypes.Arrow (tycoer2, dcoer2)),
        NoEff.NCoerArrow (tyelab, dirtyelab) )
  | Constraint.HandlerCoercion (coerA, coerB) -> (
      let (coerA2, coerA1), elabA = elab_dirty_coercion state coerA in
      let (coerB1, coerB2), elabB = elab_dirty_coercion state coerB in
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
            let (t1', t2'), elab2 = elab_ty_coercion state tycoer in
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
                  let (t2, t1), elab1 = elab_ty_coercion state tycoerA in
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
                  else failwith "Ill-typed handler coercion"))
  | Constraint.TyCoercionVar par -> (
      match Assoc.lookup par state.ty_coer_types with
      | Some xtype -> (xtype, NoEff.NCoerVar par)
      | None -> failwith "Coercion variable out of scope")
  | Constraint.ApplyCoercion (name, coer_list) ->
      let type_list =
        List.map (fun x -> fst (elab_ty_coercion state x)) coer_list
      in
      let ty1s = List.map fst type_list in
      let ty2s = List.map snd type_list in
      let elab_list =
        List.map (fun x -> snd (elab_ty_coercion state x)) coer_list
      in
      ( (ExEffTypes.Tuple ty1s, ExEffTypes.Tuple ty2s),
        NoEff.NCoerApply (name, elab_list) )
  | Constraint.TupleCoercion lst ->
      let elabs = List.map (elab_ty_coercion state) lst in
      let tylist = List.map fst elabs in
      let elablist = List.map snd elabs in
      ( ( ExEffTypes.Tuple (List.map fst tylist),
          ExEffTypes.Tuple (List.map snd tylist) ),
        NoEff.NCoerTuple elablist )
  | Constraint.QualTyCoer ((ty1, ty2), c) ->
      let (tyc1, tyc2), elabc = elab_ty_coercion state c in
      let _, ty1elab = elab_ty state ty1 in
      let _, ty2elab = elab_ty state ty2 in
      ( ( ExEffTypes.QualTy ((ty1, ty2), tyc1),
          ExEffTypes.QualTy ((ty1, ty2), tyc2) ),
        NoEff.NCoerQual ((ty1elab, ty2elab), elabc) )
  | Constraint.QualDirtCoer (dirts, c) ->
      let tyc, elabc = elab_ty_coercion state c in
      ( ( ExEffTypes.QualDirt (dirts, fst tyc),
          ExEffTypes.QualDirt (dirts, snd tyc) ),
        elabc )

and elab_dirty_coercion state (coer : Constraint.dirty_coercion) =
  match coer with
  | Constraint.BangCoercion (tcoer, dcoer) ->
      let (ty1, ty2), tyelab = elab_ty_coercion state tcoer in
      let d1, d2 = elab_dirt_coercion state dcoer in
      if is_empty_dirt d1 && is_empty_dirt d2 then
        (((ty1, d1), (ty2, d2)), tyelab)
      else if is_empty_dirt d1 then
        (((ty1, d1), (ty2, d2)), NoEff.NCoerReturn tyelab)
      else if not (is_empty_dirt d2) then
        (((ty1, d1), (ty2, d2)), NoEff.NCoerComp tyelab)
      else failwith "Ill-typed bang coercion"

and elab_dirt_coercion state dcoer =
  match dcoer with
  | Constraint.ReflDirt dirt -> (dirt, dirt)
  | Constraint.DirtCoercionVar par -> (
      match Assoc.lookup par state.dirt_coer_types with
      | Some dirts -> dirts
      | None -> failwith "Dirt coercion variable out of scope")
  | Constraint.Empty dirt -> (ExEffTypes.empty_dirt, dirt)
  | Constraint.UnionDirt (set, dc) ->
      let d1, d2 = elab_dirt_coercion state dc in
      let d1' =
        { row = d1.row; effect_set = EffectSet.union set d1.effect_set }
      in
      let d2' =
        { row = d2.row; effect_set = EffectSet.union set d2.effect_set }
      in
      (d1', d2')

let rec extend_pattern_type state pat ty =
  match (pat, ty) with
  | PVar x, _ -> extend_var_types state x ty
  | PAs (p, x), _ -> extend_pattern_type (extend_var_types state x ty) p ty
  | PTuple ps, ExEffTypes.Tuple tys -> extend_multiple_pats state ps tys
  | PConst c, _ when ExEffTypes.type_const c = ty -> state
  | PRecord _, _ -> failwith __LOC__
  | PVariant (lbl, p), _ ->
      let ty_in, _ty_out = Type.constructor_signature state.tctx_st lbl in
      extend_pattern_type state p ty_in
  | PNonbinding, _ -> state
  | _, _ -> failwith "Ill-typed pattern"

and extend_multiple_pats state ps tys =
  match (ps, tys) with
  | [], [] -> state
  | x :: xs, ty :: tys ->
      let state' = extend_pattern_type state x ty in
      extend_multiple_pats state' xs tys
  | _, _ -> typefail "Ill-typed tuple"

and elab_pattern p =
  match p with
  | PVar x -> PNVar x
  | PAs (p, x) -> PNAs (elab_pattern p, x)
  | PTuple ps -> PNTuple (List.map elab_pattern ps)
  | PConst c -> PNConst c
  | PRecord recs -> NoEff.PNRecord (Assoc.map elab_pattern recs)
  | PVariant (l, p) -> NoEff.PNVariant (l, Some (elab_pattern p))
  | PNonbinding -> PNNonbinding

let rec elab_expression state exp =
  let ty, trm = elab_expression' state exp in
  (ty, trm)

and elab_expression' state exp =
  match exp with
  | ExEff.Var x -> (
      match Assoc.lookup x state.var_types with
      | Some ty -> (ty, NoEff.NVar x)
      | None ->
          Error.runtime "Found no type for variable %t"
            (CoreTypes.Variable.print x))
  | ExEff.Const c -> (ExEffTypes.type_const c, NoEff.NConst c)
  | ExEff.Tuple vs ->
      let elab_ty_list = List.map (elab_expression state) vs in
      ( ExEffTypes.Tuple (List.map fst elab_ty_list),
        NoEff.NTuple (List.map snd elab_ty_list) )
  | ExEff.Lambda (p, t, c) ->
      let _, elab1 = elab_ty state t in
      let state' = extend_pattern_type state p t in
      let type2, elab2 = elab_computation state' c in
      (ExEffTypes.Arrow (t, type2), NoEff.NFun (elab_pattern p, elab1, elab2))
  | ExEff.Effect (e, (t1, t2)) ->
      let _, elab1 = elab_ty state t1 in
      let _, elab2 = elab_ty state t2 in
      ( ExEffTypes.Arrow
          (t1, (t2, ExEffTypes.closed_dirt (EffectSet.singleton e))),
        NoEff.NEffect (e, (elab1, elab2)) )
  | ExEff.Handler h ->
      let p, t, c = h.value_clause in
      let _, elabt = elab_ty state t in
      let state' = extend_pattern_type state p t in
      let typec, elabc = elab_computation state' c in

      if Assoc.length h.effect_clauses = 0 (* Handler - Case 1 *) then
        ( ExEffTypes.Handler ((t, ExEffTypes.empty_dirt), typec),
          NoEff.NFun (elab_pattern p, elabt, elabc) )
      else
        let ty, dirt = typec in
        if ExEffTypes.is_empty_dirt dirt (* Handler - Case 2 *) then
          let subst_cont_effect ((eff, (ty1, ty2)), (p1, p2, comp)) =
            let _, elab1 = elab_ty state ty1 in
            let _, elab2 = elab_ty state ty2 in
            let state' = extend_pattern_type state p1 ty1 in
            let state'' =
              extend_pattern_type state' p2
                (ExEffTypes.Arrow (ty2, (ty, ExEffTypes.empty_dirt)))
            in
            let _, elabcomp = elab_computation state'' comp in
            match p2 with
            | PVar x ->
                ( (eff, (elab1, elab2)),
                  ( elab_pattern p1,
                    elab_pattern p2,
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
                return_clause = (elab_pattern p, elabt, NoEff.NReturn elabc);
                effect_clauses =
                  Assoc.map_of_list subst_cont_effect
                    (Assoc.to_list h.effect_clauses);
              } ) (* Handler - Case 3 *)
        else
          let elab_effect_clause ((eff, (ty1, ty2)), (p1, p2, comp)) =
            let _, elab1 = elab_ty state ty1 in
            let _, elab2 = elab_ty state ty2 in
            let state' = extend_pattern_type state p1 ty1 in
            let state'' =
              extend_pattern_type state' p2
                (ExEffTypes.Arrow (ty2, (ty, ExEffTypes.empty_dirt)))
            in
            let _, elabcomp = elab_computation state'' comp in
            ((eff, (elab1, elab2)), (elab_pattern p1, elab_pattern p2, elabcomp))
          in
          let effectset = get_effectset (Assoc.to_list h.effect_clauses) in
          ( ExEffTypes.Handler ((t, ExEffTypes.closed_dirt effectset), typec),
            NoEff.NHandler
              {
                return_clause = (elab_pattern p, elabt, elabc);
                effect_clauses =
                  Assoc.map_of_list elab_effect_clause
                    (Assoc.to_list h.effect_clauses);
              } )
  | ExEff.CastExp (value, coer) ->
      let ty1, elab1 = elab_expression state value in
      let (ty2, r), elab2 = elab_ty_coercion state coer in
      if Type.types_are_equal ty1 ty2 then (r, NoEff.NCast (elab1, elab2))
      else
        Error.typing ~loc:Location.unknown "Ill-typed expression cast %t <= %t"
          (Type.print_ty ty1) (Type.print_ty ty2)
  | ExEff.LambdaTyCoerVar (par, (ty1, ty2), exp) ->
      let _, elab1 = elab_ty state ty1 in
      let _, elab2 = elab_ty state ty2 in
      let state' = extend_ty_coer_types state par (ty1, ty2) in
      let typev, elabv = elab_expression state' exp in
      ( ExEffTypes.QualTy ((ty1, ty2), typev),
        NoEff.NBigLambdaCoer (par, (elab1, elab2), elabv) )
  | ExEff.LambdaDirtCoerVar (par, (dirt1, dirt2), value) ->
      let state' = extend_dirt_coer_types state par (dirt1, dirt2) in
      let typev, elabv = elab_expression state' value in
      (ExEffTypes.QualDirt ((dirt1, dirt2), typev), elabv)
  | ExEff.ApplyTyCoercion (value, coer) -> (
      let (ty1, ty2), elabc = elab_ty_coercion state coer in
      let ty, elabv = elab_expression state value in
      match ty with
      | ExEffTypes.QualTy ((ty1', ty2'), t) ->
          if ty1 = ty1' && ty2 = ty2' then (t, NoEff.NApplyCoer (elabv, elabc))
          else typefail "Ill-typed coercion application"
      | _ -> typefail "Ill-typed coercion application")
  | ExEff.ApplyDirtCoercion (value, coer) -> (
      let ty, elabv = elab_expression state value in
      let dirt1, dirt2 = elab_dirt_coercion state coer in
      match ty with
      | ExEffTypes.QualDirt ((dirt1', dirt2'), t) ->
          if dirt1' = dirt1 && dirt2' = dirt2 then (t, elabv)
          else typefail "Ill-typed coercion application"
      | _ -> failwith "Ill-typed coercion application")
  | ExEff.Variant (lbl, exp) ->
      let ty_in, ty_out = Type.constructor_signature state.tctx_st lbl in
      let ty_e, elab_e = elab_expression state exp in
      assert (Type.types_are_equal ty_e ty_in);
      (ty_out, NoEff.NVariant (lbl, Some elab_e))
  | ExEff.Record ass -> failwith "records not supported yet"

and elab_abstraction state (p, t, c) =
  let _type1, ntype1 = elab_ty state t in
  let state' = extend_pattern_type state p t in
  let type2, elab2 = elab_computation state' c in
  ((t, type2), (elab_pattern p, ntype1, elab2))

and elab_computation state cmp =
  let drty, trm = elab_computation' state cmp in
  (drty, trm)

and elab_computation' state c =
  match c with
  | ExEff.Value value ->
      let t, elab = elab_expression state value in
      ((t, ExEffTypes.empty_dirt), elab)
  | ExEff.LetVal (value, abs) ->
      let tyv, elabv = elab_expression state value in
      let (_, tyc), elababs = elab_abstraction state abs in
      (tyc, NoEff.NLet (elabv, elababs))
  | ExEff.LetRec (abs_list, comp) ->
      let rec extend_state state ls =
        match ls with
        | [] -> state
        | (var, ty2, (p, ty1, comp)) :: rest ->
            let state' =
              extend_var_types state var (ExEffTypes.Arrow (ty1, ty2))
            in
            let state'' = extend_pattern_type state' p ty1 in
            extend_state state'' rest
      in
      let elab_letrec_abs (var, ty2, (p, ty1, compt)) =
        let _, t1 = elab_ty state ty1 in
        let _, t2 = elab_dirty state ty2 in
        let _, elabc = elab_computation (extend_state state abs_list) compt in
        (var, t2, (elab_pattern p, t1, elabc))
      in
      let tycomp, elabcomp =
        elab_computation (extend_state state abs_list) comp
      in
      (tycomp, NoEff.NLetRec (List.map elab_letrec_abs abs_list, elabcomp))
  | ExEff.Match (value, ty, abs_lst) -> (
      let tyv, elabv = elab_expression state value in
      let tyskel, tyelab = elab_dirty state ty in
      match abs_lst with
      | [] -> (ty, NoEff.NMatch (elabv, tyelab, [], Location.unknown))
      | abs :: _ ->
          let (_, tyc), _ = elab_abstraction state abs in
          ( tyc,
            NoEff.NMatch
              ( elabv,
                tyelab,
                List.map (fun abs -> snd @@ elab_abstraction state abs) abs_lst,
                Location.unknown ) ))
  | ExEff.Apply (v1, v2) -> (
      let ty1, elab1 = elab_expression state v1 in
      match ty1 with
      | ExEffTypes.Arrow (t1, t2) ->
          let ty2, elab2 = elab_expression state v2 in
          if ty2 = t1 then (t2, NoEff.NApplyTerm (elab1, elab2))
          else failwith "Improper argument type"
      | _ -> failwith "Improper function type")
  | ExEff.Handle (value, comp) -> (
      let (ctype, cdirt), elabc = elab_computation state comp in
      let vtype, velab = elab_expression state value in
      match vtype with
      | ExEffTypes.Handler ((vty1, vdirt1), (vty2, vdirt2)) when ctype = vty1 ->
          if Type.is_empty_dirt cdirt (* Handle - Case 1 *) then
            ((vty2, vdirt2), NoEff.NApplyTerm (velab, elabc))
          else if Type.is_empty_dirt vdirt2 (* Handle - Case 2 *) then
            let _, telab = elab_ty state vty2 in
            ( (vty2, vdirt2),
              NoEff.NCast
                ( NoEff.NHandle (elabc, velab),
                  NoEff.NCoerUnsafe (NoEff.NCoerRefl telab) ) )
            (* Handle - Case 3 *)
          else ((vty2, vdirt2), NoEff.NHandle (elabc, velab))
      | _ -> failwith "Ill-typed handler")
  | ExEff.Call ((eff, (ty1, ty2)), value, (p, ty, comp)) ->
      let _, t1 = elab_ty state ty1 in
      let _, t2 = elab_ty state ty2 in
      let _, tt = elab_ty state ty in
      let vty, velab = elab_expression state value in
      if vty = ty1 then
        let state' = extend_pattern_type state p ty in
        let cty, celab = elab_computation state' comp in
        (cty, NoEff.NCall ((eff, (t1, t2)), velab, (elab_pattern p, tt, celab)))
      else failwith "Ill-typed call"
  | ExEff.Op ((eff, (ty1, ty2)), value) ->
      let _, t1 = elab_ty state ty1 in
      let _, t2 = elab_ty state ty2 in
      let vty, velab = elab_expression state value in
      if vty = ty1 then
        ((ty2, ExEffTypes.empty_dirt), NoEff.NOp ((eff, (t1, t2)), velab))
      else typefail "Ill-typed operation"
  | ExEff.Bind (c1, abs) ->
      let (ty1, dirt1), elab1 = elab_computation state c1
      and (ty1', (ty2, dirt2)), elababs = elab_abstraction state abs in
      assert (ty1 = ty1');
      if
        ExEffTypes.is_empty_dirt dirt1 && ExEffTypes.is_empty_dirt dirt2
        (* Bind - Case 1 *)
      then ((ty2, dirt2), NoEff.NLet (elab1, elababs)) (* Bind - Case 2 *)
      else ((ty2, dirt2), NoEff.NBind (elab1, elababs))
  | ExEff.CastComp (comp, coer) ->
      let (t1, t2), elabc = elab_dirty_coercion state coer in
      let cty, coelab = elab_computation state comp in
      if Type.types_are_equal (fst cty) (fst t1) then
        (t2, NoEff.NCast (coelab, elabc))
      else
        Error.typing ~loc:Location.unknown "Ill-typed computation cast %t <= %t"
          (Type.print_ty (fst cty))
          (Type.print_ty (fst t1))

let rec elab_source_ty = function
  | Language.Type.Apply (name, ts) ->
      NoEff.NTyApply (name, List.map elab_source_ty ts)
  | TyParam p -> NoEff.NTyParam p
  | Basic s -> NoEff.NTyBasic s
  | Tuple tys -> NoEff.NTyTuple (List.map elab_source_ty tys)
  | Arrow (t1, t2) -> NoEff.NTyArrow (elab_source_ty t1, elab_source_ty t2)
  | Handler h ->
      NoEff.NTyHandler (elab_source_ty h.value, elab_source_ty h.finally)

let elab_tydef = function
  | Language.Type.Record assoc ->
      NoEff.TyDefRecord (Assoc.map elab_source_ty assoc)
  | Sum assoc ->
      let converter = function
        | None -> None
        | Some ty -> Some (elab_source_ty ty)
      in
      NoEff.TyDefSum (Assoc.map converter assoc)
  | Inline ty -> NoEff.TyDefInline (elab_source_ty ty)
