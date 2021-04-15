open Utils
open SyntaxNoEff
open Type
open Term
module NoEff = SyntaxNoEff
module ExEffTypes = Type
module ExEff = Term
module EffectSet = Set.Make (CoreTypes.Effect)
module Sub = Substitution

let typefail str =
  let message = "ExEff-to-NoEff: " ^ str in
  failwith message

let rec elab_ty (ty : ExEffTypes.ty) =
  match ty with
  | ExEffTypes.TyParam (x, _skel) -> NoEff.NTyParam x
  | ExEffTypes.Apply (name, lst) -> NoEff.NTyApply (name, List.map elab_ty lst)
  | ExEffTypes.Arrow (t, dirty) ->
      let elab1 = elab_ty t in
      let elab2 = elab_dirty dirty in
      NoEff.NTyArrow (elab1, elab2)
  | ExEffTypes.Handler ((type1, dirt1), (type2, dirt2)) ->
      let elab1 = elab_ty type1 in
      if
        ExEffTypes.is_empty_dirt dirt1
        (* Handler type - Case 1: empty input dirt *)
      then
        let elab2 = elab_dirty (type2, dirt2) in
        NoEff.NTyArrow (elab1, elab2)
        (* Handler type - Case 2: non-empty input dirt *)
      else
        let elab2 = elab_ty type2 in
        NoEff.NTyHandler (elab1, elab2)
  | ExEffTypes.Tuple tys ->
      let ty_elab_list = List.map elab_ty tys in
      NoEff.NTyTuple ty_elab_list
  | ExEffTypes.TyBasic ty -> NoEff.NTyBasic ty

and elab_dirty (ty, dirt) =
  let elab = elab_ty ty in
  if ExEffTypes.is_empty_dirt dirt then elab else NoEff.NTyComp elab

let has_empty_dirt ((_ty, dirt) : ExEffTypes.dirty) = is_empty_dirt dirt

let rec get_effectset_temp set effects =
  match effects with
  | ((eff, _), _abs) :: es -> get_effectset_temp (EffectSet.add eff set) es
  | [] -> set

let get_effectset effects = get_effectset_temp EffectSet.empty effects

let rec elab_ty_coercion coer =
  match coer.term with
  | Constraint.ReflTy -> NoEff.NCoerRefl
  | Constraint.ArrowCoercion (tycoer, dirtycoer) ->
      let tyelab = elab_ty_coercion tycoer in
      let dirtyelab = elab_dirty_coercion dirtycoer in
      NoEff.NCoerArrow (tyelab, dirtyelab)
  | Constraint.HandlerCoercion (coerA, coerB) -> (
      let coerA2, coerA1 = coerA.ty
      and elabA = elab_dirty_coercion coerA
      and coerB1, _coerB2 = coerB.ty
      and elabB = elab_dirty_coercion coerB in
      if
        has_empty_dirt coerA1 && has_empty_dirt coerA2
        (* Handler coercion - Case 1 *)
      then NoEff.NCoerArrow (elabA, elabB)
      else
        match coerB.term with
        | tycoer, _dirtcoer -> (
            let elab2 = elab_ty_coercion tycoer in
            if
              (not (has_empty_dirt coerA2)) && not (has_empty_dirt coerA2)
              (* Handler coercion - Case 2 *)
            then NoEff.NCoerHandler (elabA, NoEff.NCoerComp elab2)
            else
              match coerA.term with
              | tycoerA, _dirtcoerA ->
                  let elab1 = elab_ty_coercion tycoerA in
                  if
                    has_empty_dirt coerB1
                    && (not (has_empty_dirt coerA1))
                    && has_empty_dirt coerA2
                    (* Handler coercion - Case 3 *)
                  then NoEff.NCoerHandToFun (elab1, NoEff.NCoerUnsafe elab2)
                  else if
                    has_empty_dirt coerA2
                    && (not (has_empty_dirt coerA1))
                    && not (has_empty_dirt coerB1)
                    (* Handler coercion - Case 4 *)
                  then NoEff.NCoerHandToFun (elab1, elab2)
                  else failwith "Ill-typed handler coercion"))
  | Constraint.TyCoercionVar par -> NoEff.NCoerVar par
  | Constraint.ApplyCoercion (name, coer_list) ->
      NoEff.NCoerApply (name, List.map elab_ty_coercion coer_list)
  | Constraint.TupleCoercion lst ->
      let elabs = List.map elab_ty_coercion lst in
      NoEff.NCoerTuple elabs

and elab_dirty_coercion { term = tcoer, dcoer; _ } =
  let tyelab = elab_ty_coercion tcoer in
  let d1, d2 = dcoer.ty in
  if is_empty_dirt d1 && is_empty_dirt d2 then tyelab
  else if is_empty_dirt d1 then NoEff.NCoerReturn tyelab
  else if not (is_empty_dirt d2) then NoEff.NCoerComp tyelab
  else failwith "Ill-typed bang coercion"

let rec elab_pattern p =
  match p.term with
  | PVar x -> PNVar x.term
  | PAs (p, x) -> PNAs (elab_pattern p, x.term)
  | PTuple ps -> PNTuple (List.map elab_pattern ps)
  | PConst c -> PNConst c
  | PRecord recs -> NoEff.PNRecord (Assoc.map elab_pattern recs)
  | PVariant (l, None) -> NoEff.PNVariant (l, None)
  | PVariant (l, Some p) -> NoEff.PNVariant (l, Some (elab_pattern p))
  | PNonbinding -> PNNonbinding

let rec elab_expression exp = elab_expression' exp.term

and elab_expression' exp =
  match exp with
  | ExEff.Var x -> NoEff.NVar x.term
  | ExEff.Const c -> NoEff.NConst c
  | ExEff.Tuple vs -> NoEff.NTuple (List.map elab_expression vs)
  | ExEff.Lambda abs -> NoEff.NFun (elab_abstraction_with_param_ty abs)
  | ExEff.Handler h ->
      let elabvc = elab_abstraction_with_param_ty h.term.value_clause in

      if
        Assoc.length h.term.effect_clauses.effect_part = 0
        (* Handler - Case 1 *)
      then NoEff.NFun elabvc
      else
        let _, (_ty, dirt) = h.term.value_clause.ty in
        if ExEffTypes.is_empty_dirt dirt (* Handler - Case 2 *) then
          let subst_cont_effect ((eff, (ty1, ty2)), { term = p1, p2, comp; _ })
              =
            let elab1 = elab_ty ty1 in
            let elab2 = elab_ty ty2 in
            let elabcomp = elab_computation comp in
            match p2.term with
            | PVar { term = x; _ } ->
                ( (eff, (elab1, elab2)),
                  ( elab_pattern p1,
                    elab_pattern p2,
                    NReturn
                      (subs_var_in_term x
                         (NCast
                            ( NVar x,
                              NoEff.NCoerArrow
                                ( NoEff.NCoerRefl,
                                  NoEff.NCoerUnsafe NoEff.NCoerRefl ) ))
                         elabcomp) ) )
            | _ -> failwith "STIEN: wrong elab handler case 2"
          in
          let p, ty, c = elabvc in
          NoEff.NHandler
            {
              return_clause = (p, ty, NoEff.NReturn c);
              effect_clauses =
                Assoc.map_of_list subst_cont_effect
                  (Assoc.to_list h.term.effect_clauses.effect_part);
            } (* Handler - Case 3 *)
        else
          let elab_effect_clause ((eff, (ty1, ty2)), { term = p1, p2, comp; _ })
              =
            let elab1 = elab_ty ty1 in
            let elab2 = elab_ty ty2 in
            let elabcomp = elab_computation comp in
            ((eff, (elab1, elab2)), (elab_pattern p1, elab_pattern p2, elabcomp))
          in
          let p, ty, c = elabvc in
          NoEff.NHandler
            {
              return_clause = (p, ty, c);
              effect_clauses =
                Assoc.map_of_list elab_effect_clause
                  (Assoc.to_list h.term.effect_clauses.effect_part);
            }
  | ExEff.CastExp (value, coer) ->
      let elab1 = elab_expression value in
      let elab2 = elab_ty_coercion coer in
      NoEff.NCast (elab1, elab2)
  | ExEff.Variant (lbl, None) -> NoEff.NVariant (lbl, None)
  | ExEff.Variant (lbl, Some exp) ->
      let elab_e = elab_expression exp in
      NoEff.NVariant (lbl, Some elab_e)
  | ExEff.Record _ass -> failwith "records not supported yet"

and elab_abstraction { term = p, c; _ } =
  let elab2 = elab_computation c in
  (elab_pattern p, elab2)

and elab_abstraction_with_param_ty { term = p, c; ty = param_ty, _ } =
  let elab2 = elab_computation c in
  (elab_pattern p, elab_ty param_ty, elab2)

and elab_computation cmp = elab_computation' cmp.term

and elab_computation' c =
  match c with
  | ExEff.Value value ->
      let elab = elab_expression value in
      elab
  | ExEff.LetVal (value, abs) ->
      let elabv = elab_expression value in
      let elababs = elab_abstraction abs in
      NoEff.NLet (elabv, elababs)
  | ExEff.LetRec (abs_list, comp) ->
      let elabcomp = elab_computation comp in
      NoEff.NLetRec (elab_rec_definitions abs_list, elabcomp)
  | ExEff.Match (value, abs_lst) -> (
      let elabv = elab_expression value in
      match abs_lst with
      | [] -> NoEff.NMatch (elabv, [])
      | _ :: _ ->
          NoEff.NMatch
            (elabv, List.map (fun abs -> elab_abstraction abs) abs_lst))
  | ExEff.Apply (v1, v2) ->
      let telab1 = elab_expression v1 in
      let elab2 = elab_expression v2 in
      NoEff.NApplyTerm (telab1, elab2)
  | ExEff.Handle (value, comp) -> (
      let ctype, cdirt = comp.ty
      and elabc = elab_computation comp
      and vtype = value.ty
      and velab = elab_expression value in
      match vtype with
      | ExEffTypes.Handler ((vty1, _vdirt1), (_vty2, vdirt2)) when ctype = vty1
        ->
          if Type.is_empty_dirt cdirt (* Handle - Case 1 *) then
            NoEff.NApplyTerm (velab, elabc)
          else if Type.is_empty_dirt vdirt2 (* Handle - Case 2 *) then
            NoEff.NCast
              (NoEff.NHandle (elabc, velab), NoEff.NCoerUnsafe NoEff.NCoerRefl)
            (* Handle - Case 3 *)
          else NoEff.NHandle (elabc, velab)
      | _ -> failwith "Ill-typed handler")
  | ExEff.Call ((eff, (ty1, ty2)), value, abs) ->
      let t1 = elab_ty ty1 in
      let t2 = elab_ty ty2 in
      let velab = elab_expression value in
      let aelab = elab_abstraction_with_param_ty abs in
      NoEff.NCall ((eff, (t1, t2)), velab, aelab)
  | ExEff.Bind (c1, abs) ->
      let _ty1, dirt1 = c1.ty
      and elab1 = elab_computation c1
      and _ty1', (_ty2, dirt2) = abs.ty
      and elababs = elab_abstraction abs in
      if
        ExEffTypes.is_empty_dirt dirt1 && ExEffTypes.is_empty_dirt dirt2
        (* Bind - Case 1 *)
      then NoEff.NLet (elab1, elababs) (* Bind - Case 2 *)
      else NoEff.NBind (elab1, elababs)
  | ExEff.CastComp (comp, coer) ->
      let elabc = elab_dirty_coercion coer in
      let coelab = elab_computation comp in
      NoEff.NCast (coelab, elabc)

and elab_rec_definitions defs =
  Assoc.kmap (fun (x, abs) -> (x.term, elab_abstraction abs)) defs

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

let elab_effect (eff, (ty1, ty2)) : n_effect = (eff, (elab_ty ty1, elab_ty ty2))
