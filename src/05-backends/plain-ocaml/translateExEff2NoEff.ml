open Utils
open SyntaxNoEff
open Language.Term
open Language
open Type
module NoEff = SyntaxNoEff
module ExEffTypes = Type
module ExEff = Term
module Sub = Language.Substitution

type optimization_config = { purity_aware_translation : bool }
type state = { config : optimization_config }

let initial_state optimization_config = { config = optimization_config }

let rec elab_ty (ty : ExEffTypes.ty) =
  match ty.term with
  | ExEffTypes.TyParam x -> NoEff.NTyParam x
  | ExEffTypes.Apply { ty_name; ty_args } ->
      NoEff.NTyApply
        ( ty_name,
          List.map elab_ty (ty_args |> TyParam.Map.values |> List.map fst) )
  | ExEffTypes.Arrow (t, dirty) ->
      let elab1 = elab_ty t in
      let elab2 = elab_dirty dirty in
      NoEff.NTyArrow (elab1, elab2)
  | ExEffTypes.Handler ((type1, dirt1), (type2, dirt2)) ->
      let elab1 = elab_ty type1 in
      if Dirt.is_empty dirt1 (* Handler type - Case 1: empty input dirt *) then
        let elab2 = elab_dirty (type2, dirt2) in
        NoEff.NTyArrow (elab1, elab2)
        (* Handler type - Case 2: non-empty input dirt. The output keeps its
           dirt, so a closed handler may return a pure value. *)
      else
        let elab2 = elab_dirty (type2, dirt2) in
        NoEff.NTyHandler (elab1, elab2)
  | ExEffTypes.Tuple tys ->
      let ty_elab_list = List.map elab_ty tys in
      NoEff.NTyTuple ty_elab_list
  | ExEffTypes.TyBasic ty -> NoEff.NTyBasic ty

and elab_dirty (ty, dirt) =
  let elab = elab_ty ty in
  if Dirt.is_empty dirt then elab else NoEff.NTyComp elab

let has_empty_dirt ((_ty, dirt) : ExEffTypes.dirty) = Dirt.is_empty dirt

let rec get_effectset_temp set effects =
  match effects with
  | ((eff, _), _abs) :: es -> get_effectset_temp (Effect.Set.add eff set) es
  | [] -> set

let get_effectset effects = get_effectset_temp Effect.Set.empty effects

let elab_effect eff : n_effect =
  let ty1, ty2 = eff.ty in
  (eff.term, (elab_ty ty1, elab_ty ty2))

let rec elab_ty_coercion state coer =
  match coer.term with
  | TyCoercion.ReflTy -> NoEff.NCoerRefl
  | TyCoercion.ArrowCoercion (tycoer, dirtycoer) ->
      let tyelab = elab_ty_coercion state tycoer in
      let dirtyelab = elab_dirty_coercion state dirtycoer in
      NoEff.NCoerArrow (tyelab, dirtyelab)
  | TyCoercion.HandlerCoercion (coerA, coerB) -> (
      (* The paper's four cases, split on the input dirts of the two handler
         types: [coerA] goes from the input of the target type, [drt_in'], to
         the input of the source type, [drt_in]. *)
      let (_, drt_in'), (_, drt_in) = coerA.ty in
      let elabA = elab_dirty_coercion state coerA
      and elabB = elab_dirty_coercion state coerB in
      match (Dirt.is_empty drt_in, Dirt.is_empty drt_in') with
      | true, true -> NoEff.NCoerArrow (elabA, elabB)
      | false, true ->
          let tycoerA, _ = coerA.term in
          NoEff.NCoerHandToFun (elab_ty_coercion state tycoerA, elabB)
      | true, false ->
          (* funToHand. [drt_in'] is in [drt_in], so this needs a dirt
             parameter in [drt_in'], which counts as non-empty. *)
          let tycoerA, _ = coerA.term in
          NoEff.NCoerFunToHand (elab_ty_coercion state tycoerA, elabB)
      | false, false -> NoEff.NCoerHandler (elabA, elabB))
  | TyCoercion.TyCoercionVar par -> NoEff.NCoerVar par
  | TyCoercion.ApplyCoercion { ty_name; tcoers } ->
      NoEff.NCoerApply
        ( ty_name,
          tcoers |> TyParam.Map.values |> List.map fst
          |> List.map (elab_ty_coercion state) )
  | TyCoercion.TupleCoercion lst ->
      let elabs = List.map (elab_ty_coercion state) lst in
      NoEff.NCoerTuple elabs

and elab_dirty_coercion state { term = tcoer, dcoer; _ } =
  let tyelab = elab_ty_coercion state tcoer in
  let d1, d2 = dcoer.ty in
  if Dirt.is_empty d1 && Dirt.is_empty d2 then tyelab
  else if Dirt.is_empty d1 then NoEff.NCoerReturn tyelab
  else if not (Dirt.is_empty d2) then NoEff.NCoerComp tyelab
  else
    (* [d1] is in [d2], so this needs a dirt parameter in [d1], which counts
       as non-empty. *)
    NoEff.NCoerUnsafe tyelab

let rec is_refl_coercion = function
  | NoEff.NCoerRefl -> true
  | NoEff.NCoerArrow (c1, c2) | NoEff.NCoerHandler (c1, c2) ->
      is_refl_coercion c1 && is_refl_coercion c2
  | NoEff.NCoerTuple cs | NoEff.NCoerApply (_, cs) ->
      List.for_all is_refl_coercion cs
  | _ -> false

(* The coercions of a named type's arguments, in the order of [elab_ty]. A
   contravariant argument needs the coercion in the other direction, and an
   invariant one only admits a reflexive coercion. *)
let apply_instantiation_coercion ~same ~other ty_name ty_args =
  let coer_arg (ty, variance) =
    match variance with
    | Covariant -> same ty
    | Contravariant -> other ty
    | Invariant ->
        let coer = same ty in
        if is_refl_coercion coer then coer
        else
          failwith
            "A dirt in an invariant type argument is instantiated to the empty \
             dirt"
  in
  NoEff.NCoerApply (ty_name, ty_args |> TyParam.Map.values |> List.map coer_arg)

let rec value_coercion_from_impure_dirt empty_dirt_params ty =
  match ty.term with
  | ExEffTypes.TyParam _ -> NoEff.NCoerRefl
  | ExEffTypes.Apply { ty_name; ty_args } ->
      apply_instantiation_coercion
        ~same:(value_coercion_from_impure_dirt empty_dirt_params)
        ~other:(value_coercion_to_impure_dirt empty_dirt_params)
        ty_name ty_args
  | ExEffTypes.Arrow (ty1, drty2) ->
      NoEff.NCoerArrow
        ( value_coercion_to_impure_dirt empty_dirt_params ty1,
          computation_coercion_from_impure_dirt empty_dirt_params drty2 )
  | ExEffTypes.Tuple tys ->
      NoEff.NCoerTuple
        (List.map (value_coercion_from_impure_dirt empty_dirt_params) tys)
  | ExEffTypes.Handler ((ty1, drt1), (ty2, drt2)) -> (
      if Dirt.is_empty drt1 then
        NoEff.NCoerArrow
          ( value_coercion_to_impure_dirt empty_dirt_params ty1,
            computation_coercion_from_impure_dirt empty_dirt_params (ty2, drt2)
          )
      else
        match drt1.row with
        | Dirt.Row.Param d ->
            if
              Dirt.Param.Set.mem d empty_dirt_params
              && Effect.Set.is_empty drt1.effect_set
            then
              let coer1 = value_coercion_to_impure_dirt empty_dirt_params ty1 in
              let coer2 =
                value_coercion_from_impure_dirt empty_dirt_params ty2
              in
              if
                Dirt.is_empty
                  (Substitution.apply_substitutions_to_dirt
                     (Substitution.empty_dirt_substitution empty_dirt_params)
                     drt2)
              then NoEff.NCoerHandToFun (coer1, NoEff.NCoerUnsafe coer2)
              else NoEff.NCoerHandToFun (coer1, NoEff.NCoerComp coer2)
            else
              NoEff.NCoerHandler
                ( computation_coercion_to_impure_dirt empty_dirt_params
                    (ty1, drt1),
                  computation_coercion_from_impure_dirt empty_dirt_params
                    (ty2, drt2) )
        | Dirt.Row.Empty ->
            NoEff.NCoerHandler
              ( computation_coercion_to_impure_dirt empty_dirt_params (ty1, drt1),
                computation_coercion_from_impure_dirt empty_dirt_params
                  (ty2, drt2) ))
  | ExEffTypes.TyBasic _ -> NoEff.NCoerRefl

and computation_coercion_from_impure_dirt empty_dirt_params (ty1, drt) =
  let noeff_coer = value_coercion_from_impure_dirt empty_dirt_params ty1 in
  match drt with
  | _ when Dirt.is_empty drt -> noeff_coer
  | { effect_set; row = Dirt.Row.Param p }
    when Dirt.Param.Set.mem p empty_dirt_params
         && Effect.Set.is_empty effect_set ->
      NoEff.NCoerUnsafe noeff_coer
  | _ ->
      assert (
        not
          (Dirt.is_empty
             (Substitution.apply_substitutions_to_dirt
                (Substitution.empty_dirt_substitution empty_dirt_params)
                drt)));
      NoEff.NCoerComp noeff_coer

and value_coercion_to_impure_dirt empty_dirt_params ty =
  match ty.term with
  | ExEffTypes.TyParam _ -> NoEff.NCoerRefl
  | ExEffTypes.Apply { ty_name; ty_args } ->
      apply_instantiation_coercion
        ~same:(value_coercion_to_impure_dirt empty_dirt_params)
        ~other:(value_coercion_from_impure_dirt empty_dirt_params)
        ty_name ty_args
  | ExEffTypes.Arrow (ty1, drty2) ->
      NoEff.NCoerArrow
        ( value_coercion_from_impure_dirt empty_dirt_params ty1,
          computation_coercion_to_impure_dirt empty_dirt_params drty2 )
  | ExEffTypes.Tuple tys ->
      NoEff.NCoerTuple
        (List.map (value_coercion_to_impure_dirt empty_dirt_params) tys)
  | ExEffTypes.Handler ((ty1, drt1), (ty2, drt2)) -> (
      if Dirt.is_empty drt1 then
        NoEff.NCoerArrow
          ( value_coercion_from_impure_dirt empty_dirt_params ty1,
            computation_coercion_to_impure_dirt empty_dirt_params (ty2, drt2) )
      else
        match drt1.row with
        | Dirt.Row.Param d ->
            if
              Dirt.Param.Set.mem d empty_dirt_params
              && Effect.Set.is_empty drt1.effect_set
            then
              let coer1 =
                value_coercion_from_impure_dirt empty_dirt_params ty1
              in
              let coer2 = value_coercion_to_impure_dirt empty_dirt_params ty2 in
              if
                Dirt.is_empty
                  (Substitution.apply_substitutions_to_dirt
                     (Substitution.empty_dirt_substitution empty_dirt_params)
                     drt2)
              then NoEff.NCoerFunToHand (coer1, NoEff.NCoerReturn coer2)
              else NoEff.NCoerFunToHand (coer1, NoEff.NCoerComp coer2)
            else
              NoEff.NCoerHandler
                ( computation_coercion_from_impure_dirt empty_dirt_params
                    (ty1, drt1),
                  computation_coercion_to_impure_dirt empty_dirt_params
                    (ty2, drt2) )
        | Dirt.Row.Empty ->
            NoEff.NCoerHandler
              ( computation_coercion_from_impure_dirt empty_dirt_params
                  (ty1, drt1),
                computation_coercion_to_impure_dirt empty_dirt_params (ty2, drt2)
              ))
  | ExEffTypes.TyBasic _ -> NoEff.NCoerRefl

and computation_coercion_to_impure_dirt empty_dirt_params (ty1, drt) =
  let noeff_coer = value_coercion_to_impure_dirt empty_dirt_params ty1 in
  match drt with
  | _ when Dirt.is_empty drt -> noeff_coer
  | { effect_set; row = Dirt.Row.Param p }
    when Dirt.Param.Set.mem p empty_dirt_params
         && Effect.Set.is_empty effect_set ->
      NoEff.NCoerReturn noeff_coer
  | _ ->
      assert (
        not
          (Dirt.is_empty
             (Substitution.apply_substitutions_to_dirt
                (Substitution.empty_dirt_substitution empty_dirt_params)
                drt)));
      NoEff.NCoerComp noeff_coer

let rec elab_pattern state p =
  match p.term with
  | PVar x -> PNVar x
  | PAs (p, x) -> PNAs (elab_pattern state p, x)
  | PTuple ps -> PNTuple (List.map (elab_pattern state) ps)
  | PConst c -> PNConst c
  | PRecord recs ->
      NoEff.PNRecord (Type.Field.Map.map (elab_pattern state) recs)
  | PVariant (l, None) -> NoEff.PNVariant (l, None)
  | PVariant (l, Some p) -> NoEff.PNVariant (l, Some (elab_pattern state p))
  | PNonbinding -> PNNonbinding

let rec elab_expression (state : state) expr = elab_expression' state expr

and elab_expression' state expr =
  match expr.term with
  | ExEff.Var x ->
      let empty_dirt_params =
        x.instantiation.dirt_var_to_dirt_subs |> Dirt.Param.Map.bindings
        |> List.filter (fun (_, drt) -> Dirt.is_empty drt)
        |> List.fold_left
             (fun empty_dirt_params (param, _) ->
               Dirt.Param.Set.add param empty_dirt_params)
             Dirt.Param.Set.empty
      in
      let coercions =
        x.instantiation.type_param_to_type_coercions
        |> Type.TyCoercionParam.Map.bindings
        |> List.map (fun (_, coer) -> (elab_ty_coercion state) coer)
      in
      NoEff.NCast
        ( NoEff.NVar { variable = x.variable; coercions },
          value_coercion_from_impure_dirt empty_dirt_params x.original_ty )
  | ExEff.Const c -> NoEff.NConst c
  | ExEff.Tuple vs -> NoEff.NTuple (List.map (elab_expression state) vs)
  | ExEff.Lambda abs -> NoEff.NFun (elab_abstraction_with_param_ty state abs)
  | ExEff.Handler h -> elab_handler state h None
  | ExEff.HandlerWithFinally h ->
      elab_handler state h.handler_clauses
        (Some (elab_abstraction_with_param_ty state h.finally_clause))
  | ExEff.CastExp (value, coer) ->
      let elab1 = elab_expression state value in
      let elab2 = elab_ty_coercion state coer in
      NoEff.NCast (elab1, elab2)
  | ExEff.Variant (lbl, None) -> NoEff.NVariant (lbl, None)
  | ExEff.Variant (lbl, Some expr) ->
      let elab_e = elab_expression state expr in
      NoEff.NVariant (lbl, Some elab_e)
  | ExEff.Record _ass -> failwith __LOC__

(* The paper's three cases, split on the input dirt and on the dirt that the
   base [fwd] forwards. [elabfc] is the finally clause, which the paper does
   not have; [None] stands for the identity. *)
and elab_handler state h elabfc =
  let elabvc = elab_abstraction_with_param_ty state h.term.value_clause in
  let (_, drt_in), _ = h.ty in
  let _, (ty_mid, drt_mid) = h.term.value_clause.ty in
  (* Apply the finally clause to [t], the result of the clauses. *)
  let apply_finally t (p_fc, _, c_fc) =
    if Dirt.is_empty drt_mid then NoEff.NLet (t, (p_fc, c_fc))
    else NoEff.NBind (t, (p_fc, c_fc))
  in
  let elab_effect_clause (eff, { term = p1, p2, comp; _ }) =
    ( elab_effect eff,
      (elab_pattern state p1, elab_pattern state p2, elab_computation state comp)
    )
  in
  let effect_clauses =
    Assoc.map_of_list elab_effect_clause
      (Assoc.to_list h.term.effect_clauses.effect_part)
  in
  if Dirt.is_empty drt_in then
    (* Handler - Case 1: no operations, so a function *)
    match elabfc with
    | None -> NoEff.NFun elabvc
    | Some fc ->
        let p_vc, ty_vc, c_vc = elabvc in
        NoEff.NFun (p_vc, ty_vc, apply_finally c_vc fc)
  else if Dirt.is_empty (ExEff.forwarded_dirt h) then
    (* Handler - Case 2: closed. The clauses return [elab_dirty] of the
       output type, which need not be a computation. *)
    let x = Variable.fresh "$finally" in
    let x_var = NoEff.NVar { variable = x; coercions = [] } in
    let ty_clauses = elab_dirty (ty_mid, drt_mid) in
    let finally_clause =
      match elabfc with
      | None -> (NoEff.PNVar x, ty_clauses, x_var)
      | Some fc -> (NoEff.PNVar x, ty_clauses, apply_finally x_var fc)
    in
    NoEff.NHandler
      {
        forwarding = false;
        return_clause = elabvc;
        effect_clauses;
        finally_clause;
      }
  else (
    (* Handler - Case 3: forwarding. The forwarded dirt is in the output
       dirt, so the clauses return computations. *)
    assert (not (Dirt.is_empty drt_mid));
    let finally_clause =
      match elabfc with
      | None ->
          let x = Variable.fresh "$finally" in
          ( NoEff.PNVar x,
            elab_ty ty_mid,
            NoEff.NReturn (NoEff.NVar { variable = x; coercions = [] }) )
      | Some fc -> fc
    in
    NoEff.NHandler
      {
        forwarding = true;
        return_clause = elabvc;
        effect_clauses;
        finally_clause;
      })

and elab_abstraction state { term = p, c; _ } =
  let elab2 = elab_computation state c in
  (elab_pattern state p, elab2)

and elab_abstraction_with_param_ty state { term = p, c; ty = param_ty, _ } =
  let elab2 = elab_computation state c in
  (elab_pattern state p, elab_ty param_ty, elab2)

and elab_computation state { term; ty = _ty, drt } =
  elab_computation' state term (Dirt.is_empty drt)

and elab_computation' state c _is_empty =
  match c with
  | ExEff.Value value ->
      let elab = elab_expression state value in
      elab
  | ExEff.LetVal (value, abs) ->
      let elabv = elab_expression state value in
      let elababs = elab_abstraction state abs in
      NoEff.NLet (elabv, elababs)
  | ExEff.LetRec (abs_list, comp) ->
      let elabcomp = elab_computation state comp in
      NoEff.NLetRec (elab_rec_definitions state abs_list, elabcomp)
  | ExEff.Match (value, abs_lst) -> (
      let elabv = elab_expression state value in
      match abs_lst with
      | [] -> NoEff.NMatch (elabv, [])
      | _ :: _ ->
          NoEff.NMatch
            (elabv, List.map (fun abs -> elab_abstraction state abs) abs_lst))
  | ExEff.Apply (v1, v2) ->
      let telab1 = elab_expression state v1 in
      let elab2 = elab_expression state v2 in
      NoEff.NApplyTerm (telab1, elab2)
  | ExEff.Handle (value, comp) -> (
      let ctype, cdirt = comp.ty
      and elabc = elab_computation state comp
      and vtype = value.ty
      and velab = elab_expression state value in
      match vtype.term with
      | ExEffTypes.Handler ((vty1, _vdirt1), _) when ctype = vty1 ->
          if Dirt.is_empty cdirt (* Handle - Case 1 *) then
            NoEff.NApplyTerm (velab, elabc)
            (* Handle - Case 2: closed or forwarding alike *)
          else NoEff.NHandle (elabc, velab)
      | _ -> assert false)
  | ExEff.Call (eff, value, abs) ->
      let eff' = elab_effect eff in
      let velab = elab_expression state value in
      let aelab = elab_abstraction_with_param_ty state abs in
      NoEff.NCall (eff', velab, aelab)
  | ExEff.Bind (c1, abs) ->
      let _ty1, dirt1 = c1.ty
      and elab1 = elab_computation state c1
      and _ty1', (_ty2, dirt2) = abs.ty
      and elababs = elab_abstraction state abs in
      if Dirt.is_empty dirt1 && Dirt.is_empty dirt2 (* Bind - Case 1 *) then
        NoEff.NLet (elab1, elababs) (* Bind - Case 2 *)
      else NoEff.NBind (elab1, elababs)
  | ExEff.CastComp (comp, coer) ->
      let elabc = elab_dirty_coercion state coer in
      let coelab = elab_computation state comp in
      NoEff.NCast (coelab, elabc)
  | ExEff.Check _ -> failwith __LOC__

and elab_rec_definitions state defs =
  Assoc.kmap (fun (x, abs) -> (x, elab_abstraction state abs)) defs

let elab_tydef = function
  | Type.Record assoc -> NoEff.TyDefRecord (Type.Field.Map.map elab_ty assoc)
  | Sum assoc ->
      let converter = function None -> None | Some ty -> Some (elab_ty ty) in
      NoEff.TyDefSum (Type.Field.Map.map converter assoc)
  | Inline ty -> NoEff.TyDefInline (elab_ty ty)

(* The coercion parameters of a definition. A use passes its coercions in
   the order of [Type.TyCoercionParam.Map.bindings] (see [ExEff.Var] in
   [elab_expression']), so the parameters are sorted in the same order. *)
let elab_constraints cnstrs =
  Constraints.TyConstraints.fold
    (fun _ _ _ w lst -> w :: lst)
    cnstrs.Constraints.ty_constraints []
  |> List.sort Type.TyCoercionParam.compare

let elab_top_rec_definitions state defs =
  Assoc.kmap
    (fun (x, (_params, cnstrs, abs)) ->
      (x, (elab_constraints cnstrs, elab_abstraction state abs)))
    defs
