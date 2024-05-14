open Utils
open Language
open Type

let apply_substitution new_sub resolved unresolved =
  let substitute_ty_constraint s t1 t2 w ty1 ty2 (resolved, unresolved) =
    let ty1', ty2' =
      ( Substitution.apply_substitutions_to_type new_sub ty1,
        Substitution.apply_substitutions_to_type new_sub ty2 )
    in
    if Type.equal_ty ty1 ty1' && Type.equal_ty ty2 ty2' then
      (Constraints.add_ty_constraint s t1 t2 w resolved, unresolved)
    else
      ( resolved,
        UnresolvedConstraints.add_ty_inequality (w, (ty1', ty2')) unresolved )
  and substitute_dirt_constraint d1 d2 w effs drt1 drt2 (resolved, unresolved) =
    let drt1', drt2' =
      ( Substitution.apply_substitutions_to_dirt new_sub drt1,
        Substitution.apply_substitutions_to_dirt new_sub drt2 )
    in
    if Type.equal_dirt drt1 drt1' && Type.equal_dirt drt2 drt2' then
      (Constraints.add_dirt_constraint d1 d2 w effs resolved, unresolved)
    else
      ( resolved,
        UnresolvedConstraints.add_dirt_inequality (w, (drt1', drt2')) unresolved
      )
  in
  let resolved', unresolved' =
    (Constraints.empty, UnresolvedConstraints.apply_sub new_sub unresolved)
    |> Constraints.TyConstraints.fold_expanded substitute_ty_constraint
         resolved.Constraints.ty_constraints
    |> Constraints.DirtConstraints.fold_expanded substitute_dirt_constraint
         resolved.Constraints.dirt_constraints
  in
  (resolved', unresolved')

let change_subst f unresolved =
  UnresolvedConstraints.
    { unresolved with substitution = f unresolved.substitution }

let expand_row ~loc sub row ops =
  match row with
  | _ when Effect.Set.is_empty ops -> (sub, row)
  | Dirt.Row.Param p ->
      let p' = Dirt.Param.refresh p in
      let row' = Dirt.Row.Param p' in
      let sub' =
        Substitution.add_dirt_substitution p
          { effect_set = ops; row = row' }
          sub
      in
      (sub', row')
  | Dirt.Row.Empty -> Error.typing ~loc "Cannot extend an empty row."

let skel_eq_step ~loc resolved unresolved sk1 sk2 =
  match (sk1, sk2) with
  (* ς = ς *)
  | Skeleton.Param sp1, Skeleton.Param sp2 when sp1 = sp2 ->
      (resolved, unresolved)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | Param sp1, sk2a
    when not
           (Skeleton.Param.Set.mem sp1 (free_params_skeleton sk2a).skel_params)
    ->
      apply_substitution
        (Substitution.add_skel_param_substitution_e sp1 sk2a)
        resolved unresolved
  | sk2a, Param sp1
    when not
           (Skeleton.Param.Set.mem sp1 (free_params_skeleton sk2a).skel_params)
    ->
      apply_substitution
        (Substitution.add_skel_param_substitution_e sp1 sk2a)
        resolved unresolved
      (* occurs-check failing *)
  | Param _, _ | _, Param _ ->
      let printer = Type.print_pretty Skeleton.Param.Set.empty in
      Error.typing ~loc "This expression has a forbidden cyclic type %t = %t."
        (printer sk1) (printer sk2)
      (* int = int *)
  | Basic ps1, Basic ps2 when ps1 = ps2 -> (resolved, unresolved)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | Arrow (ska, skb), Arrow (skc, skd) ->
      ( resolved,
        unresolved
        |> UnresolvedConstraints.add_skeleton_equality (ska, skc)
        |> UnresolvedConstraints.add_skeleton_equality (skb, skd) )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | Handler (ska, skb), Handler (skc, skd) ->
      ( resolved,
        unresolved
        |> UnresolvedConstraints.add_skeleton_equality (ska, skc)
        |> UnresolvedConstraints.add_skeleton_equality (skb, skd) )
  | ( Apply { ty_name = ty_name1; skel_args = sks1 },
      Apply { ty_name = ty_name2; skel_args = sks2 } )
    when ty_name1 = ty_name2
         && TyParam.Map.cardinal sks1 = TyParam.Map.cardinal sks2 ->
      ( resolved,
        List.fold_right2
          (fun sk1 sk2 ->
            UnresolvedConstraints.add_skeleton_equality (sk1, sk2))
          (sks1 |> TyParam.Map.values)
          (sks2 |> TyParam.Map.values)
          unresolved )
  | Tuple sks1, Tuple sks2 when List.length sks1 = List.length sks2 ->
      ( resolved,
        List.fold_right2
          (fun sk1 sk2 ->
            UnresolvedConstraints.add_skeleton_equality (sk1, sk2))
          sks1 sks2 unresolved )
  | _ ->
      let printer = Type.print_pretty Skeleton.Param.Set.empty in
      Error.typing ~loc
        "This expression has type %t but it should have type %t." (printer sk1)
        (printer sk2)

and ty_eq_step resolved unresolved ty1 ty2 =
  match (ty1.term, ty2.term) with
  (* ς = ς *)
  | TyParam p1, TyParam p2 when p1 = p2 -> (resolved, unresolved)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  (* There is no need for occurs-check because skeletons of both sides are equal *)
  | TyParam p1, _ ->
      let sub1 = Substitution.add_type_substitution_e p1 ty2 in
      apply_substitution sub1 resolved unresolved
  | _, TyParam p2 ->
      let sub1 = Substitution.add_type_substitution_e p2 ty1 in
      apply_substitution sub1 resolved unresolved
      (* int = int *)
  | TyBasic ps1, TyBasic ps2 when ps1 = ps2 -> (resolved, unresolved)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | Arrow (tya, (tyb, drt1)), Arrow (tyc, (tyd, drt2)) ->
      ( resolved,
        unresolved
        |> UnresolvedConstraints.add_ty_equality (tya, tyc)
        |> UnresolvedConstraints.add_ty_equality (tyb, tyd)
        |> UnresolvedConstraints.add_dirt_equality (drt1, drt2) )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | Handler ((tya, drta), (tyb, drtb)), Handler ((tyc, drtc), (tyd, drtd)) ->
      ( resolved,
        unresolved
        |> UnresolvedConstraints.add_ty_equality (tya, tyc)
        |> UnresolvedConstraints.add_ty_equality (tyb, tyd)
        |> UnresolvedConstraints.add_dirt_equality (drta, drtc)
        |> UnresolvedConstraints.add_dirt_equality (drtb, drtd) )
  | ( Apply { ty_name = ty_name1; ty_args = tys1 },
      Apply { ty_name = ty_name2; ty_args = tys2 } )
    when ty_name1 = ty_name2
         && TyParam.Map.cardinal tys1 = TyParam.Map.cardinal tys2 ->
      ( resolved,
        List.fold_right2
          (fun (ty1, _) (ty2, _) ->
            UnresolvedConstraints.add_ty_equality (ty1, ty2))
          (tys1 |> TyParam.Map.values)
          (tys2 |> TyParam.Map.values)
          unresolved )
  | Tuple tys1, Tuple tys2 when List.length tys1 = List.length tys2 ->
      ( resolved,
        List.fold_right2
          (fun ty1 ty2 -> UnresolvedConstraints.add_ty_equality (ty1, ty2))
          tys1 tys2 unresolved )
  | _ -> assert false

and ty_omega_step type_definitions resolved unresolved omega = function
  (* ω : A <= A *)
  | ty1, ty2 when Type.equal_ty ty1 ty2 ->
      let k = omega in
      let v = TyCoercion.reflTy ty1 in
      (resolved, change_subst (Substitution.add_type_coercion k v) unresolved)
  (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
  | { term = Type.Arrow (a1, dirty1); _ }, { term = Type.Arrow (a2, dirty2); _ }
    ->
      let new_ty_coercion_var_coer, unresolved' =
        UnresolvedConstraints.fresh_ty_coer unresolved (a2, a1)
      in
      let dirty_coercion_c, unresolved'' =
        UnresolvedConstraints.fresh_dirty_coer unresolved' (dirty1, dirty2)
      in
      let k = omega in
      let v =
        TyCoercion.arrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c)
      in
      (resolved, change_subst (Substitution.add_type_coercion k v) unresolved'')
  (* ω : A₁ x A₂ x ... <= B₁ x B₂ x ...  *)
  | { term = Type.Tuple tys; _ }, { term = Type.Tuple tys'; _ } ->
      let coercions, unresolved' =
        List.fold_right2
          (fun ty ty' (coercions, unresolved) ->
            let coercion, unresolved' =
              UnresolvedConstraints.fresh_ty_coer unresolved (ty, ty')
            in
            (coercion :: coercions, unresolved'))
          tys tys' ([], unresolved)
      in
      let k = omega in
      let v = TyCoercion.tupleCoercion coercions in
      (resolved, change_subst (Substitution.add_type_coercion k v) unresolved')
  (* ω : ty (A₁,  A₂,  ...) <= ty (B₁,  B₂,  ...) *)
  | ( { term = Type.Apply { ty_name = ty_name1; ty_args = tys1 }; _ },
      { term = Type.Apply { ty_name = ty_name2; ty_args = tys2 }; _ } )
    when ty_name1 = ty_name2
         && TyParam.Map.cardinal tys1 = TyParam.Map.cardinal tys2 ->
      let coercions, unresolved' =
        List.fold_right2
          (fun (p1, (ty, v1)) (p2, (ty', v2)) (coercions, unresolved) ->
            assert (p1 = p2);
            assert (v1 = v2);
            let coercion, unresolved' =
              match v1 with
              | Covariant ->
                  let coercion, unresolved' =
                    UnresolvedConstraints.fresh_ty_coer unresolved (ty, ty')
                  in
                  (coercion, unresolved')
              | Contravariant ->
                  let coercion, unresolved' =
                    UnresolvedConstraints.fresh_ty_coer unresolved (ty', ty)
                  in
                  (coercion, unresolved')
              | Invariant ->
                  ( TyCoercion.reflTy ty,
                    UnresolvedConstraints.add_ty_equality (ty, ty') unresolved
                  )
            in
            ((p1, (coercion, v1)) :: coercions, unresolved'))
          (TyParam.Map.bindings tys1)
          (TyParam.Map.bindings tys2)
          ([], unresolved)
      in
      let v =
        TyCoercion.applyCoercion (ty_name1, coercions |> TyParam.Map.of_bindings)
      in
      ( resolved,
        change_subst (Substitution.add_type_coercion omega v) unresolved' )
  (* ω : D₁ => C₁ <= D₂ => C₂ *)
  | ( { term = Type.Handler (drty11, drty12); _ },
      { term = Type.Handler (drty21, drty22); _ } ) ->
      let drty_coer1, unresolved' =
        UnresolvedConstraints.fresh_dirty_coer unresolved (drty21, drty11)
      in
      let drty_coer2, unresolved'' =
        UnresolvedConstraints.fresh_dirty_coer unresolved' (drty12, drty22)
      in
      let k = omega in
      let v = TyCoercion.handlerCoercion (drty_coer1, drty_coer2) in
      (resolved, change_subst (Substitution.add_type_coercion k v) unresolved'')
  (* ω : α <= A /  ω : A <= α *)
  | ( ({ term = Type.TyParam t1; ty = Skeleton.Param s1 } as ty1),
      ({ term = Type.TyParam t2; ty = Skeleton.Param s2 } as ty2) )
    when s1 = s2 -> (
      (*unify_ty_vars (sub,resolved,unresolved) tv a cons*)
      let existing =
        resolved.Constraints.ty_constraints
        |> Constraints.TyConstraints.get_ty_graph s1
        |> Constraints.TyConstraints.TyParamGraph.get_edges t1
        |> TyParam.Map.find_opt t2
      in
      match existing with
      | None ->
          (Constraints.add_ty_constraint s1 t1 t2 omega resolved, unresolved)
      | Some w ->
          ( resolved,
            change_subst
              (Substitution.add_type_coercion omega
                 (TyCoercion.tyCoercionVar w (ty1, ty2)))
              unresolved ))
  | ( { term = Type.TyParam tv; ty = skel }, _
    | _, { term = Type.TyParam tv; ty = skel } ) as ct ->
      let ty = fresh_ty_with_skel type_definitions skel in
      apply_substitution
        (Substitution.add_type_substitution_e tv ty)
        resolved
        (UnresolvedConstraints.add_ty_inequality (omega, ct) unresolved)
  | _ -> assert false

and dirt_omega_step ~loc resolved unresolved w dcons =
  match dcons with
  (* ω : A <= A *)
  | drt1, drt2 when Type.equal_dirt drt1 drt2 ->
      let v = DirtCoercion.reflDirt drt1 in
      ( resolved,
        change_subst (Substitution.add_dirt_var_coercion w v) unresolved )
  (* ω : δ₁ <= O₂ ∪ δ₂ *)
  | ( ({ Dirt.effect_set = ops1; row = Dirt.Row.Param d1 } as ty1),
      ({ Dirt.effect_set = ops2; row = Dirt.Row.Param d2 } as ty2) )
    when Effect.Set.is_empty ops1 -> (
      let dirt_edges =
        Constraints.DirtConstraints.DirtParamGraph.get_edges d1
          resolved.Constraints.dirt_constraints
      in
      match Dirt.Param.Map.find_opt d2 dirt_edges with
      | None ->
          (Constraints.add_dirt_constraint d1 d2 w ops2 resolved, unresolved)
      | Some (d, _) ->
          ( resolved,
            change_subst
              (Substitution.add_dirt_var_coercion w
                 { term = DirtCoercion.DirtCoercionVar d; ty = (ty1, ty2) })
              unresolved ))
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = ops1; row = Dirt.Row.Param d1 },
      { effect_set = ops2; row = Dirt.Row.Param d2 } ) ->
      let w' = DirtCoercionParam.refresh w in
      let d2' = Dirt.Param.refresh d2 in
      let w_ty' =
        ( { Dirt.effect_set = Effect.Set.empty; row = Dirt.Row.Param d1 },
          {
            Dirt.effect_set = Effect.Set.union ops1 ops2;
            row = Dirt.Row.Param d2';
          } )
      in
      let sub_d =
        Substitution.add_dirt_substitution_e d2
          { effect_set = Effect.Set.diff ops1 ops2; row = Dirt.Row.Param d2' }
      in
      let sub' =
        sub_d
        |> Substitution.add_dirt_var_coercion w
             (* In case d1 = d2, we need to replace d1 as well in order for the
                substitution to be idempotent *)
             (Substitution.apply_sub_dirtcoer sub_d
                (DirtCoercion.unionDirt
                   (ops1, DirtCoercion.dirtCoercionVar w' w_ty')))
      in
      apply_substitution sub' resolved
        (UnresolvedConstraints.add_dirt_inequality (w', w_ty') unresolved)
  (* ω : Ø <= Δ₂ *)
  | { effect_set = ops1; row = Dirt.Row.Empty }, d when Effect.Set.is_empty ops1
    ->
      ( resolved,
        change_subst
          (Substitution.add_dirt_var_coercion w (DirtCoercion.empty d))
          unresolved )
  (* ω : δ₁ <= Ø *)
  | ( { effect_set = ops1; row = Dirt.Row.Param d1 },
      { effect_set = ops2; row = Dirt.Row.Empty } )
    when Effect.Set.is_empty ops1 && Effect.Set.is_empty ops2 ->
      let sub' =
        Substitution.add_dirt_var_coercion_e w (DirtCoercion.empty Dirt.empty)
        |> Substitution.add_dirt_substitution d1 Dirt.empty
      in
      apply_substitution sub' resolved unresolved
  (* ω : O₁ <= O₂ *)
  | ( { effect_set = ops1; row = Dirt.Row.Empty },
      { effect_set = ops2; row = Dirt.Row.Empty } ) ->
      if not (Effect.Set.subset ops1 ops2) then
        Error.typing ~loc "Effects %t are not a subset of %t"
          (Effect.Set.print ops1) (Effect.Set.print ops2);
      let unresolved' =
        change_subst
          (Substitution.add_dirt_var_coercion w
             (DirtCoercion.unionDirt
                ( ops2,
                  DirtCoercion.empty (Dirt.closed (Effect.Set.diff ops2 ops1))
                )))
          unresolved
      in
      (resolved, unresolved')
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = ops1; row = Dirt.Row.Empty },
      { effect_set = ops2; row = Dirt.Row.Param d2 } ) ->
      let d2' = Dirt.Param.refresh d2 in
      let sub' =
        Substitution.add_dirt_var_coercion_e w
          (DirtCoercion.unionDirt
             ( ops1,
               DirtCoercion.empty
                 {
                   Dirt.effect_set = Effect.Set.diff ops2 ops1;
                   row = Dirt.Row.Param d2';
                 } ))
        |> Substitution.add_dirt_substitution d2
             {
               effect_set = Effect.Set.diff ops1 ops2;
               row = Dirt.Row.Param d2';
             }
      in
      apply_substitution sub' resolved unresolved
  | _ -> assert false

and dirt_eq_step ~loc resolved unresolved { Dirt.effect_set = o1; row = row1 }
    { Dirt.effect_set = o2; row = row2 } =
  (*
  Consider the equation:
    O ∪ row₁ = O ∪ row₂
  where row₁ and row₂ are either some parameters δ or the empty row Ø.
  Any solution to this equation is equivalent to a solution of

      row₁ = (O₂ \ O₁) ∪ row₁'
      row₂ = (O₁ \ O₂) ∪ row₂'
      row₁' = row₂'

  *)
  let sub = unresolved.UnresolvedConstraints.substitution in
  let sub', row1' = expand_row ~loc sub row1 (Effect.Set.diff o2 o1) in
  let sub'', row2' = expand_row ~loc sub' row2 (Effect.Set.diff o1 o2) in
  let sub''' =
    match (row1', row2') with
    | Dirt.Row.Empty, Dirt.Row.Empty -> sub''
    | Dirt.Row.Param p1, _ ->
        Substitution.add_dirt_substitution p1
          { effect_set = Effect.Set.empty; row = row2' }
          sub''
    | _, Dirt.Row.Param p2 ->
        Substitution.add_dirt_substitution p2
          { effect_set = Effect.Set.empty; row = row1' }
          sub''
  in
  apply_substitution sub''' resolved unresolved

let rec unify' ~loc type_definitions (resolved, unresolved) =
  (* Print.debug "SUB: %t" (Substitution.print sub); *)
  (* Print.debug "resolved: %t" (Constraints.print resolved); *)
  (* Print.debug "unresolved: %t" (UnresolvedConstraints.print unresolved); *)
  match unresolved with
  | UnresolvedConstraints.
      { skeleton_equalities = (sk1, sk2) :: skeleton_equalities; _ } ->
      skel_eq_step ~loc resolved { unresolved with skeleton_equalities } sk1 sk2
      |> unify' ~loc type_definitions
  | { dirt_equalities = (drt1, drt2) :: dirt_equalities; _ } ->
      dirt_eq_step ~loc resolved { unresolved with dirt_equalities } drt1 drt2
      |> unify' ~loc type_definitions
  | { dirt_inequalities = (omega, dcons) :: dirt_inequalities; _ } ->
      dirt_omega_step ~loc resolved
        { unresolved with dirt_inequalities }
        omega dcons
      |> unify' ~loc type_definitions
  | { ty_equalities = (ty1, ty2) :: _; _ }
    when not (Skeleton.equal ty1.ty ty2.ty) ->
      skel_eq_step ~loc resolved unresolved ty1.ty ty2.ty
      |> unify' ~loc type_definitions
  | { ty_equalities = (ty1, ty2) :: ty_equalities; _ } ->
      ty_eq_step resolved { unresolved with ty_equalities } ty1 ty2
      |> unify' ~loc type_definitions
  | { ty_inequalities = (_, (ty1, ty2)) :: _; _ }
    when not (Skeleton.equal ty1.ty ty2.ty) ->
      skel_eq_step ~loc resolved unresolved ty1.ty ty2.ty
      |> unify' ~loc type_definitions
  | { ty_inequalities = (omega, tycons) :: ty_inequalities; _ } ->
      ty_omega_step type_definitions resolved
        { unresolved with ty_inequalities }
        omega tycons
      |> unify' ~loc type_definitions
  | {
   skeleton_equalities = [];
   dirt_equalities = [];
   dirt_inequalities = [];
   ty_equalities = [];
   ty_inequalities = [];
   substitution;
  } ->
      (substitution, resolved)

let unify ~loc type_definitions (sub, resolved, unresolved) =
  unify' ~loc type_definitions
    (resolved, change_subst (Substitution.merge sub) unresolved)

let solve ~loc type_definitions constraints =
  let sub, constraints =
    unify' ~loc type_definitions (Constraints.empty, constraints)
  in

  (* Print.debug "sub: %t" (Substitution.print sub); *)
  (* Print.debug "solved: %t" (Constraints.print constraints); *)
  (sub, constraints)
