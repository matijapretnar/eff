open Utils
open Language
open Type

let apply_substitution new_sub sub (paused : Type.Constraints.t) queue =
  let substitute_ty_constraint s t1 t2 w ty1 ty2 (paused, queue) =
    let ty1', ty2' =
      ( Substitution.apply_substitutions_to_type new_sub ty1,
        Substitution.apply_substitutions_to_type new_sub ty2 )
    in
    if Type.equal_ty ty1 ty1' && Type.equal_ty ty2 ty2' then
      (Type.Constraints.add_ty_constraint s t1 t2 w paused, queue)
    else (paused, Constraint.add_ty_inequality (w, (ty1', ty2')) queue)
  and substitute_dirt_constraint d1 d2 w effs drt1 drt2 (paused, queue) =
    let drt1', drt2' =
      ( Substitution.apply_substitutions_to_dirt new_sub drt1,
        Substitution.apply_substitutions_to_dirt new_sub drt2 )
    in
    if Type.equal_dirt drt1 drt1' && Type.equal_dirt drt2 drt2' then
      (Type.Constraints.add_dirt_constraint paused d1 d2 w effs, queue)
    else (paused, Constraint.add_dirt_inequality (w, (drt1', drt2')) queue)
  in
  let sub' = Substitution.merge new_sub sub in
  let paused', queue' =
    (Type.Constraints.empty, Constraint.apply_sub new_sub queue)
    |> Type.TyConstraints.fold_expanded substitute_ty_constraint
         paused.ty_constraints
    |> Type.DirtConstraints.fold_expanded substitute_dirt_constraint
         paused.dirt_constraints
  in
  (sub', paused', queue')

let expand_row row ops =
  match row with
  | _ when Type.Effect.Set.is_empty ops -> (Substitution.empty, row)
  | ParamRow p ->
      let p' = Type.DirtParam.refresh p in
      let row' = ParamRow p' in
      let sub' =
        Substitution.add_dirt_substitution_e p { effect_set = ops; row = row' }
      in
      (sub', row')
  | EmptyRow -> Error.typing ~loc:Location.unknown "Cannot extend an empty row."

let skel_eq_step sub (paused : Type.Constraints.t) rest_queue sk1 sk2 =
  match (sk1, sk2) with
  (* ς = ς *)
  | SkelParam sp1, SkelParam sp2 when sp1 = sp2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | SkelParam sp1, sk2a
    when not (SkelParam.Set.mem sp1 (free_params_skeleton sk2a).skel_params) ->
      apply_substitution
        (Substitution.add_skel_param_substitution_e sp1 sk2a)
        sub paused rest_queue
  | sk2a, SkelParam sp1
    when not (SkelParam.Set.mem sp1 (free_params_skeleton sk2a).skel_params) ->
      apply_substitution
        (Substitution.add_skel_param_substitution_e sp1 sk2a)
        sub paused rest_queue
      (* occurs-check failing *)
  | SkelParam _, _ | _, SkelParam _ ->
      let printer = Type.print_pretty () in
      Error.typing ~loc:Location.unknown
        "This expression has a forbidden cyclic type %t = %t." (printer sk1)
        (printer sk2)
      (* int = int *)
  | SkelBasic ps1, SkelBasic ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | SkelArrow (ska, skb), SkelArrow (skc, skd) ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_skeleton_equality (ska, skc)
        |> Constraint.add_skeleton_equality (skb, skd) )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | SkelHandler (ska, skb), SkelHandler (skc, skd) ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_skeleton_equality (ska, skc)
        |> Constraint.add_skeleton_equality (skb, skd) )
  | SkelApply (ty_name1, sks1), SkelApply (ty_name2, sks2)
    when ty_name1 = ty_name2 && List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun sk1 sk2 -> Constraint.add_skeleton_equality (sk1, sk2))
          sks1 sks2 rest_queue )
  | SkelTuple sks1, SkelTuple sks2 when List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun sk1 sk2 -> Constraint.add_skeleton_equality (sk1, sk2))
          sks1 sks2 rest_queue )
  | _ ->
      let printer = Type.print_pretty () in
      Error.typing ~loc:Location.unknown
        "This expression has type %t but it should have type %t." (printer sk1)
        (printer sk2)

and ty_eq_step sub (paused : Type.Constraints.t) rest_queue (ty1 : Type.ty)
    (ty2 : Type.ty) =
  match (ty1.term, ty2.term) with
  | _, _ when ty1.ty <> ty2.ty ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_ty_equality (ty1, ty2)
        |> Constraint.add_skeleton_equality (ty1.ty, ty2.ty) )
  (* ς = ς *)
  | TyParam p1, TyParam p2 when p1 = p2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | TyParam p1, _ when not (TyParam.Map.mem p1 (free_params_ty ty2).ty_params)
    ->
      let sub1 = Substitution.add_type_substitution_e p1 ty2 in
      apply_substitution sub1 sub paused rest_queue
  | _, TyParam p2 when not (TyParam.Map.mem p2 (free_params_ty ty1).ty_params)
    ->
      let sub1 = Substitution.add_type_substitution_e p2 ty1 in
      apply_substitution sub1 sub paused rest_queue
      (* occurs-check failing *)
  | TyParam _, _ | _, TyParam _ ->
      let printer = Type.print_pretty () in
      Error.typing ~loc:Location.unknown
        "This expression has a forbidden cyclic type %t = %t." (printer ty1.ty)
        (printer ty2.ty)
      (* int = int *)
  | TyBasic ps1, TyBasic ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | Arrow (tya, (tyb, drt1)), Arrow (tyc, (tyd, drt2)) ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_ty_equality (tya, tyc)
        |> Constraint.add_ty_equality (tyb, tyd)
        |> Constraint.add_dirt_equality (drt1, drt2) )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | Handler ((tya, drta), (tyb, drtb)), Handler ((tyc, drtc), (tyd, drtd)) ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_ty_equality (tya, tyc)
        |> Constraint.add_ty_equality (tyb, tyd)
        |> Constraint.add_dirt_equality (drta, drtc)
        |> Constraint.add_dirt_equality (drtb, drtd) )
  | ( Apply { ty_name = ty_name1; ty_args = tys1 },
      Apply { ty_name = ty_name2; ty_args = tys2 } )
    when ty_name1 = ty_name2 && List.length tys1 = List.length tys2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun ty1 ty2 -> Constraint.add_ty_equality (ty1, ty2))
          tys1 tys2 rest_queue )
  | Tuple tys1, Tuple tys2 when List.length tys1 = List.length tys2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun ty1 ty2 -> Constraint.add_ty_equality (ty1, ty2))
          tys1 tys2 rest_queue )
  | _ ->
      let printer = Type.print_pretty () in
      Error.typing ~loc:Location.unknown
        "This expression has type %t but it should have type %t."
        (printer ty1.ty) (printer ty2.ty)

and ty_omega_step sub (paused : Type.Constraints.t) cons rest_queue omega =
  function
  (* ω : A <= A *)
  | ty1, ty2 when Type.equal_ty ty1 ty2 ->
      let k = omega in
      let v = Coercion.reflTy ty1 in
      (Substitution.add_type_coercion k v sub, paused, rest_queue)
  (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
  | { term = Type.Arrow (a1, dirty1); _ }, { term = Type.Arrow (a2, dirty2); _ }
    ->
      let new_ty_coercion_var_coer, ty_cons = Constraint.fresh_ty_coer (a2, a1)
      and dirty_coercion_c, dirty_cnstrs =
        Constraint.fresh_dirty_coer (dirty1, dirty2)
      in
      let k = omega in
      let v =
        Coercion.arrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c)
      in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.list_union [ ty_cons; rest_queue; dirty_cnstrs ] )
  (* ω : A₁ x A₂ x ... <= B₁ x B₂ x ...  *)
  | { term = Type.Tuple tys; _ }, { term = Type.Tuple tys'; _ }
    when List.length tys = List.length tys' ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = Constraint.fresh_ty_coer (ty, ty') in
            (coercion :: coercions, Constraint.union ty_cons conss))
          tys tys' ([], Constraint.empty)
      in
      let k = omega in
      let v = Coercion.tupleCoercion coercions in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.union conss rest_queue )
  (* ω : ty (A₁,  A₂,  ...) <= ty (B₁,  B₂,  ...) *)
  (* we assume that all type parameters are positive *)
  | ( { term = Type.Apply { ty_name = ty_name1; ty_args = tys1 }; _ },
      { term = Type.Apply { ty_name = ty_name2; ty_args = tys2 }; _ } )
    when ty_name1 = ty_name2 && List.length tys1 = List.length tys2 ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = Constraint.fresh_ty_coer (ty, ty') in
            (coercion :: coercions, Constraint.union ty_cons conss))
          tys1 tys2 ([], Constraint.empty)
      in
      let k = omega in
      let v = Coercion.applyCoercion (ty_name1, coercions) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.union conss rest_queue )
  (* ω : D₁ => C₁ <= D₂ => C₂ *)
  | ( { term = Type.Handler (drty11, drty12); _ },
      { term = Type.Handler (drty21, drty22); _ } ) ->
      let drty_coer1, dirty_cons1 = Constraint.fresh_dirty_coer (drty21, drty11)
      and drty_coer2, dirty_cons2 =
        Constraint.fresh_dirty_coer (drty12, drty22)
      in
      let k = omega in
      let v = Coercion.handlerCoercion (drty_coer1, drty_coer2) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.list_union [ dirty_cons1; dirty_cons2; rest_queue ] )
  (* ω : α <= A /  ω : A <= α *)
  | ( { term = Type.TyParam t1; ty = SkelParam s1 },
      { term = Type.TyParam t2; ty = SkelParam s2 } )
    when s1 = s2 ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      (sub, Type.Constraints.add_ty_constraint s1 t1 t2 omega paused, rest_queue)
  | { term = Type.TyParam _; ty = SkelParam _ as skel_tv }, a
  | a, { term = Type.TyParam _; ty = SkelParam _ as skel_tv } ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      let skel_a = Type.skeleton_of_ty a in
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_skeleton_equality (skel_tv, skel_a)
        |> Constraint.union cons )
  | { term = Type.TyParam tv; ty = skel }, _
  | _, { term = Type.TyParam tv; ty = skel } ->
      let ty = fresh_ty_with_skel skel in
      apply_substitution
        (Substitution.add_type_substitution_e tv ty)
        sub paused
        (Constraint.union cons rest_queue)
  | ty1, ty2 ->
      let printer = Type.print_pretty () in
      Error.typing ~loc:Location.unknown
        "This expression has type %t but it should have type %t."
        (printer ty1.ty) (printer ty2.ty)

and dirt_omega_step sub resolved unresolved w dcons =
  match dcons with
  (* ω : δ₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = ops1; row = ParamRow d1 },
      { effect_set = ops2; row = ParamRow d2 } )
    when Effect.Set.is_empty ops1 ->
      ( sub,
        Type.Constraints.add_dirt_constraint resolved d1 d2 w ops2,
        unresolved )
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = ops1; row = ParamRow d1 },
      { effect_set = ops2; row = ParamRow d2 } ) ->
      let w' = DirtCoercionParam.refresh w in
      let d2' = DirtParam.refresh d2 in
      let w_ty' =
        ( { effect_set = Effect.Set.empty; row = ParamRow d1 },
          { effect_set = Effect.Set.union ops1 ops2; row = ParamRow d2' } )
      in
      let sub' =
        Substitution.add_dirt_substitution_e d2
          { effect_set = Effect.Set.diff ops1 ops2; row = ParamRow d2' }
        |> Substitution.add_dirt_var_coercion w
             (Coercion.unionDirt (ops1, Coercion.dirtCoercionVar w' w_ty'))
      in
      apply_substitution sub' sub resolved
        (Constraint.add_dirt_inequality (w', w_ty') unresolved)
  (* ω : Ø <= Δ₂ *)
  | { effect_set = ops1; row = EmptyRow }, d when Effect.Set.is_empty ops1 ->
      let sub' = Substitution.add_dirt_var_coercion w (Coercion.empty d) sub in
      (sub', resolved, unresolved)
  (* ω : δ₁ <= Ø *)
  | ( { effect_set = ops1; row = ParamRow d1 },
      { effect_set = ops2; row = EmptyRow } )
    when Effect.Set.is_empty ops1 && Effect.Set.is_empty ops2 ->
      let sub' =
        Substitution.add_dirt_var_coercion_e w (Coercion.empty empty_dirt)
        |> Substitution.add_dirt_substitution d1 empty_dirt
      in
      apply_substitution sub' sub resolved unresolved
  (* ω : O₁ <= O₂ *)
  | { effect_set = ops1; row = EmptyRow }, { effect_set = ops2; row = EmptyRow }
    ->
      assert (Effect.Set.subset ops1 ops2);
      let sub' =
        Substitution.add_dirt_var_coercion w
          (Coercion.unionDirt
             (ops2, Coercion.empty (closed_dirt (Effect.Set.diff ops2 ops1))))
          sub
      in
      (sub', resolved, unresolved)
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = ops1; row = EmptyRow },
      { effect_set = ops2; row = ParamRow d2 } ) ->
      let d2' = DirtParam.refresh d2 in
      let sub' =
        Substitution.add_dirt_var_coercion_e w
          (Coercion.unionDirt
             ( ops1,
               Coercion.empty
                 { effect_set = Effect.Set.diff ops2 ops1; row = ParamRow d2' }
             ))
        |> Substitution.add_dirt_substitution d2
             { effect_set = Effect.Set.diff ops1 ops2; row = ParamRow d2' }
      in
      apply_substitution sub' sub resolved unresolved
  | _ -> assert false

and dirt_eq_step sub paused rest_queue { effect_set = o1; row = row1 }
    { effect_set = o2; row = row2 } =
  (*
  Consider the equation:
    O ∪ row₁ = O ∪ row₂
  where row₁ and row₂ are either some parameters δ or the empty row Ø.
  Any solution to this equation is equivalent to a solution of

      row₁ = (O₂ \ O₁) ∪ row₁'
      row₂ = (O₁ \ O₂) ∪ row₂'
      row₁' = row₂'

  *)
  let sub1, row1' = expand_row row1 (Effect.Set.diff o2 o1)
  and sub2, row2' = expand_row row2 (Effect.Set.diff o1 o2) in
  let row_sub =
    match (row1', row2') with
    | EmptyRow, EmptyRow -> Substitution.empty
    | ParamRow p1, _ ->
        Substitution.add_dirt_substitution_e p1
          { effect_set = Effect.Set.empty; row = row2' }
    | _, ParamRow p2 ->
        Substitution.add_dirt_substitution_e p2
          { effect_set = Effect.Set.empty; row = row1' }
  in
  let sub' = Substitution.merge (Substitution.merge sub1 sub2) row_sub in
  apply_substitution sub' sub paused rest_queue

let rec unify (sub, paused, (queue : Constraint.t)) =
  Print.debug "SUB: %t" (Substitution.print sub);
  Print.debug "PAUSED: %t" (Type.Constraints.print paused);
  Print.debug "QUEUE: %t" (Constraint.print queue);
  match queue with
  | { skeleton_equalities = (sk1, sk2) :: skeleton_equalities; _ } ->
      skel_eq_step sub paused { queue with skeleton_equalities } sk1 sk2
      |> unify
  | { dirt_equalities = (drt1, drt2) :: dirt_equalities; _ } ->
      dirt_eq_step sub paused { queue with dirt_equalities } drt1 drt2 |> unify
  | { dirt_inequalities = (omega, dcons) :: dirt_inequalities; _ } ->
      dirt_omega_step sub paused { queue with dirt_inequalities } omega dcons
      |> unify
  | { ty_equalities = (ty1, ty2) :: ty_equalities; _ } ->
      ty_eq_step sub paused { queue with ty_equalities } ty1 ty2 |> unify
  | { ty_inequalities = (omega, tycons) :: ty_inequalities; _ } ->
      let cons =
        Constraint.add_ty_inequality (omega, tycons) Constraint.empty
      in
      ty_omega_step sub paused cons { queue with ty_inequalities } omega tycons
      |> unify
  | {
   skeleton_equalities = [];
   dirt_equalities = [];
   dirt_inequalities = [];
   ty_equalities = [];
   ty_inequalities = [];
  } ->
      (sub, paused)

let solve constraints =
  (* Print.debug "constraints: %t" (Constraint.print_constraints constraints); *)
  let solved =
    unify (Substitution.empty, Type.Constraints.empty, constraints)
  in
  (* Print.debug "sub: %t" (Substitution.print_substitutions sub); *)
  (* Print.debug "solved: %t" (Constraint.print_constraints solved); *)
  solved
