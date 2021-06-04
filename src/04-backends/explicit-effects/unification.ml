open Utils
open Type

let fresh_ty_with_skel skel =
  match skel with
  (* α : ς *)
  | SkelParam _ -> assert false
  (* α : int *)
  | SkelBasic ps -> Type.TyBasic ps
  (* α : τ₁ -> τ₂ *)
  | SkelArrow (sk1, sk2) ->
      let tvar1 = Constraint.fresh_ty_with_skel sk1
      and dtvar2 = Constraint.fresh_dirty_with_skel sk2 in
      Type.Arrow (tvar1, dtvar2)
  (* α : τ₁ x τ₂ ... *)
  | SkelTuple sks ->
      let tvars = List.map Constraint.fresh_ty_with_skel sks in
      Type.Tuple tvars
  (* α : ty_name (τ₁, τ₂, ...) *)
  | SkelApply (ty_name, sks) ->
      let tvars = List.map Constraint.fresh_ty_with_skel sks in
      Type.Apply (ty_name, tvars)
  (* α : τ₁ => τ₂ *)
  | SkelHandler (sk1, sk2) ->
      let dtvar1 = Constraint.fresh_dirty_with_skel sk1
      and dtvar2 = Constraint.fresh_dirty_with_skel sk2 in
      Type.Handler (dtvar1, dtvar2)

let process_skeleton_parameter_equality sub (paused : Constraint.resolved)
    rest_queue sp1 sk2a =
  let k = sp1 in
  let v = sk2a in
  let sub1 = Substitution.add_skel_param_substitution_e k v in
  let cons_subbed =
    Substitution.apply_substitutions_to_constraints sub1
      (Constraint.return_resolved paused rest_queue)
  in
  ( Substitution.add_skel_param_substitution k v sub,
    Constraint.empty_resolved,
    cons_subbed )

let skel_eq_step sub (paused : Constraint.resolved) rest_queue sk1 sk2 =
  match (sk1, sk2) with
  (* ς = ς *)
  | SkelParam sp1, SkelParam sp2 when sp1 = sp2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | SkelParam sp1, sk2a
    when not (SkelParamSet.mem sp1 (free_params_skeleton sk2a).skel_params) ->
      process_skeleton_parameter_equality sub paused rest_queue sp1 sk2a
  | sk2a, SkelParam sp1
    when not (SkelParamSet.mem sp1 (free_params_skeleton sk2a).skel_params) ->
      process_skeleton_parameter_equality sub paused rest_queue sp1 sk2a
  (* int = int *)
  | SkelBasic ps1, SkelBasic ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | SkelArrow (ska, skb), SkelArrow (skc, skd) ->
      ( sub,
        paused,
        Constraint.add_list_to_constraints
          [ Constraint.SkelEq (ska, skc); Constraint.SkelEq (skb, skd) ]
          rest_queue )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | SkelHandler (ska, skb), SkelHandler (skc, skd) ->
      ( sub,
        paused,
        Constraint.add_list_to_constraints
          [ Constraint.SkelEq (ska, skc); Constraint.SkelEq (skb, skd) ]
          rest_queue )
  | SkelApply (ty_name1, sks1), SkelApply (ty_name2, sks2)
    when ty_name1 = ty_name2 && List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        Constraint.add_list_to_constraints
          (List.map2 (fun sk1 sk2 -> Constraint.SkelEq (sk1, sk2)) sks1 sks2)
          rest_queue )
  | SkelTuple sks1, SkelTuple sks2 when List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        Constraint.add_list_to_constraints
          (List.map2 (fun sk1 sk2 -> Constraint.SkelEq (sk1, sk2)) sks1 sks2)
          rest_queue )
  | _ ->
      (* Print.debug "%t = %t" (Type.print_skeleton sk1) (Type.print_skeleton sk2); *)
      assert false

and ty_omega_step sub (paused : Constraint.resolved) cons rest_queue omega =
  function
  (* ω : A <= A *)
  | x, y when Type.equal_ty x y ->
      let k = omega in
      let v = Constraint.reflTy x in
      (Substitution.add_type_coercion k v sub, paused, rest_queue)
  (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
  | Type.Arrow (a1, dirty1), Type.Arrow (a2, dirty2) ->
      let new_ty_coercion_var_coer, ty_cons = Constraint.fresh_ty_coer (a2, a1)
      and dirty_coercion_c, dirty_cnstrs =
        Constraint.fresh_dirty_coer (dirty1, dirty2)
      in
      let k = omega in
      let v =
        Constraint.arrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c)
      in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.add_to_constraints ty_cons (rest_queue @ dirty_cnstrs) )
  (* ω : A₁ x A₂ x ... <= B₁ x B₂ x ...  *)
  | Type.Tuple tys, Type.Tuple tys' when List.length tys = List.length tys' ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = Constraint.fresh_ty_coer (ty, ty') in
            (coercion :: coercions, ty_cons :: conss))
          tys tys' ([], [])
      in
      let k = omega in
      let v = Constraint.tupleCoercion coercions in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.add_list_to_constraints conss rest_queue )
  (* ω : ty (A₁,  A₂,  ...) <= ty (B₁,  B₂,  ...) *)
  (* we assume that all type parameters are positive *)
  | Type.Apply (ty_name1, tys1), Type.Apply (ty_name2, tys2)
    when ty_name1 = ty_name2 && List.length tys1 = List.length tys2 ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = Constraint.fresh_ty_coer (ty, ty') in
            (coercion :: coercions, ty_cons :: conss))
          tys1 tys2 ([], [])
      in
      let k = omega in
      let v = Constraint.applyCoercion (ty_name1, coercions) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        Constraint.add_list_to_constraints conss rest_queue )
  (* ω : D₁ => C₁ <= D₂ => C₂ *)
  | Type.Handler (drty11, drty12), Type.Handler (drty21, drty22) ->
      let drty_coer1, dirty_cons1 = Constraint.fresh_dirty_coer (drty21, drty11)
      and drty_coer2, dirty_cons2 =
        Constraint.fresh_dirty_coer (drty12, drty22)
      in
      let k = omega in
      let v = Constraint.handlerCoercion (drty_coer1, drty_coer2) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        dirty_cons1 @ dirty_cons2 @ rest_queue )
  (* ω : α <= A /  ω : A <= α *)
  | Type.TyParam (p1, SkelParam s1), Type.TyParam (p2, SkelParam s2)
    when s1 = s2 ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      (sub, Constraint.resolve_ty_constraint paused omega p1 p2 s1, rest_queue)
  | Type.TyParam (_, (SkelParam _ as skel_tv)), a
  | a, Type.TyParam (_, (SkelParam _ as skel_tv)) ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      let skel_a = Type.skeleton_of_ty a in
      ( sub,
        paused,
        Constraint.add_to_constraints
          (Constraint.SkelEq (skel_tv, skel_a))
          (Constraint.add_to_constraints cons rest_queue) )
  | Type.TyParam (tv, skel), _ | _, Type.TyParam (tv, skel) ->
      let ty = fresh_ty_with_skel skel in
      let sub1 = Substitution.add_type_substitution_e tv ty in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (Constraint.return_resolved paused (cons :: rest_queue))
      in
      ( Substitution.add_type_substitution tv ty sub,
        Constraint.empty_resolved,
        cons_subbed )
  | _, _ -> assert false

and dirt_omega_step sub paused rest_queue omega dcons =
  match dcons with
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = s1; row = ParamRow v1 },
      { effect_set = s2; row = ParamRow v2 } ) ->
      if Type.EffectSet.is_empty s1 then
        (sub, Constraint.resolve_dirt_constraint paused omega dcons, rest_queue)
      else
        let omega' = Type.DirtCoercionParam.fresh () in
        let diff_set = Type.EffectSet.diff s1 s2 in
        let union_set = Type.EffectSet.union s1 s2 in
        let k0 = v2 in
        let v0 =
          let open Type in
          { effect_set = diff_set; row = ParamRow (Type.DirtParam.fresh ()) }
        in
        let omega_ty' =
          ( Type.{ effect_set = Type.EffectSet.empty; row = ParamRow v1 },
            Type.{ effect_set = union_set; row = ParamRow v2 } )
        in
        let k1' = omega in
        let v1' =
          Constraint.unionDirt (s1, Constraint.dirtCoercionVar omega' omega_ty')
        in
        let sub' =
          Substitution.add_dirt_substitution_e k0 v0
          |> Substitution.add_dirt_var_coercion k1' v1'
        in
        let new_cons = Constraint.DirtOmega (omega', omega_ty') in
        ( Substitution.merge sub sub',
          Constraint.empty_resolved,
          Substitution.apply_substitutions_to_constraints sub'
            (Constraint.return_resolved paused rest_queue
            |> Constraint.add_to_constraints new_cons) )
  (* ω : Ø <= Δ₂ *)
  | { effect_set = s1; row = EmptyRow }, d when Type.EffectSet.is_empty s1 ->
      let k = omega in
      let v = Constraint.empty d in
      (Substitution.add_dirt_var_coercion k v sub, paused, rest_queue)
  (* ω : δ₁ <= Ø *)
  | { effect_set = s1; row = ParamRow v1 }, { effect_set = s2; row = EmptyRow }
    when Type.EffectSet.is_empty s1 && Type.EffectSet.is_empty s2 ->
      let k0 = omega in
      let v0 = Constraint.empty Type.empty_dirt in
      let k1' = v1 in
      let v1' = Type.empty_dirt in
      let sub1 =
        Substitution.add_dirt_var_coercion_e k0 v0
        |> Substitution.add_dirt_substitution k1' v1'
      in
      ( Substitution.merge sub sub1,
        Constraint.empty_resolved,
        Substitution.apply_substitutions_to_constraints sub1
          (Constraint.return_resolved paused rest_queue) )
  (* ω : O₁ <= O₂ *)
  | { effect_set = s1; row = EmptyRow }, { effect_set = s2; row = EmptyRow } ->
      assert (Type.EffectSet.subset s1 s2);
      let k = omega in
      let v =
        Constraint.unionDirt
          (s2, Constraint.empty (Type.closed_dirt (Type.EffectSet.diff s2 s1)))
      in
      (Substitution.add_dirt_var_coercion k v sub, paused, rest_queue)
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | { effect_set = s1; row = EmptyRow }, { effect_set = s2; row = ParamRow v2 }
    ->
      let v2' = Type.DirtParam.fresh () in
      let k0 = omega in
      let v0 =
        Constraint.unionDirt
          ( s1,
            Constraint.empty
              Type.{ effect_set = EffectSet.diff s2 s1; row = ParamRow v2' } )
      in
      let k1 = v2 in
      let v1 = Type.{ effect_set = EffectSet.diff s1 s2; row = ParamRow v2' } in
      let sub1 =
        Substitution.add_dirt_var_coercion_e k0 v0
        |> Substitution.add_dirt_substitution k1 v1
      in
      ( Substitution.merge sub sub1,
        Constraint.empty_resolved,
        Substitution.apply_substitutions_to_constraints sub1
          (Constraint.return_resolved paused rest_queue) )
  | _ -> (sub, Constraint.resolve_dirt_constraint paused omega dcons, rest_queue)

let rec unify (sub, paused, queue) =
  (* Print.debug "SUB: %t" (Substitution.print_substitutions sub); *)
  (* Print.debug "PAUSED: %t" (Constraint.print_constraints paused); *)
  (* Print.debug "QUEUE: %t" (Constraint.print_constraints queue); *)
  match queue with
  | [] -> (sub, paused)
  | cons :: rest_queue ->
      let new_state =
        match cons with
        (* τ₁ = τ₂ *)
        | Constraint.SkelEq (sk1, sk2) ->
            skel_eq_step sub paused rest_queue sk1 sk2
        (* ω : A <= B *)
        | Constraint.TyOmega (omega, tycons) ->
            ty_omega_step sub paused cons rest_queue omega tycons
        (* ω : Δ₁ <= Δ₂ *)
        | Constraint.DirtOmega (omega, dcons) ->
            dirt_omega_step sub paused rest_queue omega dcons
      in
      unify new_state

let solve constraints =
  (* Print.debug "constraints: %t" (Constraint.print_constraints constraints); *)
  let solved =
    unify (Substitution.empty, Constraint.empty_resolved, constraints)
  in
  (* Print.debug "sub: %t" (Substitution.print_substitutions sub); *)
  (* Print.debug "solved: %t" (Constraint.print_constraints solved); *)
  solved
