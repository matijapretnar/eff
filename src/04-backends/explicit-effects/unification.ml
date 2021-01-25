open Utils
open Type
open Constraint

let rec get_skel_of_tyvar tyvar clist = get_skel_of_tyvar_ tyvar clist

and get_skel_of_tyvar_ tyvar clist =
  match clist with
  | [] -> failwith __LOC__
  | TyParamHasSkel (tv, skel) :: _ when tyvar = tv -> skel
  | _ :: xs -> get_skel_of_tyvar_ tyvar xs

let rec skeleton_of_target_ty tty =
  match tty with
  | TyParam (_, skel) -> skel
  | Arrow (a1, (a2, _)) ->
      SkelArrow (skeleton_of_target_ty a1, skeleton_of_target_ty a2)
  | Apply (ty_name, tys) ->
      SkelApply (ty_name, List.map (fun ty -> skeleton_of_target_ty ty) tys)
  | Tuple tup -> SkelTuple (List.map (fun ty -> skeleton_of_target_ty ty) tup)
  | Handler ((a1, _), (a2, _)) ->
      SkelHandler (skeleton_of_target_ty a1, skeleton_of_target_ty a2)
  | TyBasic pt -> SkelBasic pt
  | QualTy (_, ty) -> skeleton_of_target_ty ty
  | QualDirt (_, ty) -> skeleton_of_target_ty ty

let rec fix_union_find fixpoint c_list =
  let mapper x =
    match x with
    | Constraint.TyOmega (_, tycons) -> (
        match tycons with
        (* WHAT HAPPENS WITH SKELETONS? *)
        | Type.TyParam (a, _), Type.TyParam (b, _)
          when List.mem a fixpoint && not (List.mem b fixpoint) ->
            [ b ]
        | Type.TyParam (b, _), Type.TyParam (a, _)
          when List.mem a fixpoint && not (List.mem b fixpoint) ->
            [ b ]
        | _ -> [])
    | _ -> []
  in
  let new_fixpoint = fixpoint @ List.concat_map mapper c_list in
  let sort_new_fixpoint = List.sort compare new_fixpoint in
  if sort_new_fixpoint = fixpoint then sort_new_fixpoint
  else fix_union_find sort_new_fixpoint c_list

let process_skeleton_parameter_equality sub paused rest_queue sp1 sk2a =
  let k = sp1 in
  let v = sk2a in
  let sub1 = Substitution.add_skel_param_substitution_e k v in
  let cons_subbed =
    Substitution.apply_substitutions_to_constraints sub1
      (add_list_to_constraints paused rest_queue)
  in
  (Substitution.add_skel_param_substitution k v sub, [], cons_subbed)

let ty_param_has_skel_step sub paused cons rest_queue tvar skel =
  match skel with
  (* α : ς *)
  | SkelParam _ -> (sub, Constraint.add_to_constraints cons paused, rest_queue)
  (* α : int *)
  | SkelBasic ps ->
      let k = tvar in
      let v = Type.TyBasic ps in
      let sub1 = Substitution.add_type_substitution_e k v in
      ( Substitution.add_type_substitution tvar (Type.TyBasic ps) sub,
        [],
        Substitution.apply_substitutions_to_constraints sub1
          (Constraint.add_list_to_constraints paused rest_queue) )
  (* α : τ₁ -> τ₂ *)
  | SkelArrow (sk1, sk2) ->
      let tvar1, cons1 = Constraint.fresh_ty_with_skel sk1
      and tvar2, cons2 = Constraint.fresh_ty_with_skel sk2
      and dvar1 = Type.fresh_dirt () in
      let k = tvar in
      let v = Type.Arrow (tvar1, (tvar2, dvar1)) in
      let sub1 = Substitution.add_type_substitution_e k v in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (Constraint.add_list_to_constraints paused rest_queue)
      in
      ( Substitution.add_type_substitution k v sub,
        [],
        Constraint.add_to_constraints cons1 cons_subbed
        |> Constraint.add_to_constraints cons2 )
  (* α : τ₁ x τ₂ ... *)
  | SkelTuple sks ->
      let tvars, conss =
        List.fold_right
          (fun sk (tvars, conss) ->
            let tvar, cons = Constraint.fresh_ty_with_skel sk in
            (tvar :: tvars, cons :: conss))
          sks ([], [])
      in
      let k = tvar in
      let v = Type.Tuple tvars in
      let sub1 = Substitution.add_type_substitution_e k v in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (add_list_to_constraints paused rest_queue)
      in
      ( Substitution.add_type_substitution k v sub,
        [],
        add_list_to_constraints cons_subbed conss )
  (* α : ty_name (τ₁, τ₂, ...) *)
  | SkelApply (ty_name, sks) ->
      let tvars, conss =
        List.fold_right
          (fun sk (tvars, conss) ->
            let tvar, cons = Constraint.fresh_ty_with_skel sk in
            (tvar :: tvars, cons :: conss))
          sks ([], [])
      in
      let k = tvar in
      let v = Type.Apply (ty_name, tvars) in
      let sub1 = Substitution.add_type_substitution_e k v in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (add_list_to_constraints paused rest_queue)
      in
      ( Substitution.add_type_substitution k v sub,
        [],
        add_list_to_constraints cons_subbed conss )
  (* α : τ₁ => τ₂ *)
  | SkelHandler (sk1, sk2) ->
      let tvar1, cons1 = Constraint.fresh_ty_with_skel sk1
      and tvar2, cons2 = Constraint.fresh_ty_with_skel sk2
      and dvar1 = Type.fresh_dirt ()
      and dvar2 = Type.fresh_dirt () in
      let k = tvar in
      let v = Type.Handler ((tvar1, dvar1), (tvar2, dvar2)) in
      let sub1 = Substitution.add_type_substitution_e k v in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (Constraint.add_list_to_constraints paused rest_queue)
      in
      ( Substitution.add_type_substitution k v sub,
        [],
        Constraint.add_to_constraints cons1 cons_subbed
        |> Constraint.add_to_constraints cons2 )

and skel_eq_step sub paused rest_queue sk1 sk2 =
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
        add_list_to_constraints
          [ Constraint.SkelEq (ska, skc); Constraint.SkelEq (skb, skd) ]
          rest_queue )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | SkelHandler (ska, skb), SkelHandler (skc, skd) ->
      ( sub,
        paused,
        add_list_to_constraints
          [ Constraint.SkelEq (ska, skc); Constraint.SkelEq (skb, skd) ]
          rest_queue )
  | SkelApply (ty_name1, sks1), SkelApply (ty_name2, sks2)
    when ty_name1 = ty_name2 && List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        add_list_to_constraints
          (List.map2 (fun sk1 sk2 -> Constraint.SkelEq (sk1, sk2)) sks1 sks2)
          rest_queue )
  | _ -> failwith __LOC__

and ty_omega_step sub paused cons rest_queue omega = function
  (* ω : A <= A *)
  | x, y when Type.types_are_equal x y ->
      let k = omega in
      let v = Constraint.ReflTy x in
      (Substitution.add_type_coercion k v sub, paused, rest_queue)
  (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
  | Type.Arrow (a1, dirty1), Type.Arrow (a2, dirty2) ->
      let new_ty_coercion_var_coer, ty_cons = fresh_ty_coer (a2, a1)
      and dirty_coercion_c, dirty_cons1, dirty_cons2 =
        fresh_dirty_coer (dirty1, dirty2)
      in
      let k = omega in
      let v =
        Constraint.ArrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c)
      in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_to_constraints ty_cons rest_queue
        |> add_to_constraints dirty_cons1
        |> add_to_constraints dirty_cons2 )
  (* ω : A₁ x A₂ x ... <= B₁ x B₂ x ...  *)
  | Type.Tuple tys, Type.Tuple tys' when List.length tys = List.length tys' ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = fresh_ty_coer (ty, ty') in
            (coercion :: coercions, ty_cons :: conss))
          tys tys' ([], [])
      in
      let k = omega in
      let v = Constraint.TupleCoercion coercions in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_list_to_constraints conss rest_queue )
  (* ω : ty (A₁,  A₂,  ...) <= ty (B₁,  B₂,  ...) *)
  (* we assume that all type parameters are positive *)
  | Type.Apply (ty_name1, tys1), Type.Apply (ty_name2, tys2)
    when ty_name1 = ty_name2 && List.length tys1 = List.length tys2 ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = fresh_ty_coer (ty, ty') in
            (coercion :: coercions, ty_cons :: conss))
          tys1 tys2 ([], [])
      in
      let k = omega in
      let v = Constraint.ApplyCoercion (ty_name1, coercions) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_list_to_constraints conss rest_queue )
  (* ω : D₁ => C₁ <= D₂ => C₂ *)
  | Type.Handler (drty11, drty12), Type.Handler (drty21, drty22) ->
      let drty_coer1, ty_cons1, drt_cons1 = fresh_dirty_coer (drty21, drty11)
      and drty_coer2, ty_cons2, drt_cons2 = fresh_dirty_coer (drty12, drty22) in
      let k = omega in
      let v = Constraint.HandlerCoercion (drty_coer1, drty_coer2) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_to_constraints ty_cons1 rest_queue
        |> add_to_constraints ty_cons2
        |> add_to_constraints drt_cons1
        |> add_to_constraints drt_cons2 )
  (* ω : α <= A /  ω : A <= α *)
  | Type.TyParam (_, skel_tv), a | a, Type.TyParam (_, skel_tv) ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      let skel_a = skeleton_of_target_ty a in
      if skel_tv = skel_a then (sub, cons :: paused, rest_queue)
      else
        ( sub,
          add_to_constraints cons paused,
          add_to_constraints (SkelEq (skel_tv, skel_a)) rest_queue )
  | a, b -> assert false

and dirt_omega_step sub paused cons rest_queue omega dcons =
  match dcons with
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = s1; row = ParamRow v1 },
      { effect_set = s2; row = ParamRow v2 } ) ->
      if Type.EffectSet.is_empty s1 then (sub, cons :: paused, rest_queue)
      else
        let omega' = Type.DirtCoercionParam.fresh () in
        let diff_set = Type.EffectSet.diff s1 s2 in
        let union_set = Type.EffectSet.union s1 s2 in
        let k0 = v2 in
        let v0 =
          let open Type in
          { effect_set = diff_set; row = ParamRow (Type.DirtParam.fresh ()) }
        in
        let k1' = omega in
        let v1' = Constraint.UnionDirt (s1, DirtCoercionVar omega') in
        let sub' =
          Substitution.add_dirt_substitution_e k0 v0
          |> Substitution.add_dirt_var_coercion k1' v1'
        in
        let new_cons =
          Constraint.DirtOmega
            ( omega',
              ( Type.{ effect_set = Type.EffectSet.empty; row = ParamRow v1 },
                Type.{ effect_set = union_set; row = ParamRow v2 } ) )
        in
        ( Substitution.merge sub sub',
          [],
          Substitution.apply_substitutions_to_constraints sub'
            (add_list_to_constraints paused rest_queue
            |> add_to_constraints new_cons) )
  (* ω : Ø <= Δ₂ *)
  | { effect_set = s1; row = EmptyRow }, d when Type.EffectSet.is_empty s1 ->
      let k = omega in
      let v = Constraint.Empty d in
      (Substitution.add_dirt_var_coercion k v sub, paused, rest_queue)
  (* ω : δ₁ <= Ø *)
  | { effect_set = s1; row = ParamRow v1 }, { effect_set = s2; row = EmptyRow }
    when Type.EffectSet.is_empty s1 && Type.EffectSet.is_empty s2 ->
      let k0 = omega in
      let v0 = Constraint.Empty Type.empty_dirt in
      let k1' = v1 in
      let v1' = Type.empty_dirt in
      let sub1 =
        Substitution.add_dirt_var_coercion_e k0 v0
        |> Substitution.add_dirt_substitution k1' v1'
      in
      ( Substitution.merge sub sub1,
        [],
        Substitution.apply_substitutions_to_constraints sub1
          (add_list_to_constraints paused rest_queue) )
  (* ω : O₁ <= O₂ *)
  | { effect_set = s1; row = EmptyRow }, { effect_set = s2; row = EmptyRow } ->
      assert (Type.EffectSet.subset s1 s2);
      let k = omega in
      let v =
        Constraint.UnionDirt
          (s2, Constraint.Empty (Type.closed_dirt (Type.EffectSet.diff s2 s1)))
      in
      (Substitution.add_dirt_var_coercion k v sub, paused, rest_queue)
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | { effect_set = s1; row = EmptyRow }, { effect_set = s2; row = ParamRow v2 }
    ->
      let v2' = Type.DirtParam.fresh () in
      let k0 = omega in
      let v0 =
        Constraint.UnionDirt
          ( s1,
            Constraint.Empty
              Type.{ effect_set = EffectSet.diff s2 s1; row = ParamRow v2' } )
      in
      let k1 = v2 in
      let v1 = Type.{ effect_set = EffectSet.diff s1 s2; row = ParamRow v2' } in
      let sub1 =
        Substitution.add_dirt_var_coercion_e k0 v0
        |> Substitution.add_dirt_substitution k1 v1
      in
      ( Substitution.merge sub sub1,
        [],
        Substitution.apply_substitutions_to_constraints sub1
          (add_list_to_constraints paused rest_queue) )
  | _ -> (sub, cons :: paused, rest_queue)

let rec unify (sub, paused, queue) =
  match queue with
  | [] -> (sub, paused)
  | cons :: rest_queue ->
      let new_state =
        match cons with
        (* α : τ *)
        | Constraint.TyParamHasSkel (tvar, skel) ->
            ty_param_has_skel_step sub paused cons rest_queue tvar skel
        (* τ₁ = τ₂ *)
        | Constraint.SkelEq (sk1, sk2) ->
            skel_eq_step sub paused rest_queue sk1 sk2
        (* ω : A <= B *)
        | Constraint.TyOmega (omega, tycons) ->
            ty_omega_step sub paused cons rest_queue omega tycons
        (* ω : Δ₁ <= Δ₂ *)
        | Constraint.DirtOmega (omega, dcons) ->
            dirt_omega_step sub paused cons rest_queue omega dcons
      in
      unify new_state

let solve constraints = unify (Substitution.empty, [], constraints)
