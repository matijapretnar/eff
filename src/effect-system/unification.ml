open CoreUtils
open Types
open Typed
module STyParams = Set.Make (CoreTypes.TyParam)

let set_of_list =
  List.fold_left (fun acc x -> STyParams.add x acc) STyParams.empty

let rec print_c_list = function
  | [] -> Print.debug "---------------------"
  | e :: l ->
      Print.debug "%t" (Typed.print_omega_ct e);
      print_c_list l

let rec print_var_list = function
  | [] -> Print.debug "---------------------"
  | e :: l ->
      Print.debug "%t" (CoreTypes.TyParam.print e);
      print_var_list l

let rec get_skel_of_tyvar tyvar clist =
  Print.debug "getting skeleton of tyvar from list";
  Print.debug " TyParam : %t" (CoreTypes.TyParam.print tyvar);
  Print.debug "Constraint list :";
  print_c_list clist;
  get_skel_of_tyvar_ tyvar clist

and get_skel_of_tyvar_ tyvar clist =
  match clist with
  | [] -> assert false
  | TyParamHasSkel (tv, skel) :: _ when tyvar = tv -> skel
  | _ :: xs -> get_skel_of_tyvar_ tyvar xs

let rec skeleton_of_target_ty tty conslist =
  match tty with
  | TyParam x -> get_skel_of_tyvar x conslist
  | Arrow (a1, (a2, _)) ->
      SkelArrow
        (skeleton_of_target_ty a1 conslist, skeleton_of_target_ty a2 conslist)
  | Apply (ty_name, tys) ->
      SkelApply
        (ty_name, List.map (fun ty -> skeleton_of_target_ty ty conslist) tys)
  | Tuple tup ->
      SkelTuple (List.map (fun ty -> skeleton_of_target_ty ty conslist) tup)
  | Handler ((a1, _), (a2, _)) ->
      SkelHandler
        (skeleton_of_target_ty a1 conslist, skeleton_of_target_ty a2 conslist)
  | PrimTy pt -> PrimSkel pt
  | Tuple t ->
      SkelTuple (List.map (fun ty -> skeleton_of_target_ty ty conslist) t)

let rec fix_union_find fixpoint c_list =
  Print.debug "--------------start list-------";
  print_var_list fixpoint;
  Print.debug "---------------end list-------";
  let mapper x =
    match x with
    | Typed.TyOmega (_, tycons) -> (
        match tycons with
        | Types.TyParam a, Types.TyParam b
          when List.mem a fixpoint && not (List.mem b fixpoint) ->
            [ b ]
        | Types.TyParam b, Types.TyParam a
          when List.mem a fixpoint && not (List.mem b fixpoint) ->
            [ b ]
        | _ -> [])
    | _ -> []
  in
  let new_fixpoint = fixpoint @ concat_map mapper c_list in
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
  | SkelParam p -> (sub, Typed.add_to_constraints cons paused, rest_queue)
  (* α : int *)
  | PrimSkel ps ->
      let k = tvar in
      let v = Types.PrimTy ps in
      let sub1 = Substitution.add_type_substitution_e k v in
      ( Substitution.add_type_substitution tvar (Types.PrimTy ps) sub,
        [],
        Substitution.apply_substitutions_to_constraints sub1
          (Typed.add_list_to_constraints paused rest_queue) )
  (* α : τ₁ -> τ₂ *)
  | SkelArrow (sk1, sk2) ->
      let tvar1, cons1 = Typed.fresh_ty_with_skel sk1
      and tvar2, cons2 = Typed.fresh_ty_with_skel sk2
      and dvar1 = Types.fresh_dirt () in
      let k = tvar in
      let v = Types.Arrow (tvar1, (tvar2, dvar1)) in
      let sub1 = Substitution.add_type_substitution_e k v in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (Typed.add_list_to_constraints paused rest_queue)
      in
      ( Substitution.add_type_substitution k v sub,
        [],
        Typed.add_to_constraints cons1 cons_subbed
        |> Typed.add_to_constraints cons2 )
  (* α : τ₁ x τ₂ ... *)
  | SkelTuple sks ->
      let tvars, conss =
        List.fold_right
          (fun sk (tvars, conss) ->
            let tvar, cons = Typed.fresh_ty_with_skel sk in
            (tvar :: tvars, cons :: conss))
          sks ([], [])
      in
      let k = tvar in
      let v = Types.Tuple tvars in
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
            let tvar, cons = Typed.fresh_ty_with_skel sk in
            (tvar :: tvars, cons :: conss))
          sks ([], [])
      in
      let k = tvar in
      let v = Types.Apply (ty_name, tvars) in
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
      let tvar1, cons1 = Typed.fresh_ty_with_skel sk1
      and tvar2, cons2 = Typed.fresh_ty_with_skel sk2
      and dvar1 = Types.fresh_dirt ()
      and dvar2 = Types.fresh_dirt () in
      let k = tvar in
      let v = Types.Handler ((tvar1, dvar1), (tvar2, dvar2)) in
      let sub1 = Substitution.add_type_substitution_e k v in
      let cons_subbed =
        Substitution.apply_substitutions_to_constraints sub1
          (Typed.add_list_to_constraints paused rest_queue)
      in
      ( Substitution.add_type_substitution k v sub,
        [],
        Typed.add_to_constraints cons1 cons_subbed
        |> Typed.add_to_constraints cons2 )
  | ForallSkel (p, sk1) -> failwith __LOC__

and skel_eq_step sub paused cons rest_queue sk1 sk2 =
  match (sk1, sk2) with
  | s1, s2 when s1 = s2 -> (sub, paused, rest_queue)
  (* ς = ς *)
  | SkelParam sp1, SkelParam sp2 when sp1 = sp2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | SkelParam sp1, sk2a when not (List.mem sp1 (free_skeleton sk2a)) ->
      process_skeleton_parameter_equality sub paused rest_queue sp1 sk2a
  | sk2a, SkelParam sp1 when not (List.mem sp1 (free_skeleton sk2a)) ->
      process_skeleton_parameter_equality sub paused rest_queue sp1 sk2a
  (* int = int *)
  | PrimSkel ps1, PrimSkel ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | SkelArrow (ska, skb), SkelArrow (skc, skd) ->
      ( sub,
        paused,
        add_list_to_constraints
          [ Typed.SkelEq (ska, skc); Typed.SkelEq (skb, skd) ]
          rest_queue )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | SkelHandler (ska, skb), SkelHandler (skc, skd) ->
      ( sub,
        paused,
        add_list_to_constraints
          [ Typed.SkelEq (ska, skc); Typed.SkelEq (skb, skd) ]
          rest_queue )
  | SkelApply (ty_name1, sks1), SkelApply (ty_name2, sks2)
    when ty_name1 = ty_name2 && List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        add_list_to_constraints
          (List.map2 (fun sk1 sk2 -> Typed.SkelEq (sk1, sk2)) sks1 sks2)
          rest_queue )
  | SkelTuple t1, SkelTuple t2 ->
      let new_constraints =
        List.map (fun (s1, s2) -> Typed.SkelEq (s1, s2)) (List.combine t1 t2)
      in
      (sub, paused, add_list_to_constraints new_constraints rest_queue)
  | SkelTuple _, _ | _, SkelTuple _ -> failwith "Invalid constraint"
  | _ ->
      Print.debug "%t" (Types.print_skeleton sk1);
      Print.debug "%t" (Types.print_skeleton sk2);
      failwith __LOC__

and ty_omega_step sub paused cons rest_queue omega = function
  (* ω : A <= A *)
  | x, y when Types.types_are_equal x y ->
      let k = omega in
      let v = Typed.ReflTy x in
      (Substitution.add_type_coercion k v sub, paused, rest_queue)
  (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
  | Types.Arrow (a1, dirty1), Types.Arrow (a2, dirty2) ->
      let new_ty_coercion_var_coer, ty_cons = fresh_ty_coer (a2, a1)
      and dirty_coercion_c, dirty_cons = fresh_dirty_coer (dirty1, dirty2) in
      let k = omega in
      let v =
        Typed.ArrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c)
      in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_to_constraints ty_cons rest_queue |> add_to_constraints dirty_cons
      )
  (* ω : A₁ x A₂ x ... <= B₁ x B₂ x ...  *)
  | Types.Tuple tys, Types.Tuple tys' when List.length tys = List.length tys' ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = fresh_ty_coer (ty, ty') in
            (coercion :: coercions, ty_cons :: conss))
          tys tys' ([], [])
      in
      let k = omega in
      let v = Typed.TupleCoercion coercions in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_list_to_constraints conss rest_queue )
  (* ω : ty (A₁,  A₂,  ...) <= ty (B₁,  B₂,  ...) *)
  (* we assume that all type parameters are positive *)
  | Types.Apply (ty_name1, tys1), Types.Apply (ty_name2, tys2)
    when ty_name1 = ty_name2 && List.length tys1 = List.length tys2 ->
      let coercions, conss =
        List.fold_right2
          (fun ty ty' (coercions, conss) ->
            let coercion, ty_cons = fresh_ty_coer (ty, ty') in
            (coercion :: coercions, ty_cons :: conss))
          tys1 tys2 ([], [])
      in
      let k = omega in
      let v = Typed.ApplyCoercion (ty_name1, coercions) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_list_to_constraints conss rest_queue )
  (* ω : D₁ => C₁ <= D₂ => C₂ *)
  | Types.Handler (drty11, drty12), Types.Handler (drty21, drty22) ->
      let drty_coer1, drty_cons1 = fresh_dirty_coer (drty21, drty11)
      and drty_coer2, drty_cons2 = fresh_dirty_coer (drty12, drty22) in
      let k = omega in
      let v = Typed.HandlerCoercion (drty_coer1, drty_coer2) in
      ( Substitution.add_type_coercion k v sub,
        paused,
        add_to_constraints drty_cons1 rest_queue
        |> add_to_constraints drty_cons2 )
  (* ω : α <= A /  ω : A <= α *)
  | Types.TyParam tv, a | a, Types.TyParam tv ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      let skel_tv = get_skel_of_tyvar tv (paused @ rest_queue) in
      let skel_a = skeleton_of_target_ty a (paused @ rest_queue) in
      if skel_tv = skel_a then (sub, cons :: paused, rest_queue)
      else
        ( sub,
          add_to_constraints cons paused,
          add_to_constraints (SkelEq (skel_tv, skel_a)) rest_queue )
  | a, b ->
      Print.debug "can't solve subtyping for types: %t and %t"
        (print_target_ty a) (print_target_ty b);
      assert false

and dirt_omega_step sub paused cons rest_queue omega dcons =
  match dcons with
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = s1; row = ParamRow v1 },
      { effect_set = s2; row = ParamRow v2 } ) ->
      if Types.EffectSet.is_empty s1 then (sub, cons :: paused, rest_queue)
      else
        let omega' = CoreTypes.DirtCoercionParam.fresh () in
        let diff_set = Types.EffectSet.diff s1 s2 in
        let union_set = Types.EffectSet.union s1 s2 in
        let k0 = v2 in
        let v0 =
          let open Types in
          {
            effect_set = diff_set;
            row = ParamRow (CoreTypes.DirtParam.fresh ());
          }
        in
        let k1' = omega in
        let v1' = Typed.UnionDirt (s1, DirtCoercionVar omega') in
        let sub' =
          Substitution.add_dirt_substitution_e k0 v0
          |> Substitution.add_dirt_var_coercion k1' v1'
        in
        let new_cons =
          Typed.DirtOmega
            ( omega',
              ( Types.{ effect_set = Types.EffectSet.empty; row = ParamRow v1 },
                Types.{ effect_set = union_set; row = ParamRow v2 } ) )
        in
        ( Substitution.merge sub sub',
          [],
          Substitution.apply_substitutions_to_constraints sub'
            (add_list_to_constraints paused rest_queue
            |> add_to_constraints new_cons) )
  (* ω : Ø <= Δ₂ *)
  | { effect_set = s1; row = EmptyRow }, d when Types.EffectSet.is_empty s1 ->
      let k = omega in
      let v = Typed.Empty d in
      (Substitution.add_dirt_var_coercion k v sub, paused, rest_queue)
  (* ω : δ₁ <= Ø *)
  | { effect_set = s1; row = ParamRow v1 }, { effect_set = s2; row = EmptyRow }
    when Types.EffectSet.is_empty s1 && Types.EffectSet.is_empty s2 ->
      let k0 = omega in
      let v0 = Typed.Empty Types.empty_dirt in
      let k1' = v1 in
      let v1' = Types.empty_dirt in
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
      assert (Types.EffectSet.subset s1 s2);
      let k = omega in
      let v =
        Typed.UnionDirt
          (s2, Typed.Empty (Types.closed_dirt (Types.EffectSet.diff s2 s1)))
      in
      (Substitution.add_dirt_var_coercion k v sub, paused, rest_queue)
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | { effect_set = s1; row = EmptyRow }, { effect_set = s2; row = ParamRow v2 }
    ->
      let v2' = CoreTypes.DirtParam.fresh () in
      let k0 = omega in
      let v0 =
        Typed.UnionDirt
          ( s1,
            Typed.Empty
              Types.{ effect_set = EffectSet.diff s2 s1; row = ParamRow v2' } )
      in
      let k1 = v2 in
      let v1 =
        Types.{ effect_set = EffectSet.diff s1 s2; row = ParamRow v2' }
      in
      let sub1 =
        Substitution.add_dirt_var_coercion_e k0 v0
        |> Substitution.add_dirt_substitution k1 v1
      in
      ( Substitution.merge sub sub1,
        [],
        Substitution.apply_substitutions_to_constraints sub1
          (add_list_to_constraints paused rest_queue) )
  | _ -> (sub, cons :: paused, rest_queue)

let dirty_omega_step sub paused cons rest_queue (omega1, omega2) drtycons =
  let (ty1, drt1), (ty2, drt2) = drtycons in
  let ty_cons = TyOmega (omega1, (ty1, ty2))
  and dirt_cons = DirtOmega (omega2, (drt1, drt2)) in
  let sub', paused', rest_queue' =
    ty_omega_step sub paused ty_cons rest_queue omega1 (ty1, ty2)
  in
  dirt_omega_step sub' paused' dirt_cons rest_queue' omega2 (drt1, drt2)

let rec unify (sub, paused, queue) =
  Print.debug "=============Start loop============";
  Print.debug "-----Subs-----";
  Substitution.print_substitutions sub;
  Print.debug "-----paused-----";
  print_c_list paused;
  Print.debug "-----queue-----";
  print_c_list queue;
  match queue with
  | [] ->
      Print.debug "=============FINAL LOOP Result============";
      (sub, paused)
  | cons :: rest_queue ->
      let new_state =
        match cons with
        (* α : τ *)
        | Typed.TyParamHasSkel (tvar, skel) ->
            ty_param_has_skel_step sub paused cons rest_queue tvar skel
        (* τ₁ = τ₂ *)
        | Typed.SkelEq (sk1, sk2) ->
            skel_eq_step sub paused cons rest_queue sk1 sk2
        (* ω : A <= B *)
        | Typed.TyOmega (omega, tycons) ->
            ty_omega_step sub paused cons rest_queue omega tycons
        (* ω : Δ₁ <= Δ₂ *)
        | Typed.DirtOmega (omega, dcons) ->
            dirt_omega_step sub paused cons rest_queue omega dcons
        (* ω : A ! Δ₁ <= B ! Δ₂ *)
        | Typed.DirtyOmega (omega, drtycons) ->
            dirty_omega_step sub paused cons rest_queue omega drtycons
      in
      Print.debug "=========End loop============";
      unify new_state
