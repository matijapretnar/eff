open Utils
open Language
open Type

let apply_substitution new_sub sub (paused : Constraints.t) queue =
  let substitute_ty_constraint s t1 t2 w ty1 ty2 (paused, queue) =
    let ty1', ty2' =
      ( Substitution.apply_substitutions_to_type new_sub ty1,
        Substitution.apply_substitutions_to_type new_sub ty2 )
    in
    if Type.equal_ty ty1 ty1' && Type.equal_ty ty2 ty2' then
      (Constraints.add_ty_constraint s t1 t2 w paused, queue)
    else (paused, Constraint.add_ty_inequality (w, (ty1', ty2')) queue)
  and substitute_dirt_constraint d1 d2 w effs drt1 drt2 (paused, queue) =
    let drt1', drt2' =
      ( Substitution.apply_substitutions_to_dirt new_sub drt1,
        Substitution.apply_substitutions_to_dirt new_sub drt2 )
    in
    if Type.equal_dirt drt1 drt1' && Type.equal_dirt drt2 drt2' then
      (Constraints.add_dirt_constraint d1 d2 w effs paused, queue)
    else (paused, Constraint.add_dirt_inequality (w, (drt1', drt2')) queue)
  in
  let sub' = Substitution.merge new_sub sub in
  let paused', queue' =
    (Constraints.empty, Constraint.apply_sub new_sub queue)
    |> Constraints.TyConstraints.fold_expanded substitute_ty_constraint
         paused.ty_constraints
    |> Constraints.DirtConstraints.fold_expanded substitute_dirt_constraint
         paused.dirt_constraints
  in
  (sub', paused', queue')

let expand_row ~loc row ops =
  match row with
  | _ when Effect.Set.is_empty ops -> (Substitution.empty, row)
  | Dirt.Row.Param p ->
      let p' = Dirt.Param.refresh p in
      let row' = Dirt.Row.Param p' in
      let sub' =
        Substitution.add_dirt_substitution_e p { effect_set = ops; row = row' }
      in
      (sub', row')
  | Dirt.Row.Empty -> Error.typing ~loc "Cannot extend an empty row."

let skel_eq_step ~loc sub (paused : Constraints.t) rest_queue sk1 sk2 =
  match (sk1, sk2) with
  (* ς = ς *)
  | Skeleton.Param sp1, Skeleton.Param sp2 when sp1 = sp2 ->
      (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | Param sp1, sk2a
    when not
           (Skeleton.Param.Set.mem sp1 (free_params_skeleton sk2a).skel_params)
    ->
      apply_substitution
        (Substitution.add_skel_param_substitution_e sp1 sk2a)
        sub paused rest_queue
  | sk2a, Param sp1
    when not
           (Skeleton.Param.Set.mem sp1 (free_params_skeleton sk2a).skel_params)
    ->
      apply_substitution
        (Substitution.add_skel_param_substitution_e sp1 sk2a)
        sub paused rest_queue
      (* occurs-check failing *)
  | Param _, _ | _, Param _ ->
      let printer = Type.print_pretty Skeleton.Param.Set.empty in
      Error.typing ~loc "This expression has a forbidden cyclic type %t = %t."
        (printer sk1) (printer sk2)
      (* int = int *)
  | Basic ps1, Basic ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | Arrow (ska, skb), Arrow (skc, skd) ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_skeleton_equality (ska, skc)
        |> Constraint.add_skeleton_equality (skb, skd) )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | Handler (ska, skb), Handler (skc, skd) ->
      ( sub,
        paused,
        rest_queue
        |> Constraint.add_skeleton_equality (ska, skc)
        |> Constraint.add_skeleton_equality (skb, skd) )
  | ( Apply { ty_name = ty_name1; skel_args = sks1 },
      Apply { ty_name = ty_name2; skel_args = sks2 } )
    when ty_name1 = ty_name2
         && TyParam.Map.cardinal sks1 = TyParam.Map.cardinal sks2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun sk1 sk2 -> Constraint.add_skeleton_equality (sk1, sk2))
          (sks1 |> TyParam.Map.values)
          (sks2 |> TyParam.Map.values)
          rest_queue )
  | Tuple sks1, Tuple sks2 when List.length sks1 = List.length sks2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun sk1 sk2 -> Constraint.add_skeleton_equality (sk1, sk2))
          sks1 sks2 rest_queue )
  | _ ->
      let printer = Type.print_pretty Skeleton.Param.Set.empty in
      Error.typing ~loc
        "This expression has type %t but it should have type %t." (printer sk1)
        (printer sk2)

and ty_eq_step sub (paused : Constraints.t) rest_queue (ty1 : Type.ty)
    (ty2 : Type.ty) =
  match (ty1.term, ty2.term) with
  (* ς = ς *)
  | TyParam p1, TyParam p2 when p1 = p2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  (* There is no need for occurs-check because skeletons of both sides are equal *)
  | TyParam p1, _ ->
      let sub1 = Substitution.add_type_substitution_e p1 ty2 in
      apply_substitution sub1 sub paused rest_queue
  | _, TyParam p2 ->
      let sub1 = Substitution.add_type_substitution_e p2 ty1 in
      apply_substitution sub1 sub paused rest_queue
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
    when ty_name1 = ty_name2
         && TyParam.Map.cardinal tys1 = TyParam.Map.cardinal tys2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun (ty1, _) (ty2, _) -> Constraint.add_ty_equality (ty1, ty2))
          (tys1 |> TyParam.Map.values)
          (tys2 |> TyParam.Map.values)
          rest_queue )
  | Tuple tys1, Tuple tys2 when List.length tys1 = List.length tys2 ->
      ( sub,
        paused,
        List.fold_right2
          (fun ty1 ty2 -> Constraint.add_ty_equality (ty1, ty2))
          tys1 tys2 rest_queue )
  | _ -> assert false

and ty_omega_step type_definitions sub (paused : Constraints.t) cons rest_queue
    omega = function
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
  | { term = Type.Tuple tys; _ }, { term = Type.Tuple tys'; _ } ->
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
  | ( { term = Type.Apply { ty_name = ty_name1; ty_args = tys1 }; _ },
      { term = Type.Apply { ty_name = ty_name2; ty_args = tys2 }; _ } )
    when ty_name1 = ty_name2
         && TyParam.Map.cardinal tys1 = TyParam.Map.cardinal tys2 ->
      let coercions, cons =
        List.fold_right2
          (fun (p1, (ty, v1)) (p2, (ty', v2)) (coercions, conss) ->
            assert (p1 = p2);
            assert (v1 = v2);
            let coercion, ty_cons =
              match v1 with
              | Covariant ->
                  let coercion, ty_cons = Constraint.fresh_ty_coer (ty, ty') in
                  (coercion, ty_cons)
              | Contravariant ->
                  let coercion, ty_cons = Constraint.fresh_ty_coer (ty', ty) in
                  (coercion, ty_cons)
              | Invariant ->
                  ( Coercion.reflTy ty,
                    Constraint.add_ty_equality (ty, ty') Constraint.empty )
            in
            ((p1, (coercion, v1)) :: coercions, Constraint.union ty_cons conss))
          (TyParam.Map.bindings tys1)
          (TyParam.Map.bindings tys2)
          ([], Constraint.empty)
      in
      let v =
        Coercion.applyCoercion (ty_name1, coercions |> TyParam.Map.of_bindings)
      in
      ( Substitution.add_type_coercion omega v sub,
        paused,
        Constraint.union cons rest_queue )
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
  | ( ({ term = Type.TyParam t1; ty = Skeleton.Param s1 } as ty1),
      ({ term = Type.TyParam t2; ty = Skeleton.Param s2 } as ty2) )
    when s1 = s2 -> (
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      let existing =
        paused.ty_constraints
        |> Constraints.TyConstraints.get_ty_graph s1
        |> Constraints.TyConstraints.TyParamGraph.get_edges t1
        |> TyParam.Map.find_opt t2
      in
      match existing with
      | None ->
          (sub, Constraints.add_ty_constraint s1 t1 t2 omega paused, rest_queue)
      | Some w ->
          ( Substitution.add_type_coercion omega
              (Coercion.tyCoercionVar w (ty1, ty2))
              sub,
            paused,
            rest_queue ))
  | { term = Type.TyParam tv; ty = skel }, _
  | _, { term = Type.TyParam tv; ty = skel } ->
      let ty = fresh_ty_with_skel type_definitions skel in
      apply_substitution
        (Substitution.add_type_substitution_e tv ty)
        sub paused
        (Constraint.union cons rest_queue)
  | _ -> assert false

and dirt_omega_step ~loc sub resolved unresolved w dcons =
  match dcons with
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
          ( sub,
            Constraints.add_dirt_constraint d1 d2 w ops2 resolved,
            unresolved )
      | Some (d, _) ->
          ( Substitution.add_dirt_var_coercion w
              { term = Coercion.DirtCoercionVar d; ty = (ty1, ty2) }
              sub,
            resolved,
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
      let sub' =
        Substitution.add_dirt_substitution_e d2
          { effect_set = Effect.Set.diff ops1 ops2; row = Dirt.Row.Param d2' }
        |> Substitution.add_dirt_var_coercion w
             (Coercion.unionDirt (ops1, Coercion.dirtCoercionVar w' w_ty'))
      in
      apply_substitution sub' sub resolved
        (Constraint.add_dirt_inequality (w', w_ty') unresolved)
  (* ω : Ø <= Δ₂ *)
  | { effect_set = ops1; row = Dirt.Row.Empty }, d when Effect.Set.is_empty ops1
    ->
      let sub' = Substitution.add_dirt_var_coercion w (Coercion.empty d) sub in
      (sub', resolved, unresolved)
  (* ω : δ₁ <= Ø *)
  | ( { effect_set = ops1; row = Dirt.Row.Param d1 },
      { effect_set = ops2; row = Dirt.Row.Empty } )
    when Effect.Set.is_empty ops1 && Effect.Set.is_empty ops2 ->
      let sub' =
        Substitution.add_dirt_var_coercion_e w (Coercion.empty Dirt.empty)
        |> Substitution.add_dirt_substitution d1 Dirt.empty
      in
      apply_substitution sub' sub resolved unresolved
  (* ω : O₁ <= O₂ *)
  | ( { effect_set = ops1; row = Dirt.Row.Empty },
      { effect_set = ops2; row = Dirt.Row.Empty } ) ->
      if not (Effect.Set.subset ops1 ops2) then
        Error.typing ~loc "Effects %t are not a subset of %t"
          (Effect.Set.print ops1) (Effect.Set.print ops2);
      let sub' =
        Substitution.add_dirt_var_coercion w
          (Coercion.unionDirt
             (ops2, Coercion.empty (Dirt.closed (Effect.Set.diff ops2 ops1))))
          sub
      in
      (sub', resolved, unresolved)
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | ( { effect_set = ops1; row = Dirt.Row.Empty },
      { effect_set = ops2; row = Dirt.Row.Param d2 } ) ->
      let d2' = Dirt.Param.refresh d2 in
      let sub' =
        Substitution.add_dirt_var_coercion_e w
          (Coercion.unionDirt
             ( ops1,
               Coercion.empty
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
      apply_substitution sub' sub resolved unresolved
  | _ -> assert false

and dirt_eq_step ~loc sub paused rest_queue { Dirt.effect_set = o1; row = row1 }
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
  let sub1, row1' = expand_row ~loc row1 (Effect.Set.diff o2 o1)
  and sub2, row2' = expand_row ~loc row2 (Effect.Set.diff o1 o2) in
  let row_sub =
    match (row1', row2') with
    | Dirt.Row.Empty, Dirt.Row.Empty -> Substitution.empty
    | Dirt.Row.Param p1, _ ->
        Substitution.add_dirt_substitution_e p1
          { effect_set = Effect.Set.empty; row = row2' }
    | _, Dirt.Row.Param p2 ->
        Substitution.add_dirt_substitution_e p2
          { effect_set = Effect.Set.empty; row = row1' }
  in
  let sub' = Substitution.merge (Substitution.merge sub1 sub2) row_sub in
  apply_substitution sub' sub paused rest_queue

let rec unify ~loc type_definitions (sub, paused, (queue : Constraint.t)) =
  Print.debug "SUB: %t" (Substitution.print sub);
  Print.debug "PAUSED: %t" (Constraints.print paused);
  Print.debug "QUEUE: %t" (Constraint.print queue);
  match queue with
  | { skeleton_equalities = (sk1, sk2) :: skeleton_equalities; _ } ->
      skel_eq_step ~loc sub paused { queue with skeleton_equalities } sk1 sk2
      |> unify ~loc type_definitions
  | { dirt_equalities = (drt1, drt2) :: dirt_equalities; _ } ->
      dirt_eq_step ~loc sub paused { queue with dirt_equalities } drt1 drt2
      |> unify ~loc type_definitions
  | { dirt_inequalities = (omega, dcons) :: dirt_inequalities; _ } ->
      dirt_omega_step ~loc sub paused
        { queue with dirt_inequalities }
        omega dcons
      |> unify ~loc type_definitions
  | { ty_equalities = (ty1, ty2) :: _; _ }
    when not (Skeleton.equal ty1.ty ty2.ty) ->
      skel_eq_step ~loc sub paused queue ty1.ty ty2.ty
      |> unify ~loc type_definitions
  | { ty_equalities = (ty1, ty2) :: ty_equalities; _ } ->
      ty_eq_step sub paused { queue with ty_equalities } ty1 ty2
      |> unify ~loc type_definitions
  | { ty_inequalities = (_, (ty1, ty2)) :: _; _ }
    when not (Skeleton.equal ty1.ty ty2.ty) ->
      skel_eq_step ~loc sub paused queue ty1.ty ty2.ty
      |> unify ~loc type_definitions
  | { ty_inequalities = (omega, tycons) :: ty_inequalities; _ } ->
      let cons =
        Constraint.add_ty_inequality (omega, tycons) Constraint.empty
      in
      ty_omega_step type_definitions sub paused cons
        { queue with ty_inequalities }
        omega tycons
      |> unify ~loc type_definitions
  | {
   skeleton_equalities = [];
   dirt_equalities = [];
   dirt_inequalities = [];
   ty_equalities = [];
   ty_inequalities = [];
  } ->
      (sub, paused)

let collapse_cycles { Language.Constraints.ty_constraints; dirt_constraints } =
  let open Language.Constraints in
  (* Remove type cycles *)
  let garbage_collect_skeleton_component skel graph new_constr =
    let pack ty_param = { term = TyParam ty_param; ty = Skeleton.Param skel } in
    let components = TyConstraints.TyParamGraph.scc graph in
    (* For each component: pick one and add equal constraint  *)
    let new_constr' =
      List.fold
        (fun new_constr component ->
          match TyParam.Set.elements component with
          | [] -> assert false
          (* Select the first one as representative *)
          | top :: rest ->
              let new_constr' =
                List.fold
                  (fun new_constr param ->
                    Constraint.add_ty_equality (pack top, pack param) new_constr)
                  new_constr rest
              in
              new_constr')
        new_constr components
    in
    new_constr'
  in
  let ty_constraints =
    Skeleton.Param.Map.fold garbage_collect_skeleton_component ty_constraints
      Constraint.empty
  in
  (* Dirt constraints *)
  let components = DirtConstraints.DirtParamGraph.scc dirt_constraints in
  let ty_constraints =
    List.fold_left
      (fun ty_constraints component ->
        if
          Dirt.Param.Set.cardinal component = 1
          || not (* If the cycle is simple *)
               (Dirt.Param.Set.for_all
                  (fun v ->
                    let edges =
                      DirtConstraints.DirtParamGraph.get_edges v
                        dirt_constraints
                    in
                    Dirt.Param.Set.for_all
                      (fun target ->
                        match
                          DirtConstraints.DirtParamGraph.Edges.get_edge target
                            edges
                        with
                        | None -> true
                        | Some (_, dirts) -> Effect.Set.is_empty dirts)
                      component)
                  component)
        then ty_constraints
        else
          (* Pick one and set all other to equal it *)
          let representative = Dirt.Param.Set.choose component in
          let ty_constraints =
            Dirt.Param.Set.fold
              (fun v acc ->
                if v <> representative then
                  Constraint.add_dirt_equality
                    (Dirt.no_effect v, Dirt.no_effect representative)
                    acc
                else acc)
              component ty_constraints
          in
          ty_constraints)
      ty_constraints components
  in
  ty_constraints

let join_simple_nodes { Language.Constraints.ty_constraints; _ } =
  let open Language.Constraints in
  let module G = TyConstraints.TyParamGraph in
  let join_component skel graph new_constr =
    let pack ty_param = { term = TyParam ty_param; ty = Skeleton.Param skel } in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in
    let increment v m =
      TyParam.Map.update v
        (function None -> Some 1 | Some x -> Some (x + 1))
        m
    in
    let indeg, outdeg =
      G.fold
        (fun source sink _edge (indeg, outdeg) ->
          (increment sink indeg, increment source outdeg))
        graph
        (TyParam.Map.empty, TyParam.Map.empty)
    in
    (* Sanity check *)
    let assert_degrees grph line =
      TyParam.Map.iter
        (fun p n ->
          let sz = G.get_edges p grph |> G.Edges.cardinal in
          assert (n = sz))
        line
    in
    assert_degrees inverse_graph indeg;
    assert_degrees graph outdeg;
    (* Find the node with the least indegree *)
    let get_ones (k, n) =
      assert (n <> 0);
      if n = 1 then Some k else None
    in
    let filter line =
      line |> TyParam.Map.bindings |> List.filter_map get_ones
      |> TyParam.Set.of_list
    in
    let indeg_line = filter indeg and outdeg_line = filter outdeg in
    let process_part_general ?(mode = "incoming") target
        (indeg_line, outdeg_line) (base_graph, reverse_graph) constr =
      (* Removing outging/incoming edges with degree 1 is practically the same but on different (reversed) graph
         The naming in this function assumes that the input graph is original graph and we are removing edges with
         exactly 1 incoming edge *)
      Print.debug "In mode %s, removing: %t" mode (TyParam.print target);
      let incoming = G.get_edges target reverse_graph in
      assert (G.Edges.cardinal incoming = 1);
      let source, _edge = G.Vertex.Map.choose incoming in
      let next = G.get_edges target base_graph in
      let base_graph =
        base_graph
        |> G.remove_edge source target (* remove this edge *)
        |> G.Edges.fold (* rewire other edges *)
             (fun next e acc ->
               acc |> G.remove_edge target next
               |> G.add_edge (* Triangels can produce duplicate edges *)
                    ~allow_duplicate:true source next e)
             next
        |> G.remove_vertex_unsafe target
      and reverse_graph =
        reverse_graph
        |> G.remove_edge target source
        |> G.Edges.fold (* rewire other edges *)
             (fun next e acc ->
               acc |> G.remove_edge next target
               |> G.add_edge ~allow_duplicate:true next source e)
             next
        |> G.remove_vertex_unsafe target
      in
      let remove_edges base_graph line =
        line |> TyParam.Set.remove target
        |> G.Edges.fold
             (fun potential _ acc ->
               let num =
                 base_graph |> G.get_edges potential |> G.Edges.cardinal
               in
               if num = 1 then acc |> TyParam.Set.add potential
               else acc |> TyParam.Set.remove potential)
             (next
             |> G.Vertex.Map.map (fun _ -> ())
             (* Treat source as any other *)
             |> G.Edges.add_edge ~allow_duplicate:true source ())
      in
      let indeg_line = remove_edges reverse_graph indeg_line
      and outdeg_line = remove_edges base_graph outdeg_line in
      ( (indeg_line, outdeg_line),
        (base_graph, reverse_graph),
        Constraint.add_ty_equality (pack source, pack target) constr )
    in
    let rec process (indeg_line, outdeg_line) (graph, reverse_graph) constr =
      match TyParam.Set.choose_opt indeg_line with
      | Some v ->
          let (indeg_line, outdeg_line), (graph, reverse_graph), constr =
            process_part_general v (indeg_line, outdeg_line)
              (graph, reverse_graph) constr
          in
          process (indeg_line, outdeg_line) (graph, reverse_graph) constr
      | None -> (
          match TyParam.Set.choose_opt outdeg_line with
          | Some v ->
              let (outdeg_line, indeg_line), (reverse_graph, graph), constr =
                process_part_general ~mode:"outgoing" v
                  (outdeg_line, indeg_line) (reverse_graph, graph) constr
              in
              process (indeg_line, outdeg_line) (graph, reverse_graph) constr
          | None ->
              (* TODO: a bunch of asserts *)
              constr)
    in
    process (indeg_line, outdeg_line) (graph, inverse_graph) new_constr
  in
  let ty_constraints =
    Skeleton.Param.Map.fold join_component ty_constraints Constraint.empty
  in
  ty_constraints

let solve ~loc type_definitions constraints =
  let sub, constraints =
    unify ~loc type_definitions
      (Substitution.empty, Constraints.empty, constraints)
  in
  (* Print.debug "sub: %t" (Substitution.print_substitutions sub); *)
  (* Print.debug "solved: %t" (Constraint.print_constraints solved); *)
  let cycle_constraints = collapse_cycles constraints in
  let subs', cycle_constraints' =
    unify ~loc type_definitions (sub, constraints, cycle_constraints)
  in
  let cycle_constraints' = Constraints.clean cycle_constraints' in
  let simple_one_constraints = join_simple_nodes cycle_constraints' in
  let subs'', simple_one_constraints' =
    unify ~loc type_definitions
      (subs', cycle_constraints', simple_one_constraints)
  in
  ( sub |> Substitution.merge subs' |> Substitution.merge subs'',
    simple_one_constraints' )
