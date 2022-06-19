open Utils
open Language
open Type
open Coercion

type counter = {
  type_coercions : float TyCoercionParam.Map.t;
  dirt_coercion : float DirtCoercionParam.Map.t;
}

let empty =
  {
    type_coercions = TyCoercionParam.Map.empty;
    dirt_coercion = DirtCoercionParam.Map.empty;
  }

let print counter ppf =
  Format.fprintf ppf "{tycoerc: %t;\ndirtcoerc: %t}"
    (TyCoercionParam.Map.print
       (fun n ppf -> Print.print ppf "%f" n)
       counter.type_coercions)
    (DirtCoercionParam.Map.print
       (fun n ppf -> Print.print ppf "%f" n)
       counter.dirt_coercion)

let ( ++ ) c1 c2 =
  let combine _ a b = Some (a +. b) in
  {
    type_coercions =
      TyCoercionParam.Map.union combine c1.type_coercions c2.type_coercions;
    dirt_coercion =
      DirtCoercionParam.Map.union combine c1.dirt_coercion c2.dirt_coercion;
  }

let multiply c coercions =
  {
    type_coercions = TyCoercionParam.Map.map (( *. ) c) coercions.type_coercions;
    dirt_coercion = DirtCoercionParam.Map.map (( *. ) c) coercions.dirt_coercion;
  }

let combine (coercion_params : Coercion.Params.t) counter =
  let coercion_params =
    {
      type_coercions =
        coercion_params.type_coercion_params |> TyCoercionParam.Set.elements
        |> List.map (fun x -> (x, 1.0))
        |> TyCoercionParam.Map.of_bindings;
      dirt_coercion =
        coercion_params.dirt_coercion_params |> DirtCoercionParam.Set.elements
        |> List.map (fun x -> (x, 1.0))
        |> DirtCoercionParam.Map.of_bindings;
    }
  in
  coercion_params ++ counter

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
          (* Compress cycles with the effect edges *)
          || not
               (let edge_labels =
                  Dirt.Param.Set.fold
                    (fun v l ->
                      let edges =
                        DirtConstraints.DirtParamGraph.get_edges v
                          dirt_constraints
                      in
                      Dirt.Param.Set.fold
                        (fun target l ->
                          [
                            DirtConstraints.DirtParamGraph.Edges.get_edge target
                              edges;
                          ]
                          @ l)
                        component l)
                    component []
                  |> List.filter_map (fun x -> x)
                in
                let _, drt =
                  match edge_labels with [] -> assert false | x :: _ -> x
                in
                List.for_all
                  (fun (_, drt') -> Effect.Set.equal drt drt')
                  edge_labels)
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
  let join_skeleton_component add_constraint is_collapsible graph new_constr =
    let module BaseSym = TyParam in
    let module G = TyConstraints.TyParamGraph in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in
    let increment v m =
      BaseSym.Map.update v
        (function None -> Some 1 | Some x -> Some (x + 1))
        m
    in
    let indeg, outdeg =
      G.fold
        (fun source sink _edge (indeg, outdeg) ->
          (increment sink indeg, increment source outdeg))
        graph
        (BaseSym.Map.empty, BaseSym.Map.empty)
    in
    (* Sanity check *)
    let assert_degrees grph line =
      BaseSym.Map.iter
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
      line |> BaseSym.Map.bindings |> List.filter_map get_ones
      |> BaseSym.Set.of_list
    in
    let indeg_line = filter indeg and outdeg_line = filter outdeg in
    let process_part_general ?(mode = "incoming") target
        (indeg_line, outdeg_line) (base_graph, reverse_graph) constr =
      (* Removing outging/incoming edges with degree 1 is practically the same but on different (reversed) graph
         The naming in this function assumes that the input graph is original graph and we are removing edges with
         exactly 1 incoming edge *)
      let remove_current_node_from_list = BaseSym.Set.remove target in
      Print.debug "In mode %s, removing: %t" mode (BaseSym.print target);
      let incoming = G.get_edges target reverse_graph in
      assert (G.Edges.cardinal incoming = 1);
      let source, edge = G.Vertex.Map.choose incoming in
      let next = G.get_edges target base_graph in
      if is_collapsible edge then
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
          line |> remove_current_node_from_list
          |> G.Edges.fold
               (fun potential _ acc ->
                 let num =
                   base_graph |> G.get_edges potential |> G.Edges.cardinal
                 in
                 if num = 1 then acc |> BaseSym.Set.add potential
                 else acc |> BaseSym.Set.remove potential)
               (next
               |> G.Vertex.Map.map (fun _ -> ())
               (* Treat source as any other *)
               |> G.Edges.add_edge ~allow_duplicate:true source ())
        in
        let indeg_line = remove_edges reverse_graph indeg_line
        and outdeg_line = remove_edges base_graph outdeg_line in
        ( (indeg_line, outdeg_line),
          (base_graph, reverse_graph),
          add_constraint source target constr )
      else
        ( ( indeg_line |> remove_current_node_from_list,
            outdeg_line |> remove_current_node_from_list ),
          (base_graph, reverse_graph),
          constr )
    in
    let rec process (indeg_line, outdeg_line) (graph, reverse_graph) constr =
      match BaseSym.Set.choose_opt indeg_line with
      | Some v ->
          let (indeg_line, outdeg_line), (graph, reverse_graph), constr =
            process_part_general v (indeg_line, outdeg_line)
              (graph, reverse_graph) constr
          in
          process (indeg_line, outdeg_line) (graph, reverse_graph) constr
      | None -> (
          match BaseSym.Set.choose_opt outdeg_line with
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
  let new_constr =
    Skeleton.Param.Map.fold
      (fun skel graph acc ->
        let pack ty_param =
          { term = TyParam ty_param; ty = Skeleton.Param skel }
        in
        let add_constraint source target constraints =
          Constraint.add_ty_equality (pack source, pack target) constraints
        in
        join_skeleton_component add_constraint
          (fun _ -> (* collapse all edges *) true)
          graph acc)
      ty_constraints Constraint.empty
  in
  new_constr

let join_simple_dirt_nodes { Language.Constraints.dirt_constraints; _ } _level =
  let open Language.Constraints in
  let join_dirt_component add_constraint is_collapsible graph new_constr =
    let module BaseSym = Dirt.Param in
    let module G = DirtConstraints.DirtParamGraph in
    (* We can assume that the graph is a DAG *)
    let inverse_graph = G.reverse graph in
    let increment v m =
      BaseSym.Map.update v
        (function None -> Some 1 | Some x -> Some (x + 1))
        m
    in
    let indeg, outdeg =
      G.fold
        (fun source sink _edge (indeg, outdeg) ->
          (increment sink indeg, increment source outdeg))
        graph
        (BaseSym.Map.empty, BaseSym.Map.empty)
    in
    (* Sanity check *)
    let assert_degrees grph line =
      BaseSym.Map.iter
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
      line |> BaseSym.Map.bindings |> List.filter_map get_ones
      |> BaseSym.Set.of_list
    in
    let indeg_line = filter indeg and outdeg_line = filter outdeg in
    let process_part_general ?(mode = "outgoing") target
        (indeg_line, outdeg_line) (base_graph, reverse_graph) (visited, changed)
        constr =
      (* Removing outging/incoming edges with degree 1 is practically the same but on different (reversed) graph
         The naming in this function assumes that the input graph is original graph and we are removing edges with
         exactly 1 incoming edge *)
      let remove_current_node_from_list = BaseSym.Set.remove target in
      let visited = BaseSym.Set.add target visited in
      Print.debug "Contracting drit, in mode %s, removing: %t" mode
        (BaseSym.print target);
      let incoming = G.get_edges target reverse_graph in
      assert (G.Edges.cardinal incoming = 1);
      let source, ((_, dirts) as edge) = G.Vertex.Map.choose incoming in
      let next = G.get_edges target base_graph in
      let only_empty =
        G.Edges.fold
          (fun to_ (_, drt) acc ->
            Print.debug "from me only_empty %t" (BaseSym.print to_);
            Effect.Set.is_empty drt && acc)
          next true
      in
      let all_edges_same =
        let l = G.Edges.fold (fun _ (_, drt) l -> drt :: l) next [] in
        match l with
        | [] -> false
        | x :: xs -> List.for_all (fun y -> Effect.Set.equal x y) xs
      in
      (* Check if outgoing edges strictly dominate this edge - only on outgoing *)
      let next_from_source =
        G.Vertex.Map.find_opt source reverse_graph
        |> Option.value ~default:BaseSym.Map.empty
      in
      let is_dominated =
        Effect.Set.subset dirts
          (G.Edges.fold
             (fun to_ (_, drt) ->
               Print.debug "from me %t" (BaseSym.print to_);
               Effect.Set.inter drt)
             next_from_source dirts)
        && mode = "outgoing"
        && (not (BaseSym.Map.is_empty next_from_source))
        && Effect.Set.is_empty dirts
        (* && _level = 2 *)
      in
      Print.debug "%b %b %b" (is_collapsible edge) only_empty is_dominated;
      let is_dominated = is_dominated in
      let can_continue_on_graph = all_edges_same && not is_dominated in
      if is_collapsible edge || is_dominated then
        let _ =
          Print.debug "Contracting drit, in mode %s, really removing: %t" mode
            (BaseSym.print target)
        in
        (* If all the rewired edges are simple, we can update graph, otherwise we have to re-solve and don't update graph just yet *)
        let (indeg_line, outdeg_line), (base_graph, reverse_graph) =
          (* if no graph invariants get broken, we do not need to resolve *)
          if can_continue_on_graph then
            let base_graph =
              if only_empty then
                base_graph
                |> G.remove_edge source target (* remove this edge *)
                |> G.Edges.fold (* rewire other edges *)
                     (fun next e acc ->
                       acc |> G.remove_edge target next
                       |> G.add_edge (* Triangels can produce duplicate edges *)
                            ~allow_duplicate:true source next e)
                     next
                |> G.remove_vertex_unsafe target
              else base_graph
            and reverse_graph =
              if only_empty then
                reverse_graph
                |> G.remove_edge target source
                |> G.Edges.fold (* rewire other edges *)
                     (fun next e acc ->
                       acc |> G.remove_edge next target
                       |> G.add_edge ~allow_duplicate:true next source e)
                     next
                |> G.remove_vertex_unsafe target
              else reverse_graph
            in
            let remove_edges base_graph line =
              line |> remove_current_node_from_list
              |> G.Edges.fold
                   (fun potential _ acc ->
                     let num =
                       base_graph |> G.get_edges potential |> G.Edges.cardinal
                     in
                     if num = 1 then acc |> BaseSym.Set.add potential
                     else acc |> BaseSym.Set.remove potential)
                   (next
                   |> G.Vertex.Map.map (fun _ -> ())
                   (* Treat source as any other *)
                   |> G.Edges.add_edge ~allow_duplicate:true source ())
            in
            let indeg_line = remove_edges reverse_graph indeg_line
            and outdeg_line = remove_edges base_graph outdeg_line in
            ((indeg_line, outdeg_line), (base_graph, reverse_graph))
          else ((indeg_line, outdeg_line), (base_graph, reverse_graph))
        in
        ( (indeg_line, outdeg_line),
          (base_graph, reverse_graph),
          (visited, BaseSym.Set.add target changed),
          add_constraint source target constr )
      else
        ( ( indeg_line |> remove_current_node_from_list,
            outdeg_line |> remove_current_node_from_list ),
          (base_graph, reverse_graph),
          (visited, changed),
          (* Do not contract constraints if the edge is not collapsible *)
          constr )
    in
    let rec process (indeg_line, outdeg_line) (graph, reverse_graph)
        (visited, changed) constr =
      let indeg_line = BaseSym.Set.diff indeg_line visited in
      let outdeg_line = BaseSym.Set.diff outdeg_line visited in
      (* Print.debug "Indegs line: %t"
           (Print.sequence "," BaseSym.print (BaseSym.Set.elements indeg_line));
         Print.debug "Outdegs line: %t"
           (Print.sequence "," BaseSym.print (BaseSym.Set.elements outdeg_line)); *)
      match BaseSym.Set.choose_opt indeg_line with
      | Some v ->
          let ( (indeg_line, outdeg_line),
                (graph, reverse_graph),
                (visited, changed),
                constr ) =
            process_part_general v (indeg_line, outdeg_line)
              (graph, reverse_graph) (visited, changed) constr
          in
          process (indeg_line, outdeg_line) (graph, reverse_graph)
            (visited, changed) constr
      | _ -> (
          match BaseSym.Set.choose_opt outdeg_line with
          | Some v ->
              let ( (outdeg_line, indeg_line),
                    (reverse_graph, graph),
                    (visited, changed),
                    constr ) =
                process_part_general ~mode:"outgoing" v
                  (outdeg_line, indeg_line) (reverse_graph, graph)
                  (visited, changed) constr
              in
              process (indeg_line, outdeg_line) (graph, reverse_graph)
                (visited, changed) constr
          | _ ->
              (* TODO: a bunch of asserts *)
              (constr, changed))
    in
    process (indeg_line, outdeg_line) (graph, inverse_graph)
      (Dirt.Param.Set.empty, Dirt.Param.Set.empty)
      new_constr
  in
  join_dirt_component
    (fun p1 p2 ->
      Constraint.add_dirt_equality (Dirt.no_effect p1, Dirt.no_effect p2))
    (fun (_, drt) -> Effect.Set.is_empty drt)
    dirt_constraints Constraint.empty

let calculate_lower_bound { Language.Constraints.dirt_constraints; _ }
    allow_contraction =
  (* Ths is a bad implementation of toposort, but it should work from now, to see, how it goes
     (at some point cycle detection should also sort it) *)
  let open Language.Constraints in
  let module BaseSym = Dirt.Param in
  let module G = DirtConstraints.DirtParamGraph in
  (* Toposort *)
  let components = G.scc_tarjan dirt_constraints in
  (* First combine multinodes *)
  let node_effects, parents, _component_parent =
    List.fold_left
      (fun (node_w, parents, component_parent) component ->
        match component with
        | top :: _ ->
            let effects, parents =
              List.fold
                (fun (effects, parents) start ->
                  (* Add parent node *)
                  let parents = BaseSym.Map.add start top parents in
                  let edges = G.get_edges start dirt_constraints in
                  (* loop over all outgoing in the same cycle *)
                  let effects =
                    List.fold
                      (fun effects target ->
                        let edge_effects =
                          edges |> G.Edges.get_edge target
                          |> Option.default_map Effect.Set.empty snd
                        in
                        Effect.Set.union effects edge_effects)
                      effects component
                  in
                  (effects, parents))
                (Effect.Set.empty, parents)
                component
            in
            (* add cycle effects to all nodes in this scc *)
            ( List.fold
                (fun acc v -> BaseSym.Map.add v effects acc)
                node_w component,
              parents,
              component_parent |> BaseSym.Map.add top component )
        | [] -> assert false)
      (BaseSym.Map.empty, BaseSym.Map.empty, BaseSym.Map.empty)
      components
  in
  (* Calculate lower bound for all nodes *)
  let lower_bounds = BaseSym.Map.empty in
  (* Traverse in topological sort order, and push all  *)
  let lower_bounds =
    List.fold_left
      (fun lower_bounds component ->
        let parent = List.hd component in
        let parent = BaseSym.Map.find parent parents in
        let component_lower_bound =
          match BaseSym.Map.find_opt parent lower_bounds with
          | Some lb -> lb
          | None -> Effect.Set.empty
        in
        let component_lower_bound =
          Effect.Set.union component_lower_bound
            (BaseSym.Map.find parent node_effects)
        in
        let lower_bounds =
          List.fold
            (fun lower_bounds v ->
              let edges = G.get_edges v dirt_constraints in
              let lower_bounds =
                BaseSym.Map.fold
                  (fun target (_, eff) lower_bounds ->
                    let pushed = Effect.Set.union eff component_lower_bound in
                    let target_parent = BaseSym.Map.find target parents in
                    let lower_bounds =
                      BaseSym.Map.update target_parent
                        (function
                          | None -> Some pushed
                          | Some existing ->
                              Some (Effect.Set.union existing pushed))
                        lower_bounds
                    in
                    lower_bounds)
                  edges lower_bounds
              in
              lower_bounds)
            lower_bounds component
        in
        lower_bounds)
      lower_bounds components
  in
  let constraints, change =
    G.fold
      (fun source target ((_, drt_set) as e) ((cons, _) as acc) ->
        let target_parent = BaseSym.Map.find target parents in
        let source_parent = BaseSym.Map.find source parents in
        if BaseSym.compare source target_parent = 0 then acc
        else if
          Effect.Set.subset drt_set
            (Option.value
               (BaseSym.Map.find_opt source_parent lower_bounds)
               ~default:Effect.Set.empty)
          && allow_contraction e
        then
          ( Constraint.add_dirt_equality
              (Dirt.no_effect source, Dirt.no_effect target)
              cons,
            true )
        else acc)
      dirt_constraints (Constraint.empty, false)
  in
  (constraints, change)

let contract_constraints () = ()

let rec score_expression e =
  let cur, cong =
    match e with
    | { term = Term.Var _; _ } -> (Coercion.Params.empty, empty)
    | { term = Term.Const _; _ } -> (Coercion.Params.empty, empty)
    | { term = Term.Tuple lst; _ } ->
        ( Coercion.Params.empty,
          List.fold ( ++ ) empty (List.map score_expression lst) )
    | { term = Term.Record r; _ } ->
        ( Coercion.Params.empty,
          List.fold ( ++ ) empty
            (List.map score_expression (Label.Map.values r)) )
    | { term = Term.Variant (_, e); _ } ->
        (Coercion.Params.empty, Option.default_map empty score_expression e)
    | { term = Term.Lambda abs; _ } ->
        (Coercion.Params.empty, score_abstraction abs)
    | { term = Term.Handler hc; _ } ->
        (Coercion.Params.empty, score_handler_clauses hc)
    | { term = Term.HandlerWithFinally { handler_clauses; finally_clause }; _ }
      ->
        ( Coercion.Params.empty,
          score_handler_clauses handler_clauses
          ++ score_abstraction finally_clause )
    | { term = Term.CastExp (exp, coer); _ } ->
        (Coercion.coercion_params_ty_coercion coer, score_expression exp)
  in
  combine cur (multiply 0.5 cong)

and score_abstraction { term = _, c; _ } = score_computation c

and score_handler_clauses { term = { Term.value_clause; effect_clauses }; _ } =
  score_abstraction value_clause
  ++ (Assoc.values_of effect_clauses.effect_part
     |> List.map (fun { term = _, _, c; _ } -> score_computation c)
     |> List.fold ( ++ ) empty)

and score_computation c =
  let cur, cong =
    match c with
    | { term = Term.Value e; _ } -> (Coercion.Params.empty, score_expression e)
    | { term = Term.LetVal (e, abs); _ } ->
        (Coercion.Params.empty, score_expression e ++ score_abstraction abs)
    | { term = Term.LetRec (lst, c); _ } ->
        ( Coercion.Params.empty,
          Assoc.fold_left
            (fun acc (_, abs) -> acc ++ score_abstraction abs)
            empty lst
          ++ score_computation c )
    | { term = Term.Match (e, lst); _ } ->
        ( Coercion.Params.empty,
          score_expression e
          ++ List.fold_left
               (fun acc abs -> acc ++ score_abstraction abs)
               empty lst )
    | { term = Term.Apply (e1, e2); _ } ->
        (Coercion.Params.empty, score_expression e1 ++ score_expression e2)
    | { term = Term.Handle (e, c); _ } ->
        (Coercion.Params.empty, score_expression e ++ score_computation c)
    | { term = Term.Call (_, e, abs); _ } ->
        (Coercion.Params.empty, score_expression e ++ score_abstraction abs)
    | { term = Term.Bind (c1, abs); _ } ->
        (Coercion.Params.empty, score_computation c1 ++ score_abstraction abs)
    | { term = Term.CastComp (c, coer); _ } ->
        (Coercion.coercion_params_dirty_coercion coer, score_computation c)
    | { term = Term.Check (_, c); _ } ->
        (Coercion.Params.empty, score_computation c)
  in

  combine cur (multiply 0.5 cong)

let optimize_top_let subs constraints defs =
  let counter =
    List.fold
      (fun acc abs -> score_abstraction abs ++ acc)
      empty (Assoc.values_of defs)
  in
  Print.debug "counter %t" (print counter);
  (subs, constraints)

(* 
if !Config.garbage_collect then
  let cycle_constraints = collapse_cycles constraints in
  let subs', cycle_constraints' =
    unify ~loc type_definitions (sub, constraints, cycle_constraints)
  in
  let cycle_constraints' = Constraints.clean cycle_constraints' in
  let simple_one_constraints = join_simple_nodes cycle_constraints' in
  let subs'', simple_one_constraints' =
    unify ~loc type_definitions
      ( sub |> Substitution.merge subs',
        cycle_constraints',
        simple_one_constraints )
  in
  let rec runner level subs_state cons_state =
    Print.debug "Contracting dirts on %d\n" level;
    Print.debug "(* Constraints graph before :\n %t \n*)"
      (Language.Constraints.print_dot cons_state);
    let new_cons, changed = join_simple_dirt_nodes cons_state level in
    (* Dont collect any lower bounds  *)
    let new_cons', ch = calculate_lower_bound cons_state (fun _ -> true) in

    let subs_state', cons_state' =
      unify ~loc type_definitions
        (subs_state, cons_state, new_cons |> Constraint.union new_cons')
    in

    Print.debug "(* Constraints graph after :\n %t \n*)"
      (Language.Constraints.print_dot cons_state');
    let cons_state' = Constraints.clean cons_state' in
    if level >= 10 || (Dirt.Param.Set.is_empty changed && not ch) then
      (subs_state', cons_state')
    else runner (level + 1) subs_state' cons_state'
  in
  let subs, constraints =
    runner 0
      (sub |> Substitution.merge subs' |> Substitution.merge subs'')
      simple_one_constraints'
  in
  (subs, constraints)
else (sub, constraints) *)
