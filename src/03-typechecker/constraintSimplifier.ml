open Utils
open Language
open Type
open TyCoercion

(*
Configuration for partial optimizations   
*)

let simplify_type_params = true
let simplify_dirt_params = true

(* Merge a type parameter [gamma] into another type parameter [rho] of the
   same skeleton. Writing [x ~> y] when the constraints give a path, possibly
   empty, from [x] to [y], the merge [gamma |-> rho] is complete if:
   - (L) [pi ~> rho] for every lower bound [pi <= gamma],
   - (U) [rho ~> beta] for every upper bound [gamma <= beta],
   - (P+) [rho ~> gamma] if [gamma] is positive,
   - (P-) [gamma ~> rho] if [gamma] is negative.
   The constraints still hold after the merge because of (L) and (U), and the
   simplified type is a subtype of the original because of (P+) and (P-). The
   rule covers both kinds of bridges: if [alpha <= alpha'] is the only lower
   bound of a non-negative [alpha'], take [gamma = alpha'] and [rho = alpha],
   and dually for the only upper bound of a non-positive parameter. It also
   merges a neutral parameter with any parameter between its bounds.

   It also contracts cycles: if [gamma] and [rho] lie on a common cycle, all
   four conditions hold. A bipolar [gamma] can satisfy both (P+) and (P-) only
   on a cycle, and then its instances are coercible both ways, which is the
   same assumption the paper makes for contracting cycles. Each merge removes
   a node, so the loop ends. *)
let merge_type_params ({ Language.Constraints.ty_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let module G = Language.Constraints.TyConstraints.TyParamGraph in
  let module P = FreeParams.TypeParams in
  let merge gamma rho graph =
    let rename v = if TyParam.compare v gamma = 0 then rho else v in
    G.fold
      (fun v1 v2 edge acc ->
        let v1 = rename v1 and v2 = rename v2 in
        if TyParam.compare v1 v2 = 0 then acc
        else G.add_edge ~allow_duplicate:true v1 v2 edge acc)
      graph G.empty
  in
  let can_merge graph reversed reach type_params gamma rho =
    let reaches x y = TyParam.Set.mem y (TyParam.Map.find x reach) in
    TyParam.compare gamma rho <> 0
    && (P.can_be_negative gamma type_params || reaches rho gamma)
    && (P.can_be_positive gamma type_params || reaches gamma rho)
    && TyParam.Map.for_all
         (fun pi _ -> reaches pi rho)
         (G.get_edges gamma reversed)
    && TyParam.Map.for_all
         (fun beta _ -> reaches rho beta)
         (G.get_edges gamma graph)
  in
  let rec merge_all skel graph type_params constraints =
    let vertices = G.vertices graph |> TyParam.Set.elements in
    let reversed = G.reverse graph in
    let reach =
      List.fold_left
        (fun reach v -> TyParam.Map.add v (G.traverse v graph) reach)
        TyParam.Map.empty vertices
    in
    let candidate =
      List.find_map
        (fun gamma ->
          List.find_opt
            (can_merge graph reversed reach type_params gamma)
            vertices
          |> Option.map (fun rho -> (gamma, rho)))
        vertices
    in
    match candidate with
    | None -> constraints
    | Some (gamma, rho) ->
        Print.debug "Merging %t into %t" (TyParam.print gamma)
          (TyParam.print rho);
        let pack ty_param =
          { term = TyParam ty_param; ty = Skeleton.Param skel }
        in
        merge_all skel (merge gamma rho graph)
          (P.combine_polarity rho gamma type_params)
          (UnresolvedConstraints.add_ty_equality
             (pack gamma, pack rho)
             constraints)
  in
  Skeleton.Param.Map.fold
    (fun skel graph constraints ->
      merge_all skel graph params.type_params constraints)
    ty_constraints
    (UnresolvedConstraints.from_resolved resolved)

(* Merge a dirt parameter [gamma] into another dirt parameter [rho], or into
   the empty dirt. An edge [pi -O-> delta] stands for [pi <= O \cup delta].
   Writing [x ~>O y] when there is a path, possibly empty, from [x] to [y]
   whose edges have operations within [O], the merge [gamma |-> rho] is
   complete if:
   - (L) [pi ~>O rho] for every other edge [pi -O-> gamma],
   - (U) [rho ~>O beta] for every other edge [gamma -O-> beta],
   - (P+) [rho ~>{} gamma] if [gamma] is positive,
   - (P-) [gamma ~>{} rho] if [gamma] is negative.
   This is the rule of [merge_type_params], where all operation sets are
   empty, and the proof is the same: a path [pi ~>O rho] composes to
   [pi <= O \cup rho], and (P+) and (P-) need coercions with no additional
   operations. Loops [gamma -O-> gamma] become [rho -O-> rho], which hold
   trivially.

   The empty dirt is a node [bot] with an edge [bot -{}-> delta] to every
   [delta], and nothing reaches it, because the constraints have no closed
   upper bounds. Merging [gamma] into [bot] is thus allowed when [gamma] is
   not negative and has no lower bounds. As in the paper's emptyDirt, we
   merge a whole set of such parameters at once, where the lower bounds may
   also come from the set itself: the parameters on a cycle whose edges have
   operations can be emptied only together. The largest such set consists of
   the parameters that cannot be reached from a negative one. We prefer these
   merges, because the empty dirt allows purity-based optimisations.

   The rule covers contracting cycles without operations, bridges whose edge
   has no operations, and setting non-negative dirt parameters without lower
   bounds to the empty dirt, including the ones that appear in no constraint.
   Each merge removes a parameter, so the loop ends. *)
let merge_dirt_params ({ Language.Constraints.dirt_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let module G = Language.Constraints.DirtConstraints.DirtParamGraph in
  let module P = FreeParams.DirtParams in
  let module S = Dirt.Param.Set in
  let other gamma pi = Dirt.Param.compare pi gamma <> 0 in
  (* Parameters reachable from [x] along edges with operations within [ops],
     remembered for the current graph *)
  let reach graph =
    let memo = ref Dirt.Param.Map.empty in
    fun ops x ->
      let known = Dirt.Param.Map.find_opt x !memo |> Option.value ~default:[] in
      match
        List.find_opt (fun (ops', _) -> Effect.Set.equal ops ops') known
      with
      | Some (_, reached) -> reached
      | None ->
          let rec visit reached v =
            if S.mem v reached then reached
            else
              G.Edges.fold
                (fun w (_, effs) reached ->
                  if Effect.Set.subset effs ops then visit reached w
                  else reached)
                (G.get_edges v graph) (S.add v reached)
          in
          let reached = visit S.empty x in
          memo := Dirt.Param.Map.add x ((ops, reached) :: known) !memo;
          reached
  in
  let lower_bounds reversed gamma =
    G.get_edges gamma reversed
    |> Dirt.Param.Map.filter (fun pi _ -> other gamma pi)
  in
  let upper_bounds graph gamma =
    G.get_edges gamma graph
    |> Dirt.Param.Map.filter (fun beta _ -> other gamma beta)
  in
  (* The parameters that can be emptied together: those that cannot be
     reached from a negative parameter along any edges *)
  let emptiable graph dirt_params alive =
    let rec visit reached v =
      if S.mem v reached then reached
      else
        G.Edges.fold
          (fun w _ reached -> visit reached w)
          (G.get_edges v graph) (S.add v reached)
    in
    let negative =
      S.filter (fun d -> not (P.can_be_positive d dirt_params)) alive
    in
    S.diff alive (S.fold (fun d reached -> visit reached d) negative S.empty)
  in
  let merge_target graph reversed reach dirt_params gamma =
    let lower = lower_bounds reversed gamma in
    let candidates =
      if Dirt.Param.Map.is_empty lower then reach Effect.Set.empty gamma
      else
        Dirt.Param.Map.fold
          (fun pi (_, ops) candidates -> S.inter candidates (reach ops pi))
          lower (G.vertices graph)
    in
    let can_merge rho =
      other gamma rho
      && (P.can_be_negative gamma dirt_params
         || S.mem gamma (reach Effect.Set.empty rho))
      && (P.can_be_positive gamma dirt_params
         || S.mem rho (reach Effect.Set.empty gamma))
      && Dirt.Param.Map.for_all
           (fun pi (_, ops) -> S.mem rho (reach ops pi))
           lower
      && Dirt.Param.Map.for_all
           (fun beta (_, ops) -> S.mem beta (reach ops rho))
           (upper_bounds graph gamma)
    in
    S.elements candidates |> List.find_opt can_merge
  in
  (* Replace [gamma] by [rho] in all edges, dropping loops and intersecting
     the operations of parallel edges, as unification does. *)
  let rename gamma rho graph =
    let rename v = if Dirt.Param.compare v gamma = 0 then rho else v in
    G.fold
      (fun v1 v2 (w, effs) graph ->
        let v1 = rename v1 and v2 = rename v2 in
        if Dirt.Param.compare v1 v2 = 0 then graph
        else
          match Dirt.Param.Map.find_opt v2 (G.get_edges v1 graph) with
          | Some (w', effs') ->
              graph |> G.remove_edge v1 v2
              |> G.add_edge v1 v2 (w', Effect.Set.inter effs effs')
          | None -> G.add_edge v1 v2 (w, effs) graph)
      graph G.empty
  in
  let remove removed graph =
    G.fold
      (fun v1 v2 edge graph ->
        if S.mem v1 removed || S.mem v2 removed then graph
        else G.add_edge v1 v2 edge graph)
      graph G.empty
  in
  let rec merge_all graph dirt_params alive constraints =
    let reversed = G.reverse graph in
    let reach = reach graph in
    let alive_list = S.elements alive in
    let empty = emptiable graph dirt_params alive in
    if not (S.is_empty empty) then (
      Print.debug "Emptying %t"
        (Print.sequence "," Dirt.Param.print (S.elements empty));
      merge_all (remove empty graph) dirt_params (S.diff alive empty)
        (S.fold
           (fun gamma ->
             UnresolvedConstraints.add_dirt_equality
               (Dirt.no_effect gamma, Dirt.empty))
           empty constraints))
    else
      let target gamma =
        merge_target graph reversed reach dirt_params gamma
        |> Option.map (fun rho -> (gamma, rho))
      in
      match List.find_map target alive_list with
      | None -> constraints
      | Some (gamma, rho) ->
          Print.debug "Merging %t into %t" (Dirt.Param.print gamma)
            (Dirt.Param.print rho);
          merge_all (rename gamma rho graph)
            (P.combine_polarity rho gamma dirt_params)
            (S.remove gamma alive)
            (UnresolvedConstraints.add_dirt_equality
               (Dirt.no_effect gamma, Dirt.no_effect rho)
               constraints)
  in
  let alive =
    S.union
      (G.vertices dirt_constraints)
      (S.union params.dirt_params.positive params.dirt_params.negative)
  in
  merge_all dirt_constraints params.dirt_params alive
    (UnresolvedConstraints.from_resolved resolved)

let simplify_type_constraints ~loc type_definitions constraints get_params =
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot
       ~param_polarity:(get_params constraints.Constraints.substitution)
       constraints);
  let constraints = Constraints.remove_loops constraints in
  merge_type_params constraints (get_params constraints.substitution)
  |> Unification.unify ~loc type_definitions

let simplify_dirt_contraints ~loc type_definitions constraints get_params =
  Print.debug "Full constraints: %t"
    (Language.Constraints.print_dot
       ~param_polarity:(get_params constraints.Constraints.substitution)
       constraints);
  let constraints = Constraints.remove_loops constraints in
  merge_dirt_params constraints (get_params constraints.substitution)
  |> Unification.unify ~loc type_definitions
  |> Constraints.remove_loops

let simplify_constraints ~loc type_definitions constraints get_params =
  let constraints =
    if simplify_type_params then
      simplify_type_constraints ~loc type_definitions constraints get_params
    else constraints
  in
  let constraints =
    if simplify_dirt_params then
      simplify_dirt_contraints ~loc type_definitions constraints get_params
    else constraints
  in
  constraints

let simplify_computation ~loc type_definitions constraints typ =
  simplify_constraints ~loc type_definitions constraints (fun subs ->
      let polarity =
        calculate_polarity_dirty_ty (Substitution.apply_sub_dirty_ty subs typ)
      in
      polarity)

let simplify_expression ~loc type_definitions constraints typ =
  simplify_constraints ~loc type_definitions constraints (fun subs ->
      let polarity =
        calculate_polarity_type (Substitution.apply_sub_ty subs typ)
      in
      polarity)

let simplify_top_let_rec ~loc type_definitions constraints tys =
  simplify_constraints ~loc type_definitions constraints (fun subs ->
      let tys = List.map (Substitution.apply_sub_abs_ty subs) tys in
      let params =
        List.fold
          (fun acc ty -> FreeParams.union (calculate_polarity_abs_ty ty) acc)
          FreeParams.empty tys
      in
      params)
