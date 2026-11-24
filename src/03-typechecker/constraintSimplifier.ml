open Utils
open Language
open Type
open TyCoercion

(*
Configuration for partial optimizations   
*)

let simplify_type_params = true
let simplify_dirt_params = true

(* Merging parameters.

   A constraint graph has parameters as nodes and an edge [pi -O-> delta] for
   each constraint [pi <= O \cup delta]. For type parameters, [O] is always
   empty. Writing [x ~>O y] when there is a path, possibly empty, from [x] to
   [y] whose edges have operations within [O], merging a parameter [gamma]
   into another parameter [rho] is complete if:
   - (L) [pi ~>O rho] for every edge [pi -O-> gamma] with [pi <> gamma],
   - (U) [rho ~>O beta] for every edge [gamma -O-> beta] with [beta <> gamma],
   - (P+) [rho ~>{} gamma] if [gamma] is positive,
   - (P-) [gamma ~>{} rho] if [gamma] is negative.
   For an instantiation of the original constraints, take the same one on all
   parameters but [gamma]. A path [pi ~>O rho] composes to [pi <= O \cup rho],
   which instantiates the merged edges by (L) and (U), and a loop
   [gamma -O-> gamma] becomes [rho -O-> rho], which holds trivially. (P+) and
   (P-) give the coercion between the simplified and the original type at
   [gamma], with no additional operations. A neutral [gamma] needs neither.

   Bridges are instances of the rule: if [alpha -{}-> alpha'] is the only
   lower bound of a non-negative [alpha'], take [gamma = alpha'] and
   [rho = alpha], and dually. So is contracting a cycle without operations,
   where [gamma] and [rho] lie on it. A bipolar [gamma] satisfies both (P+)
   and (P-) only on such a cycle, and then its instances are coercible both
   ways, which is the same assumption the paper makes for contracting cycles.
   The rule also merges a neutral parameter with any parameter between its
   bounds, which bridges cannot do.

   Dirts also have the empty dirt, a node [bot] with an edge [bot -{}-> delta]
   to every [delta] and, as the constraints have no closed upper bounds, no
   edges into it. So [gamma] can merge into [bot] if it is not negative and
   has no lower bounds. As in the paper's emptyDirt, we merge a whole set of
   such parameters at once, as their lower bounds may also come from the set:
   the parameters on a cycle whose edges have operations can be emptied only
   together. The largest such set consists of the parameters that cannot be
   reached from a negative one. We prefer these merges, because the empty dirt
   allows purity-based optimisations.

   Each merge removes a parameter, so the loop ends. *)
module Merge (V : Symbol.S) = struct
  type graph = Effect.Set.t V.Map.t V.Map.t
  type target = Empty | Param of V.t

  let edges v (graph : graph) =
    V.Map.find_opt v graph |> Option.value ~default:V.Map.empty

  let fold f (graph : graph) acc =
    V.Map.fold (fun v -> V.Map.fold (f v)) graph acc

  (* Adding an edge parallel to an existing one keeps the intersection of
     their operations, as unification does. *)
  let add_edge v1 v2 ops (graph : graph) =
    if V.compare v1 v2 = 0 then graph
    else
      V.Map.add v1
        (V.Map.update v2
           (function
             | None -> Some ops | Some ops' -> Some (Effect.Set.inter ops ops'))
           (edges v1 graph))
        graph

  let reverse graph = fold (fun v1 v2 -> add_edge v2 v1) graph V.Map.empty

  let vertices graph =
    fold
      (fun v1 v2 _ vs -> vs |> V.Set.add v1 |> V.Set.add v2)
      graph V.Set.empty

  (* The parameters reachable from [sources] along edges whose operations
     satisfy [follow] *)
  let reachable graph follow sources =
    let rec visit reached v =
      if V.Set.mem v reached then reached
      else
        V.Map.fold
          (fun w ops reached -> if follow ops then visit reached w else reached)
          (edges v graph) (V.Set.add v reached)
    in
    V.Set.fold (fun v reached -> visit reached v) sources V.Set.empty

  (* [merges ~bottom ~positive ~negative ~alive graph] lists the merges, in
     order. [alive] are the parameters to consider, which may include ones
     without edges. *)
  let merges ~bottom ~positive ~negative ~alive (graph : graph) =
    let rec merge_all graph positive negative alive merges =
      let others gamma map = V.Map.remove gamma map in
      let reversed = reverse graph in
      let memo = ref V.Map.empty in
      let reach ops x =
        let known = V.Map.find_opt x !memo |> Option.value ~default:[] in
        match
          List.find_opt (fun (ops', _) -> Effect.Set.equal ops ops') known
        with
        | Some (_, reached) -> reached
        | None ->
            let reached =
              reachable graph
                (fun ops' -> Effect.Set.subset ops' ops)
                (V.Set.singleton x)
            in
            memo := V.Map.add x ((ops, reached) :: known) !memo;
            reached
      in
      let empty =
        if bottom then
          V.Set.diff alive
            (reachable graph (fun _ -> true) (V.Set.inter alive negative))
        else V.Set.empty
      in
      if not (V.Set.is_empty empty) then
        let graph =
          fold
            (fun v1 v2 ops graph ->
              if V.Set.mem v1 empty || V.Set.mem v2 empty then graph
              else add_edge v1 v2 ops graph)
            graph V.Map.empty
        in
        merge_all graph positive negative (V.Set.diff alive empty)
          (List.rev_map (fun gamma -> (gamma, Empty)) (V.Set.elements empty)
          @ merges)
      else
        let target gamma =
          let lower = others gamma (edges gamma reversed)
          and upper = others gamma (edges gamma graph) in
          let candidates =
            if V.Map.is_empty lower then reach Effect.Set.empty gamma
            else
              V.Map.fold
                (fun pi ops candidates -> V.Set.inter candidates (reach ops pi))
                lower (vertices graph)
          in
          let can_merge rho =
            V.compare gamma rho <> 0
            && ((not (V.Set.mem gamma positive))
               || V.Set.mem gamma (reach Effect.Set.empty rho))
            && ((not (V.Set.mem gamma negative))
               || V.Set.mem rho (reach Effect.Set.empty gamma))
            && V.Map.for_all (fun pi ops -> V.Set.mem rho (reach ops pi)) lower
            && V.Map.for_all
                 (fun beta ops -> V.Set.mem beta (reach ops rho))
                 upper
          in
          V.Set.elements candidates |> List.find_opt can_merge
          |> Option.map (fun rho -> (gamma, rho))
        in
        match List.find_map target (V.Set.elements alive) with
        | None -> List.rev merges
        | Some (gamma, rho) ->
            let rename v = if V.compare v gamma = 0 then rho else v in
            let graph =
              fold
                (fun v1 v2 ops -> add_edge (rename v1) (rename v2) ops)
                graph V.Map.empty
            in
            let carry set =
              if V.Set.mem gamma set then V.Set.add rho set else set
            in
            merge_all graph (carry positive) (carry negative)
              (V.Set.remove gamma alive)
              ((gamma, Param rho) :: merges)
    in
    merge_all graph positive negative alive []
end

module TypeMerge = Merge (TyParam)
module DirtMerge = Merge (Dirt.Param)

let merge_type_params ({ Language.Constraints.ty_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let module G = Language.Constraints.TyConstraints.TyParamGraph in
  Skeleton.Param.Map.fold
    (fun skel graph constraints ->
      let graph =
        G.fold
          (fun v1 v2 _ -> TypeMerge.add_edge v1 v2 Effect.Set.empty)
          graph TyParam.Map.empty
      in
      let pack ty_param =
        { term = TyParam ty_param; ty = Skeleton.Param skel }
      in
      TypeMerge.merges ~bottom:false ~positive:params.type_params.positive
        ~negative:params.type_params.negative ~alive:(TypeMerge.vertices graph)
        graph
      |> List.fold_left
           (fun constraints (gamma, target) ->
             match target with
             | TypeMerge.Param rho ->
                 UnresolvedConstraints.add_ty_equality
                   (pack gamma, pack rho)
                   constraints
             | TypeMerge.Empty -> assert false)
           constraints)
    ty_constraints
    (UnresolvedConstraints.from_resolved resolved)

let merge_dirt_params ({ Language.Constraints.dirt_constraints; _ } as resolved)
    (params : FreeParams.params) =
  let module G = Language.Constraints.DirtConstraints.DirtParamGraph in
  let graph =
    G.fold
      (fun v1 v2 (_, ops) -> DirtMerge.add_edge v1 v2 ops)
      dirt_constraints Dirt.Param.Map.empty
  in
  let { FreeParams.DirtParams.positive; negative } = params.dirt_params in
  let alive =
    Dirt.Param.Set.union (DirtMerge.vertices graph)
      (Dirt.Param.Set.union positive negative)
  in
  DirtMerge.merges ~bottom:true ~positive ~negative ~alive graph
  |> List.fold_left
       (fun constraints (gamma, target) ->
         let target =
           match target with
           | DirtMerge.Param rho -> Dirt.no_effect rho
           | DirtMerge.Empty -> Dirt.empty
         in
         UnresolvedConstraints.add_dirt_equality
           (Dirt.no_effect gamma, target)
           constraints)
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
