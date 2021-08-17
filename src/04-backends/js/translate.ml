open Utils
open Language
open Syntax
module CoreSyntax = UntypedSyntax

(* ------------------------------------------------------------------------ *)
(* Translations *)

(** Conversion functions. *)
let rec of_expression { it; _ } =
  match it with
  | CoreSyntax.Var v -> Var v
  | CoreSyntax.Const const -> Const const
  | CoreSyntax.Annotated (e, _) -> of_expression e
  | CoreSyntax.Tuple es -> List (List.map of_expression es)
  | CoreSyntax.Record assoc ->
      Record (Assoc.to_list @@ Assoc.map of_expression assoc)
  | CoreSyntax.Variant (lbl, e_opt) -> (
      match e_opt with
      | None -> Syntax.Variant (lbl, None)
      | Some e -> Syntax.Variant (lbl, Some (of_expression e)))
  | CoreSyntax.Lambda abs -> Lambda (of_abstraction abs)
  | CoreSyntax.Effect eff -> Effect eff
  | CoreSyntax.Handler { effect_clauses; value_clause; finally_clause } ->
      let eff_clauses =
        Assoc.to_list @@ Assoc.map of_abstraction2 effect_clauses
      in
      Handler
        {
          effect_clauses = eff_clauses;
          value_clause = of_abstraction value_clause;
          finally_clause = of_abstraction finally_clause;
        }

and of_computation { it; _ } =
  match it with
  | CoreSyntax.Value e -> of_expression e
  | CoreSyntax.Let (p_c_lst, c) ->
      let to_bind abs acc =
        let _match, projections, term = of_abstraction_generic abs in
        match projections with
        | [] -> Bind (term, (_match, acc))
        | _ -> Bind (term, (_match, Sequence (projections @ [ acc ])))
      in
      List.fold_right to_bind p_c_lst @@ of_computation c
  | CoreSyntax.LetRec (var_abs_lst, c) ->
      let wrap_with_lambda (var, abs) =
        Let (var, Lambda (of_abstraction abs))
      in
      let sequential_lets = List.map wrap_with_lambda var_abs_lst in
      Sequence (sequential_lets @ [ of_computation c ])
  | CoreSyntax.Match (e, abs_lst) ->
      let _match = CoreTypes.Variable.fresh "$match" in
      let of_abstraction_with_shape ((p, _) as abs) =
        (shape_of p, of_abstraction abs ~_match_gen:(Some _match))
      in
      Sequence
        [
          Let (_match, of_expression e);
          Match (List.map of_abstraction_with_shape abs_lst);
        ]
  | CoreSyntax.Apply (e1, e2) -> Apply (of_expression e1, of_expression e2)
  | CoreSyntax.Check _ -> Comment "Check is not supported"
  | CoreSyntax.Handle (e, c) -> Handle (of_expression e, of_computation c)

and of_abstraction_generic ?(_match_gen = None) (p, c) =
  let _match, projections = projections p ~_match_gen in
  (_match, projections, of_computation c)

and of_abstraction ?(_match_gen = None) abs =
  let _match, projections, term = of_abstraction_generic abs ~_match_gen in
  match projections with
  | [] -> (_match, term)
  | _ -> (_match, Sequence (projections @ [ term ]))

and of_abstraction2 (p1, p2, c) =
  let _match1, projections1 = projections p1 in
  let _match2, projections2 = projections p2 in
  match projections1 @ projections2 with
  | [] -> (_match1, _match2, of_computation c)
  | projections ->
      (_match1, _match2, Sequence (projections @ [ of_computation c ]))

and projections ?(_match_gen = None) p =
  match (bindings p, _match_gen) with
  | [ (var, []) ], None -> (var, [])
  | bindings, _ ->
      let _match =
        match _match_gen with
        | Some m -> m
        | None -> CoreTypes.Variable.fresh "$match"
      in
      let to_projection (var, pr_list) =
        Let (var, Projection (_match, pr_list))
      in
      (_match, List.map to_projection bindings)

and shape_of { it; _ } =
  match it with
  | CoreSyntax.PNonbinding -> PArbitrary
  | CoreSyntax.PConst const -> PConst const
  | CoreSyntax.PVar _ -> PArbitrary
  | CoreSyntax.PAnnotated (p, _) -> shape_of p
  | CoreSyntax.PAs (p, _) -> shape_of p
  | CoreSyntax.PTuple ps -> PTuple (List.map shape_of ps)
  | CoreSyntax.PRecord assoc -> PRecord (Assoc.map shape_of assoc)
  | CoreSyntax.PVariant (lbl, p_opt) -> (
      match p_opt with
      | None -> PVariant (lbl, None)
      | Some p -> PVariant (lbl, Some (shape_of p)))

and bindings { it; _ } =
  match it with
  | CoreSyntax.PNonbinding -> []
  (* constant is not bound to anything.. it's here only for choosing the correct branch *)
  | CoreSyntax.PConst _ -> []
  | CoreSyntax.PVar var -> [ (var, []) ]
  | CoreSyntax.PAnnotated (p, _) -> bindings p
  | CoreSyntax.PAs (p, var) -> (var, []) :: bindings p
  | CoreSyntax.PTuple ps ->
      let proj_tuple_patt i p =
        let add_proj (var, projs) = (var, Int i :: projs) in
        List.map add_proj @@ bindings p
      in
      List.mapi proj_tuple_patt ps |> List.flatten
  | CoreSyntax.PRecord assoc ->
      let proj_record_patt (f, p) =
        let add_proj (var, projs) = (var, Field f :: projs) in
        List.map add_proj @@ bindings p
      in
      List.map proj_record_patt (Assoc.to_list assoc) |> List.flatten
  | CoreSyntax.PVariant (_, p_opt) -> (
      match p_opt with
      | None -> []
      | Some p ->
          let add_proj (var, projs) = (var, VariantProj :: projs) in
          List.map add_proj @@ bindings p)
