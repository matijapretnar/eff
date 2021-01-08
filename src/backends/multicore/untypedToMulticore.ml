open CoreUtils
module Multicore = MulticoreSyntax
module CoreSyntax = UntypedSyntax

let abstraction_is_id (p, c) =
  (* Used to remove trivial finally clauses from handlers. *)
  match p with
  | Multicore.PVar v ->
      CoreTypes.Variable.fold (fun desc _ -> desc = "$id_par") v
  | _ -> false

let rec of_abstraction (p, c) = (of_pattern p, of_computation c)

and of_abstraction2 (p1, p2, c) =
  (of_pattern p1, of_pattern p2, of_computation c)

(** Conversion functions. *)
and of_expression { it; at } =
  match it with
  | CoreSyntax.Var v -> Multicore.Var v
  | CoreSyntax.Const const -> Multicore.Const const
  | CoreSyntax.Annotated (e, ty) ->
      Multicore.Annotated (of_expression e, of_type ty)
  | CoreSyntax.Tuple es -> Multicore.Tuple (List.map of_expression es)
  | CoreSyntax.Record assoc -> Multicore.Record (Assoc.map of_expression assoc)
  | CoreSyntax.Variant (lbl, e_opt) -> (
      match e_opt with
      | None -> Multicore.Variant (lbl, None)
      | Some e -> Multicore.Variant (lbl, Some (of_expression e)))
  | CoreSyntax.Lambda abs -> (
      (* Transform back to [function] keyword if possible *)
      match abs with
      | p, { it = CoreSyntax.Match (e, abs_lst) } -> (
          let p' = of_pattern p in
          let e' = of_expression e in
          match (p', e') with
          | Multicore.PVar v1, Multicore.Var v2
            when v1 = v2
                 && CoreTypes.Variable.fold
                      (fun desc _ -> desc = "$function")
                      v1 ->
              let converter abs = Multicore.ValueClause (of_abstraction abs) in
              Multicore.Function (List.map converter abs_lst)
          | _ -> Multicore.Lambda (of_abstraction abs))
      | _ -> Multicore.Lambda (of_abstraction abs))
  | CoreSyntax.Effect eff -> Multicore.Effect eff
  | CoreSyntax.Handler { effect_clauses; value_clause; finally_clause } ->
      (* Non-trivial case *)
      let effect_clauses' =
        List.map
          (fun (eff, abs) -> Multicore.EffectClause (eff, of_abstraction2 abs))
          (Assoc.to_list effect_clauses)
      in
      let value_clause' = Multicore.ValueClause (of_abstraction value_clause) in
      let finally_clause_abs = of_abstraction finally_clause in
      let ghost_bind = CoreTypes.Variable.fresh "$c_thunk" in
      let match_handler =
        Multicore.Match
          ( Multicore.Apply (Multicore.Var ghost_bind, Multicore.Tuple []),
            value_clause' :: effect_clauses' )
      in
      if abstraction_is_id finally_clause_abs then
        Multicore.Lambda (Multicore.PVar ghost_bind, match_handler)
      else
        Multicore.Lambda
          ( Multicore.PVar ghost_bind,
            Multicore.Apply (Multicore.Lambda finally_clause_abs, match_handler)
          )

and of_computation { it; at } =
  match it with
  | CoreSyntax.Value e -> of_expression e
  | CoreSyntax.Let (p_c_lst, c) ->
      let converter (p, c) = (of_pattern p, of_computation c) in
      Multicore.Let (List.map converter p_c_lst, of_computation c)
  | CoreSyntax.LetRec (var_abs_lst, c) ->
      let converter (var, abs) = (var, of_abstraction abs) in
      Multicore.LetRec (List.map converter var_abs_lst, of_computation c)
  | CoreSyntax.Match (e, abs_lst) ->
      let converter abs = Multicore.ValueClause (of_abstraction abs) in
      Multicore.Match (of_expression e, List.map converter abs_lst)
  | CoreSyntax.Apply (e1, e2) ->
      Multicore.Apply (of_expression e1, of_expression e2)
  | CoreSyntax.Check c -> Multicore.Check (of_computation c)
  | CoreSyntax.Handle (e, c) ->
      (* Non-trivial case *)
      let modified_handler = of_expression e in
      let thunked_c =
        Multicore.Lambda (Multicore.PNonbinding, of_computation c)
      in
      Multicore.Apply (modified_handler, thunked_c)

and of_pattern { it; at } =
  match it with
  | CoreSyntax.PVar var -> Multicore.PVar var
  | CoreSyntax.PAnnotated (p, ty) ->
      Multicore.PAnnotated (of_pattern p, of_type ty)
  | CoreSyntax.PAs (p, var) -> Multicore.PAs (of_pattern p, var)
  | CoreSyntax.PTuple ps -> Multicore.PTuple (List.map of_pattern ps)
  | CoreSyntax.PRecord assoc -> Multicore.PRecord (Assoc.map of_pattern assoc)
  | CoreSyntax.PVariant (lbl, p_opt) -> (
      match p_opt with
      | None -> Multicore.PVariant (lbl, None)
      | Some p -> Multicore.PVariant (lbl, Some (of_pattern p)))
  | CoreSyntax.PConst const -> Multicore.PConst const
  | CoreSyntax.PNonbinding -> Multicore.PNonbinding

and of_type = function
  | Type.Apply (name, tys) -> Multicore.TyApply (name, List.map of_type tys)
  | Type.TyParam ty_param -> Multicore.TyParam ty_param
  | Type.Basic s -> Multicore.TyBasic s
  | Type.Tuple tys -> Multicore.TyTuple (List.map of_type tys)
  | Type.Arrow (ty1, ty2) -> Multicore.TyArrow (of_type ty1, of_type ty2)
  | Type.Handler { value; finally } ->
      (* Non-trivial case *)
      Multicore.TyArrow
        ( Multicore.TyArrow (of_type Type.unit_ty, of_type value),
          of_type finally )

and of_tydef = function
  | Tctx.Record assoc -> Multicore.TyDefRecord (Assoc.map of_type assoc)
  | Tctx.Sum assoc ->
      let converter = function None -> None | Some ty -> Some (of_type ty) in
      Multicore.TyDefSum (Assoc.map converter assoc)
  | Tctx.Inline ty -> Multicore.TyDefInline (of_type ty)
