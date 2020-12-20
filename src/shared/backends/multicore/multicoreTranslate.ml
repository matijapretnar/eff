open CoreUtils
open MulticoreSyntax
module CoreSyntax = UntypedSyntax

(* ------------------------------------------------------------------------ *)
(* Translations *)

let abstraction_is_id (p, _c) =
  (* Used to remove trivial finally clauses from handlers. *)
  match p with
  | PVar v -> CoreTypes.Variable.fold (fun desc _ -> desc = "$id_par") v
  | _ -> false

let rec of_abstraction (p, c) = (of_pattern p, of_computation c)

and of_abstraction2 (p1, p2, c) =
  (of_pattern p1, of_pattern p2, of_computation c)

(** Conversion functions. *)
and of_expression { it; _ } =
  match it with
  | CoreSyntax.Var v -> Var v
  | CoreSyntax.Const const -> Const const
  | CoreSyntax.Annotated (e, ty) -> Annotated (of_expression e, of_type ty)
  | CoreSyntax.Tuple es -> Tuple (List.map of_expression es)
  | CoreSyntax.Record assoc -> Record (Assoc.map of_expression assoc)
  | CoreSyntax.Variant (lbl, e_opt) -> (
      match e_opt with
      | None -> Variant (lbl, None)
      | Some e -> Variant (lbl, Some (of_expression e)))
  | CoreSyntax.Lambda abs -> (
      (* Transform back to [function] keyword if possible *)
      match abs with
      | p, { it = CoreSyntax.Match (e, abs_lst); _ } -> (
          let p' = of_pattern p in
          let e' = of_expression e in
          match (p', e') with
          | PVar v1, Var v2
            when v1 = v2
                 && CoreTypes.Variable.fold
                      (fun desc _ -> desc = "$function")
                      v1 ->
              let converter abs = ValueClause (of_abstraction abs) in
              Function (List.map converter abs_lst)
          | _ -> Lambda (of_abstraction abs))
      | _ -> Lambda (of_abstraction abs))
  | CoreSyntax.Effect eff -> Effect eff
  | CoreSyntax.Handler { effect_clauses; value_clause; finally_clause } ->
      (* Non-trivial case *)
      let effect_clauses' =
        List.map
          (fun (eff, abs) -> EffectClause (eff, of_abstraction2 abs))
          (Assoc.to_list effect_clauses)
      in
      let value_clause' = ValueClause (of_abstraction value_clause) in
      let finally_clause_abs = of_abstraction finally_clause in
      let ghost_bind = CoreTypes.Variable.fresh "$c_thunk" in
      let match_handler =
        Match
          (Apply (Var ghost_bind, Tuple []), value_clause' :: effect_clauses')
      in
      if abstraction_is_id finally_clause_abs then
        Lambda (PVar ghost_bind, match_handler)
      else
        Lambda
          (PVar ghost_bind, Apply (Lambda finally_clause_abs, match_handler))

and of_computation { it; _ } =
  match it with
  | CoreSyntax.Value e -> of_expression e
  | CoreSyntax.Let (p_c_lst, c) ->
      let converter (p, c) = (of_pattern p, of_computation c) in
      Let (List.map converter p_c_lst, of_computation c)
  | CoreSyntax.LetRec (var_abs_lst, c) ->
      let converter (var, abs) = (var, of_abstraction abs) in
      LetRec (List.map converter var_abs_lst, of_computation c)
  | CoreSyntax.Match (e, abs_lst) ->
      let converter abs = ValueClause (of_abstraction abs) in
      Match (of_expression e, List.map converter abs_lst)
  | CoreSyntax.Apply (e1, e2) -> Apply (of_expression e1, of_expression e2)
  | CoreSyntax.Check c -> Check (of_computation c)
  | CoreSyntax.Handle (e, c) ->
      (* Non-trivial case *)
      let modified_handler = of_expression e in
      let thunked_c = Lambda (PNonbinding, of_computation c) in
      Apply (modified_handler, thunked_c)

and of_pattern { it; _ } =
  match it with
  | CoreSyntax.PVar var -> PVar var
  | CoreSyntax.PAnnotated (p, ty) -> PAnnotated (of_pattern p, of_type ty)
  | CoreSyntax.PAs (p, var) -> PAs (of_pattern p, var)
  | CoreSyntax.PTuple ps -> PTuple (List.map of_pattern ps)
  | CoreSyntax.PRecord assoc -> PRecord (Assoc.map of_pattern assoc)
  | CoreSyntax.PVariant (lbl, p_opt) -> (
      match p_opt with
      | None -> PVariant (lbl, None)
      | Some p -> PVariant (lbl, Some (of_pattern p)))
  | CoreSyntax.PConst const -> PConst const
  | CoreSyntax.PNonbinding -> PNonbinding

and of_type = function
  | Type.Apply (name, tys) -> TyApply (name, List.map of_type tys)
  | Type.TyParam ty_param -> TyParam ty_param
  | Type.Basic s -> TyBasic s
  | Type.Tuple tys -> TyTuple (List.map of_type tys)
  | Type.Arrow (ty1, ty2) -> TyArrow (of_type ty1, of_type ty2)
  | Type.Handler { value; finally } ->
      (* Non-trivial case *)
      TyArrow (TyArrow (of_type Type.unit_ty, of_type value), of_type finally)

and of_tydef = function
  | TypeContext.Record assoc -> TyDefRecord (Assoc.map of_type assoc)
  | TypeContext.Sum assoc ->
      let converter = function None -> None | Some ty -> Some (of_type ty) in
      TyDefSum (Assoc.map converter assoc)
  | TypeContext.Inline ty -> TyDefInline (of_type ty)
