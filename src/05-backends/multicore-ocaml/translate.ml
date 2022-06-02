open Utils
open Language
open Syntax

(* ------------------------------------------------------------------------ *)
(* Translations *)

let rec of_abstraction { term = p, c; _ } = (of_pattern p, of_computation c)

and of_abstraction2 { term = p1, p2, c; _ } =
  (of_pattern p1, of_pattern p2, of_computation c)

(** Conversion functions. *)
and of_expression exp =
  match exp.term with
  | Term.Var v -> Var v.variable
  | Term.Const const -> Const const
  | Term.Tuple es -> Tuple (List.map of_expression es)
  | Term.Record assoc -> Record (Type.Field.Map.map of_expression assoc)
  | Term.Variant (lbl, e_opt) -> (
      match e_opt with
      | None -> Variant (lbl, None)
      | Some e -> Variant (lbl, Some (of_expression e)))
  | Term.Lambda abs -> (
      (* Transform back to [function] keyword if possible *)
      match abs.term with
      | p, { term = Term.Match (e, abs_lst); _ } -> (
          let p' = of_pattern p in
          let e' = of_expression e in
          match (p', e') with
          | PVar v1, Var v2
            when v1 = v2
                 && Term.Variable.fold (fun desc _ -> desc = "$function") v1 ->
              let converter abs = ValueClause (of_abstraction abs) in
              Function (List.map converter abs_lst)
          | _ -> Lambda (of_abstraction abs))
      | _ -> Lambda (of_abstraction abs))
  | Term.Handler h -> of_handler h None
  | Term.HandlerWithFinally h ->
      of_handler h.handler_clauses (Some h.finally_clause)
  | Term.CastExp (exp, _) -> of_expression exp

and of_handler
    ({ term = { value_clause; effect_clauses = { effect_part; _ } }; _ } :
      Term.handler_clauses) finally_clause =
  (* Non-trivial case *)
  let effect_clauses' =
    List.map
      (fun (eff, abs) -> EffectClause (eff.term, of_abstraction2 abs))
      (Assoc.to_list effect_part)
  in
  let value_clause' = ValueClause (of_abstraction value_clause) in
  let ghost_bind = Term.Variable.fresh "$c_thunk" in
  let match_handler =
    Match (Apply (Var ghost_bind, Tuple []), value_clause' :: effect_clauses')
  in
  match finally_clause with
  | None -> Lambda (PVar ghost_bind, match_handler)
  | Some fin ->
      let p_fin, c_fin = of_abstraction fin in
      Lambda (PVar ghost_bind, Let ([ (p_fin, match_handler) ], c_fin))

and of_computation cmp =
  match cmp.term with
  | Term.Value e -> of_expression e
  | Term.LetVal (e, a) ->
      let p, c = of_abstraction a in
      Let ([ (p, of_expression e) ], c)
  | Term.Bind (c1, a) ->
      let p, c2 = of_abstraction a in
      Let ([ (p, of_computation c1) ], c2)
  | Term.LetRec (var_abs_lst, c) ->
      let converter (var, abs) = (var, of_abstraction abs) in
      LetRec (List.map converter (Assoc.to_list var_abs_lst), of_computation c)
  | Term.Match (e, abs_lst) ->
      let converter abs = ValueClause (of_abstraction abs) in
      Match (of_expression e, List.map converter abs_lst)
  | Term.Apply (e1, e2) -> Apply (of_expression e1, of_expression e2)
  | Term.Handle (e, c) ->
      (* Non-trivial case *)
      let modified_handler = of_expression e in
      let thunked_c = Lambda (PNonbinding, of_computation c) in
      Apply (modified_handler, thunked_c)
  | Term.Call (eff, e, a) ->
      let p, c = of_abstraction a in
      Let ([ (p, Apply (Effect eff.term, of_expression e)) ], c)
  | Term.CastComp (c, _) -> of_computation c
  | Term.Check (_, c) -> Check (of_computation c)

and of_pattern pat =
  match pat.term with
  | Term.PVar var -> PVar var
  | Term.PAs (p, var) -> PAs (of_pattern p, var)
  | Term.PTuple ps -> PTuple (List.map of_pattern ps)
  | Term.PRecord assoc -> PRecord (Type.Field.Map.map of_pattern assoc)
  | Term.PVariant (lbl, p_opt) -> (
      match p_opt with
      | None -> PVariant (lbl, None)
      | Some p -> PVariant (lbl, Some (of_pattern p)))
  | Term.PConst const -> PConst const
  | Term.PNonbinding -> PNonbinding

and of_type ty =
  match ty.term with
  | Type.Apply { ty_name; ty_args } ->
      TyApply
        ( ty_name,
          List.map of_type
            (ty_args |> TyParam.TyParam.Map.values |> List.map fst) )
  | Type.TyParam ty_param -> TyParam ty_param
  | Type.TyBasic s -> TyBasic s
  | Type.Tuple tys -> TyTuple (List.map of_type tys)
  | Type.Arrow (ty1, ty2) -> TyArrow (of_type ty1, of_dirty ty2)
  | Type.Handler (drty1, drty2) ->
      (* Non-trivial case *)
      TyArrow (TyArrow (of_type Type.unit_ty, of_dirty drty1), of_dirty drty2)

and of_dirty (ty, _) = of_type ty

and of_tydef = function
  | Type.Record assoc -> TyDefRecord (Type.Field.Map.map of_type assoc)
  | Type.Sum assoc ->
      let converter = function None -> None | Some ty -> Some (of_type ty) in
      TyDefSum (Type.Field.Map.map converter assoc)
  | Type.Inline ty -> TyDefInline (of_type ty)
