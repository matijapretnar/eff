open CoreUtils
module SkelEff = SkelEffSyntax
module Multicore = MulticoreSyntax

(* Abstractions *)
let rec of_abstraction (p, c) = (of_pattern p, of_computation c)

and of_abstraction2 (p1, p2, c) =
  (of_pattern p1, of_pattern p2, of_computation c)

and of_abstraction_with_ty (p, _, c) = of_abstraction (p, c)

(* Patterns *)
and of_pattern : SkelEff.e_pattern -> Multicore.pattern = function
  | SkelEff.PEVar v -> Multicore.PVar v
  | SkelEff.PEAs (p, v) -> Multicore.PAs (of_pattern p, v)
  | SkelEff.PETuple ps -> Multicore.PTuple (List.map of_pattern ps)
  | SkelEff.PERecord ass -> Multicore.PRecord (Assoc.map of_pattern ass)
  | SkelEff.PEVariant (l, p) -> Multicore.PVariant (l, Some (of_pattern p))
  | SkelEff.PEConst c -> Multicore.PConst c
  | SkelEff.PENonbinding -> Multicore.PNonbinding

(* Expressions (-> Terms in the Multicore syntax) *)
and of_expression : SkelEff.e_expression -> Multicore.term = function
  | SkelEff.EVar v -> Multicore.Var v
  | SkelEff.EConst c -> Multicore.Const c
  | SkelEff.ETuple es -> Multicore.Tuple (List.map of_expression es)
  | SkelEff.ERecord ass -> Multicore.Record (Assoc.map of_expression ass)
  | SkelEff.EVariant (l, e) -> (
      match e with
      | None -> Multicore.Variant (l, None)
      | Some e -> Multicore.Variant (l, Some (of_expression e)))
  | SkelEff.ELambda abs -> Multicore.Lambda (of_abstraction_with_ty abs)
  | SkelEff.EEffect (e, _) -> Multicore.Effect e
  | SkelEff.EHandler { effect_clauses; value_clause } ->
      let effect_clauses' =
        List.map
          (fun ((eff, _), abs) ->
            Multicore.EffectClause (eff, of_abstraction2 abs))
          (Assoc.to_list effect_clauses)
      in
      let value_clause' =
        Multicore.ValueClause (of_abstraction_with_ty value_clause)
      in
      let ghost_bind = CoreTypes.Variable.fresh "$c_thunk" in
      let match_handler =
        Multicore.Match
          ( Multicore.Apply (Multicore.Var ghost_bind, Multicore.Tuple []),
            value_clause' :: effect_clauses' )
      in
      Multicore.Lambda (Multicore.PVar ghost_bind, match_handler)
  | SkelEff.EBigLambdaSkel (_, e) -> of_expression e
  | SkelEff.EApplySkelExp (e, _) -> of_expression e

(* Computations (-> Terms in the Multicore syntax) *)
and of_computation : SkelEff.e_computation -> Multicore.term = function
  | SkelEff.EValue e -> of_expression e
  | SkelEff.ELetVal (p, e, c) ->
      Multicore.Let ([ (of_pattern p, of_expression e) ], of_computation c)
  | SkelEff.EApply (e1, e2) ->
      Multicore.Apply (of_expression e1, of_expression e2)
  | SkelEff.EHandle (e, c) ->
      let handler' = of_expression e in
      let abs = Multicore.Lambda (Multicore.PNonbinding, of_computation c) in
      Multicore.Apply (handler', abs)
  | SkelEff.ECall (eff, exp, abs) -> failwith "SkelEff call"
  | SkelEff.EBind (c, abs) ->
      Multicore.Apply (Multicore.Lambda (of_abstraction abs), of_computation c)
      (* Meh? *)
  | SkelEff.EMatch (e, sk, abs_list, loc) ->
      let converter abs = Multicore.ValueClause (of_abstraction abs) in
      Multicore.Match (of_expression e, List.map converter abs_list)
  | SkelEff.ELetRec (abs_list, c) ->
      let converter (var, _, _, abs) = (var, of_abstraction abs) in
      Multicore.LetRec (List.map converter abs_list, of_computation c)

(* Types *)
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

(* Type definitions *)
and of_tydef = function
  | TypeContext.Record assoc -> Multicore.TyDefRecord (Assoc.map of_type assoc)
  | TypeContext.Sum assoc ->
      let converter = function None -> None | Some ty -> Some (of_type ty) in
      Multicore.TyDefSum (Assoc.map converter assoc)
  | TypeContext.Inline ty -> Multicore.TyDefInline (of_type ty)
