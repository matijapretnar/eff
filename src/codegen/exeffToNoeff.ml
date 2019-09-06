open NoEffSyntax
open Types
open Typed

module NoEff = NoEffSyntax
module ExEffTypes = Types
module ExEff = Typed
module EffectSet = Set.Make (CoreTypes.Effect)

type effect_set = EffectSet.t

let rec type_elab ty =
  match ty with
  | ExEffTypes.TyParam x -> NoEff.NTyParam x
  | ExEffTypes.Apply (name, lst) -> NoEff.NTyApply (name, List.map type_elab lst)
  | ExEffTypes.Arrow (ty, dirty) -> NoEff.NTyArrow (type_elab ty, dirty_elab dirty)
  | ExEffTypes.Handler ((type1, dirt1), dirty) ->
    if (EffectSet.is_empty (dirt1.effect_set) && (dirt1.row = ExEffTypes.EmptyRow))
    then NoEff.NTyArrow ( (type_elab type1), (dirty_elab dirty) )
    else NoEff.NTyHandler ( (dirty_elab (type1, dirt1)), (dirty_elab dirty) )
  | ExEffTypes.Tuple tys -> NoEff.NTyTuple (List.map type_elab tys)
  | ExEffTypes.QualTy ( (t1, t2), ty) ->
    NoEff.NTyQual ( (type_elab t1, type_elab t2), type_elab ty)
  | ExEffTypes.QualDirt (_, ty) -> type_elab ty
  | ExEffTypes.TySchemeTy (par, skel, ty) -> NoEff.NTyForall (par, type_elab ty)
  | ExEffTypes.TySchemeDirt (par, ty) -> type_elab ty
  | ExEffTypes.TySchemeSkel (par, ty) -> type_elab ty
  | ExEffTypes.PrimTy ty ->
    match ty with
    | ExEffTypes.IntTy -> NoEff.NTyPrim NInt
    | ExEffTypes.BoolTy -> NoEff.NTyPrim NBool
    | ExEffTypes.StringTy -> NoEff.NTyPrim NString
    | ExEffTypes.FloatTy -> NoEff.NTyPrim NFloat

and dirty_elab (ty, dirt) =
  if ( (EffectSet.is_empty dirt.effect_set) && (dirt.row = ExEffTypes.EmptyRow) )
  then type_elab ty
  else NoEff.NTyComp (type_elab ty)

and pattern_elab p =
  match p with
  | PVar x -> NVar x
  | PAs (p, x) -> NAs (pattern_elab p, x)
  | PTuple ps -> NTuple (List.map pattern_elab ps)
  | PConst c -> NConst c
  | PNonbinding -> NNonBinding

and value_elab v =
  match v with
  | ExEff.Var x -> NoEff.NVar x
  | ExEff.BuiltIn (s, i) -> NoEff.NBuiltIn (s, i)
  | ExEff.Const c -> NoEff.NConst c
  | ExEff.Tuple vs -> NoEff.NTuple (List.map value_elab vs)
  | ExEff.Lambda (p, t, c) -> NoEff.NFun (pattern_elab p, type_elab t, comp_elab c)
  | ExEff.Effect (e, _) -> NoEff.NEffect e
  | ExEff.Handler h ->
      let (p, t, c) = h.value_clause in
      let elab_effect_clause ((eff, _), (p1, p2, comp)) = (eff, (pattern_elab p1, pattern_elab p2, comp_elab comp)) in
      {return_clause= (pattern_elab p, type_elab t, comp_elab c);
	effect_clauses= List.map elab_effect_clause h.effect_clauses}

and comp_elab c = failwith "TODO"
