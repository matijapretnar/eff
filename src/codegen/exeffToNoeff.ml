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
  (* STIEN: Add int, bool, string, float to NoEff *)
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
