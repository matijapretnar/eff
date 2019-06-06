open NoEffSyntax

let print_type formatter noEff_ty = 
  match noEff_ty with
    | TyVar t -> formatter ""
    | Unit -> formatter "unit"
    | Arrow (ty1, ty2) -> formatter ""
    | Handler (ty1, ty2) -> formatter ""
(*     | ForAll of CoreTypes.TyParam.t * ty
    | Qualification of ty_coercion * ty
    | Computation of ty *)