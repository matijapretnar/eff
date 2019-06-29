let compile_type exeff_ty = 
  match exeff_ty with
    | Types.Arrow (ty, ty_d) -> NoEffSyntax.TyUnit
