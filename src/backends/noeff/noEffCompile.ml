(* 
let compile_type noeff_ty = 
  match noeff_ty with
    | Types.TyParam t -> NoEffSyntax.TyVar t
    | Types.Apply (ty_name, tar_tys) -> 
    | Types.Arrow (tar_ty , tar_dirt) -> NoEffSyntax.Arrow
    | Types.Tuple tar_tys -> 
    | Types.Handler (tar_dirt1, tar_dirt2) -> NoEffSyntax.Handler
    | Types.PrimTy p_ty -> 
    | Types.QualTy (c_ty, tar_ty) -> NoEffSyntax.Qualification
    | Types.QualDirt (c_dirt, tar_ty) -> NoEffSyntax.Qualification
    | Types.TySchemeTy (t, skel, atr_ty) -> NoEffSyntax.Forall
    | Types.TySchemeDirt (d, tar_ty) -> 
    | Types.TySchemeSkel (s, tar_ty) ->  *)
