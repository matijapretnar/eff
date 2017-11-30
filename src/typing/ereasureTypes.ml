type e_ty = 
  | ETyvar of Params.e_ty_param
  | Arrow of e_ty * e_ty
  | Tuple of e_ty list
  | Handler of e_ty * e_ty
  | PrimTy of prim_ty
  | TySchemeTy of Params.e_ty_param  * e_ty

 and 
 prim_ty =
 | IntTy
 | BoolTy
 | StringTy
 | FloatTy