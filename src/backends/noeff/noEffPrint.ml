open NoEffSyntax

let print_type formatter noEff_ty = 
  match noEff_ty with
    | TyVar t -> formatter ""
    | TyUnit -> formatter "unit"
    | TyBasic t -> formatter ""
    | TyArrow (ty1, ty2) -> formatter ""
    | TyHandler (ty1, ty2) -> formatter ""
    | TyForAll (t, ty) -> formatter ""
    | TyQualification (tyc, ty) -> formatter ""
    | TyComputation ty -> formatter ""

let rec print_term formatter noEff_term =
  match noEff_term with
    | Var v -> formatter ""
    | Unit -> formatter ""
    | Lambda awty -> formatter ""
    | Apply (t1, t2) -> (print_term formatter t1) @ (print_term formatter t2)
    | BigLambdaTy (typ, t) -> formatter ""
    | ApplyTy (t, ty) -> formatter ""
    | BigLambdaCoerVar (tycp, tyc, t) -> formatter ""
    | ApplyCoercion (t, c) -> formatter ""
    | Cast (t, c) -> formatter ""
    | Return t -> formatter ""
    | Handler h -> formatter ""
    | Let (v, t1, t2) -> formatter ""
    | Call (e, t, awty) -> formatter ""
    | Do (v, t1, t2) -> formatter ""
    | Handle (t1, t2) -> formatter ""
