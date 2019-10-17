open NoEffSyntax

let print = Format.fprintf

let print_type formatter noEff_ty = 
  match noEff_ty with
    | TyVar t -> print formatter ""
    | TyApply (tyName, tys) -> print formatter ""
    | TyTuple tys -> print formatter ""
    | TyBasic t -> print formatter ""
    | TyArrow (ty1, ty2) -> print formatter ""
    | TyHandler (ty1, ty2) -> print formatter ""
    | TyForAll (t, ty) -> print formatter ""
    | TyQualification (tyc, ty) -> print formatter ""
    | TyComputation ty -> print formatter ""

let rec print_term formatter noEff_term =
  match noEff_term with
    | Var v -> formatter ""
    | BuiltIn (s, i) -> formatter ""
    | Const c -> formatter ""
    | Tuple ts -> formatter ""
    | Record rcd -> formatter ""
    | Variant (l, t1) -> formatter ""
    | Lambda awty -> formatter ""
    | Effect e -> formatter ""
    | Apply (t1, t2) -> (print_term formatter t1) @ (print_term formatter t2)
    | BigLambdaTy (typ, t) -> formatter ""
    | ApplyTy (t, ty) -> formatter ""
    | BigLambdaCoerVar (tycp, tyc, t) -> formatter ""
    | ApplyTyCoercion (t, c) -> formatter ""
    | Cast (t, c) -> formatter ""
    | Return t -> formatter ""
    | Handler h -> formatter ""
    | LetVal (t1, abs_ty) -> formatter ""
    | LetRec (vs_tys_ts, t2) -> formatter ""
    | Match (t, abs) -> formatter ""
    | Call (e, t, awty) -> formatter ""
    | Op (e, t) -> formatter ""
    | Bind (t, abs) -> formatter ""
    | Do (v, t1, t2) -> formatter ""
    | Handle (t1, t2) -> formatter ""
