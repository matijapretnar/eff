let rec compile_type exeff_ty = 
  match exeff_ty with
    | Types.TyParam ty_param -> NoEffSyntax.TyVar ty_param
    | Types.Apply (ty_name, tys) -> NoEffSyntax.TyApply ( ty_name, List.map compile_type tys )
    | Types.Arrow (ty1, drty2) -> NoEffSyntax.TyArrow (compile_type ty1, compile_dirty_type drty2)
    | Types.Tuple tys -> NoEffSyntax.TyTuple (List.map compile_type tys)
    | Types.Handler ((ty1, {effect_set=eff_set; row=row}), (ty2, ty_dirt2)) -> 
        if (Types.EffectSet.is_empty eff_set) 
        then NoEffSyntax.TyArrow (compile_type ty1, compile_type ty2) 
        else NoEffSyntax.TyHandler (compile_type ty1, compile_type ty2) 
    | Types.PrimTy ty_const -> NoEffSyntax.TyBasic ty_const
    | Types.QualTy (pi, ty) -> NoEffSyntax.TyQualification (compile_coercion_type pi, compile_type ty)
    | Types.QualDirt (_, ty) -> compile_type ty
    | Types.TySchemeTy (ty_param, _, ty) -> NoEffSyntax.TyForAll (ty_param, compile_type ty)
    | Types.TySchemeDirt (_, ty) -> compile_type ty
    | Types.TySchemeSkel (_, ty) -> compile_type ty

and compile_dirty_type (ty, dirt) =
   if (Types.EffectSet.is_empty dirt.effect_set) (* dirt is empty?*)
   then compile_type ty
   else NoEffSyntax.TyComputation (compile_type ty)

and compile_coercion_type (ty1, ty2) =
    NoEffSyntax.TyCoercion (compile_type ty1, compile_type ty2)

let rec compile_pattern exeff_pat = 
  match exeff_pat with
    | Typed.PVar v -> NoEffSyntax.PVar v
    | Typed.PAs (pat, v) -> NoEffSyntax.PAs (compile_pattern pat, v)
    | Typed.PTuple pats -> NoEffSyntax.PTuple (List.map compile_pattern pats)
    | Typed.PRecord patr -> NoEffSyntax.PRecord (Assoc.map compile_pattern patr)
    | Typed.PVariant (lab, pat) -> NoEffSyntax.PVariant (lab, compile_pattern pat)
    | Typed.PConst c -> NoEffSyntax.PConst c
    | Typed.PNonbinding -> NoEffSyntax.PNonbinding

let rec compile_expr exeff_expr = 
  match exeff_expr with
    | Typed.Var v -> NoEffSyntax.Var v
    | Typed.BuiltIn (s, i) -> NoEffSyntax.BuiltIn (s,i)
    | Typed.Const ct -> NoEffSyntax.Const ct
    | Typed.Tuple lst -> NoEffSyntax.Tuple (List.map compile_expr lst)
    | Typed.Record rcd -> NoEffSyntax.Record (Assoc.map compile_expr rcd)
    | Typed.Variant (label, expr) -> NoEffSyntax.Variant (label, compile_expr expr)
    | Typed.Lambda (pat, ty, comp) -> NoEffSyntax.Lambda (compile_pattern pat, compile_type ty, compile_comp comp)
    | Typed.Effect  (eff, (ty1, ty2)) -> NoEffSyntax.Effect (eff, (compile_type ty1, compile_type ty2))
    | Typed.Handler {effect_clauses = eff_cls; value_clause = (pat, ty, comp)} -> 
        if Assoc.is_empty eff_cls
        then NoEffSyntax.Lambda (compile_pattern pat, compile_type ty, compile_comp comp)
        else failwith __LOC__
    | Typed.BigLambdaTy (ty_par, skel, expr) -> NoEffSyntax.BigLambdaTy (ty_par, compile_expr expr)
    | Typed.BigLambdaDirt (_, expr) -> compile_expr expr
    | Typed.BigLambdaSkel (_, expr) -> compile_expr expr
    | Typed.CastExp (expr, coer_ty) -> NoEffSyntax.Cast (compile_expr expr, compile_ty_coercion coer_ty)
    | Typed.ApplyTyExp (expr, ty) -> NoEffSyntax.ApplyTy (compile_expr expr, compile_type ty)
    | Typed.LambdaTyCoerVar (coer_param_ty, pi, expr) -> 
        NoEffSyntax.BigLambdaCoerVar (
          coer_param_ty, 
          compile_coercion_type pi, 
          compile_expr expr)
    | Typed.LambdaDirtCoerVar (dirt_coer_param, ct_dirt, expr) -> compile_expr expr
    | Typed.ApplyDirtExp (expr, drt) -> failwith __LOC__
    | Typed.ApplySkelExp (expr, skel) -> compile_expr expr
    | Typed.ApplyTyCoercion (expr, ty_coer) -> NoEffSyntax.ApplyCoercion (compile_expr expr, compile_ty_coercion ty_coer)
    | Typed.ApplyDirtCoercion (expr, drt_coer) -> compile_expr expr

and compile_ty_coercion exeff_ty_coer = 
  match exeff_ty_coer with
  | Typed.ReflTy ty -> failwith __LOC__
  | Typed.ArrowCoercion (ty_coer, drt_coer) -> failwith __LOC__
  | Typed.HandlerCoercion (drt_coer1, drt_coer2) -> failwith __LOC__
  | Typed.TyCoercionVar ty_coer_param -> failwith __LOC__
  | Typed.SequenceTyCoer (ty_coer1, ty_coer2) -> failwith __LOC__
  | Typed.ApplyCoercion (ty_name, ty_coers) -> failwith __LOC__
  | Typed.TupleCoercion (ty_coers) -> failwith __LOC__
  | Typed.LeftArrow ty_coerc -> failwith __LOC__
  | Typed.ForallTy (ty_param, ty_coer) -> failwith __LOC__
  | Typed.ApplyTyCoer (ty_coer, ty) -> failwith __LOC__
  | Typed.ForallDirt (drt_param, ty_coer) -> failwith __LOC__
  | Typed.ApplyDirCoer (ty_coer, drt) -> failwith __LOC__
  | Typed.PureCoercion drt_coer -> failwith __LOC__
  | Typed.QualTyCoer (ct_ty, ty_coer) -> failwith __LOC__
  | Typed.QualDirtCoer (ct_drt, ty_coer) -> failwith __LOC__
  | Typed.ApplyQualTyCoer (ty_coer1, ty_coer2) -> failwith __LOC__
  | Typed.ApplyQualDirtCoer (ty_coer, drt_coer) -> failwith __LOC__
  | Typed.ForallSkel (skel_param, ty_coer) -> failwith __LOC__
  | Typed.ApplySkelCoer (ty_coer, skel) -> failwith __LOC__

and compile_comp exeff_comp = 
  match exeff_comp with
    | Typed.Value expr -> compile_expr expr
    | Typed.LetVal (expr, (pat, ty, comp)) -> failwith __LOC__
    | Typed.LetRec (lst, comp) -> failwith __LOC__
    | Typed.Match (expr, abs) -> failwith __LOC__
    | Typed.Apply (expr1, expr2) -> NoEffSyntax.Apply (compile_expr expr1, compile_expr expr2)
    | Typed.Handle (expr, comp) -> failwith __LOC__
    | Typed.Call (eff, expr, abs_ty) -> failwith __LOC__
    | Typed.Op ((eff,(ty1,ty2)), expr) -> NoEffSyntax.Op ((eff, (compile_type ty1, compile_type ty2)), compile_expr expr)
    | Typed.Bind (comp, abs) -> failwith __LOC__
    | Typed.CastComp (comp, drty_coer) -> failwith __LOC__
    | Typed.CastComp_ty (comp, ty_coer) -> failwith __LOC__
    | Typed.CastComp_dirt (comp, drt_coer) -> failwith __LOC__
