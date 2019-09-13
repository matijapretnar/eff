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
   if (Types.EffectSet.is_empty dirt.effect_set)  (* if dirt is empty *)
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
    | Typed.Effect (eff, (ty1, ty2)) -> NoEffSyntax.Effect (eff, (compile_type ty1, compile_type ty2))
    | Typed.Handler handler -> 
        if Assoc.is_empty handler.effect_clauses
        then NoEffSyntax.Lambda (compile_value_clause handler.value_clause)
        else compile_handler_with_effects handler
    | Typed.BigLambdaTy (ty_par, skel, expr) -> NoEffSyntax.BigLambdaTy (ty_par, compile_expr expr)
    | Typed.BigLambdaDirt (_, expr) -> compile_expr expr
    | Typed.BigLambdaSkel (_, expr) -> compile_expr expr
    | Typed.CastExp (expr, coer_ty) -> NoEffSyntax.Cast (compile_expr expr, compile_coercion coer_ty)
    | Typed.ApplyTyExp (expr, ty) -> NoEffSyntax.ApplyTy (compile_expr expr, compile_type ty)
    | Typed.LambdaTyCoerVar (coer_param_ty, pi, expr) -> 
        NoEffSyntax.BigLambdaCoerVar (
          coer_param_ty, 
          compile_coercion_type pi, 
          compile_expr expr)
    | Typed.LambdaDirtCoerVar (dirt_coer_param, ct_dirt, expr) -> compile_expr expr
    | Typed.ApplyDirtExp (expr, drt) -> let exeff_ty = TypeChecker.type_of_expression TypeChecker.initial_state expr in 
        (match exeff_ty with 
          | Types.TySchemeDirt (drt_param, _) -> NoEffSyntax.Cast (compile_expr expr, compile_ty_coercion_dirt drt_param drt exeff_ty)
          | _ -> failwith __LOC__)  (* Fail if wrong type *)
    | Typed.ApplySkelExp (expr, skel) -> compile_expr expr
    | Typed.ApplyTyCoercion (expr, ty_coer) -> NoEffSyntax.ApplyCoercion (compile_expr expr, compile_coercion ty_coer)
    | Typed.ApplyDirtCoercion (expr, drt_coer) -> compile_expr expr

and compile_effect (ef, (ty1, ty2)) = (ef, (compile_type ty1, compile_type ty2))

and compile_effect_clauses eff_cls = 
  Assoc.kmap 
    (fun ((ef, (ty1, ty2)), (pat1, pat2, comp)) -> 
      ((ef, (compile_type ty1, compile_type ty2)), 
      (compile_pattern pat1, compile_pattern pat2, compile_comp comp))) 
    eff_cls

and replace_var_with var replacement_term term = 
  match term with
  | NoEffSyntax.Var v -> if (v = var) then replacement_term else NoEffSyntax.Var v
  | NoEffSyntax.BuiltIn (s, i) -> NoEffSyntax.BuiltIn (s, i)
  | NoEffSyntax.Const t -> NoEffSyntax.Const t
  | NoEffSyntax.Tuple ts -> NoEffSyntax.Tuple (List.map (replace_var_with var replacement_term) ts)
  | NoEffSyntax.Record rcrd -> NoEffSyntax.Record (Assoc.map (replace_var_with var replacement_term) rcrd)
  | NoEffSyntax.Variant (l, t) -> NoEffSyntax.Variant (l, replace_var_with var replacement_term t)
  | NoEffSyntax.Lambda (p, ty, t) -> NoEffSyntax.Lambda (p, ty, replace_var_with var replacement_term t)
  | NoEffSyntax.Effect e -> NoEffSyntax.Effect e
  | NoEffSyntax.Apply (t1, t2) -> NoEffSyntax.Apply (replace_var_with var replacement_term t1, replace_var_with var replacement_term t2)
  | NoEffSyntax.BigLambdaTy (p, t) -> NoEffSyntax.BigLambdaTy (p, replace_var_with var replacement_term t)
  | NoEffSyntax.ApplyTy (t, ty) -> NoEffSyntax.ApplyTy (replace_var_with var replacement_term t, ty)
  | NoEffSyntax.BigLambdaCoerVar (p, tyc, t) -> NoEffSyntax.BigLambdaCoerVar (p, tyc, replace_var_with var replacement_term t)
  | NoEffSyntax.ApplyCoercion (t, c) -> NoEffSyntax.ApplyCoercion (replace_var_with var replacement_term t, c)
  | NoEffSyntax.Cast (t, c) -> NoEffSyntax.Cast (replace_var_with var replacement_term t, c)
  | NoEffSyntax.Return t -> NoEffSyntax.Return (replace_var_with var replacement_term t)
  | NoEffSyntax.Handler {effect_clauses=efc; value_clause=(p,ty,t)} -> 
      NoEffSyntax.Handler {effect_clauses=(Assoc.map (fun (p1, p2, t) -> (p1, p2, replace_var_with var replacement_term t)) efc); 
                           value_clause=(p,ty, replace_var_with var replacement_term t)}
  | NoEffSyntax.Let (v, t1, t2) -> NoEffSyntax.Let (v, replace_var_with var replacement_term t1, replace_var_with var replacement_term t2)
  | NoEffSyntax.Call (e, t1, (p, ty, t2)) -> NoEffSyntax.Call (e, replace_var_with var replacement_term t1, (p, ty, replace_var_with var replacement_term t2))
  | NoEffSyntax.Op (e, t) -> NoEffSyntax.Op (e, replace_var_with var replacement_term t)
  | NoEffSyntax.Do (v, t1, t2) -> NoEffSyntax.Do (v, replace_var_with var replacement_term t1, replace_var_with var replacement_term t2)
  | NoEffSyntax.Handle (t1, t2) -> NoEffSyntax.Handle (replace_var_with var replacement_term t1, replace_var_with var replacement_term t2)

and compile_effect_clauses_return eff_cls = 
  Assoc.kmap 
    (fun ((ef, (ty1, ty2)), (pat1, pat2, comp)) -> (match pat2 with
      | Typed.PVar var -> 
        let noEffTy1 = compile_type ty1 in (
        let noEffTy2 = compile_type ty2 in 
          ((ef, (noEffTy1, noEffTy2)), 
          (compile_pattern pat1, 
           compile_pattern pat2, 
           NoEffSyntax.Return (replace_var_with var 
             (NoEffSyntax.Cast (Var var, NoEffSyntax.CoerArrow (ReflTy noEffTy1, Unsafe (ReflTy noEffTy2))))
             (compile_comp comp)))))
      | _ -> failwith __LOC__)) (* Fail if wrong pattern *)
    eff_cls

and compile_value_clause (pat, ty, comp) = (compile_pattern pat, compile_type ty, compile_comp comp)

and compile_value_clause_return (pat, ty, comp) = (compile_pattern pat, compile_type ty, NoEffSyntax.Return (compile_comp comp))

and compile_handler_with_effects {effect_clauses = eff_cls; value_clause = val_cl} = 
  match TypeChecker.type_of_handler TypeChecker.initial_state {effect_clauses = eff_cls; value_clause = val_cl} with
    | Types.Handler (_, (ty, drt)) -> 
      if (Types.EffectSet.is_empty drt.effect_set) 
      then NoEffSyntax.Handler {
        effect_clauses = (compile_effect_clauses_return eff_cls); 
        value_clause = (compile_value_clause_return val_cl)}
      else NoEffSyntax.Handler {effect_clauses = (compile_effect_clauses eff_cls); value_clause = (compile_value_clause val_cl)}
    | _ -> failwith __LOC__ (* Fail if wrong type *)

and compile_coercion exeff_ty_coer = 
  match exeff_ty_coer with
  | Typed.ReflTy ty -> NoEffSyntax.ReflTy (compile_type ty)
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

and compile_ty_coercion_dirt dirt_param dirt exeff_ty = 
  match exeff_ty with
    | Types.TyParam ty_param -> failwith __LOC__
    | Types.Apply (ty_name, tys) -> failwith __LOC__
    | Types.Arrow (ty1, drty2) -> failwith __LOC__
    | Types.Tuple tys -> failwith __LOC__
    | Types.Handler (tyd1, tyd2) -> failwith __LOC__
    | Types.PrimTy ty_const -> failwith __LOC__
    | Types.QualTy (pi, ty) -> failwith __LOC__
    | Types.QualDirt (ct_dirt, ty) -> failwith __LOC__
    | Types.TySchemeTy (ty_param, _, ty) -> failwith __LOC__
    | Types.TySchemeDirt (dirt_param, ty) -> failwith __LOC__
    | Types.TySchemeSkel (skel_param, ty) -> failwith __LOC__

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
