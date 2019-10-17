let is_dirt_empty (dirt : Types.dirt) = match dirt.row with 
  | Types.EmptyRow -> Types.EffectSet.is_empty dirt.effect_set
  | Types.ParamRow _ -> false

let rec substitute_var_in_term var replacement_term term = 
  match term with
  | NoEffSyntax.Var v -> if (v = var) then replacement_term else NoEffSyntax.Var v
  | NoEffSyntax.BuiltIn (s, i) -> NoEffSyntax.BuiltIn (s, i)
  | NoEffSyntax.Const t -> NoEffSyntax.Const t
  | NoEffSyntax.Tuple ts -> NoEffSyntax.Tuple (List.map (substitute_var_in_term var replacement_term) ts)
  | NoEffSyntax.Record rcrd -> NoEffSyntax.Record (Assoc.map (substitute_var_in_term var replacement_term) rcrd)
  | NoEffSyntax.Variant (l, t) -> NoEffSyntax.Variant (l, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Lambda (p, ty, t) -> NoEffSyntax.Lambda (p, ty, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Effect e -> NoEffSyntax.Effect e
  | NoEffSyntax.Apply (t1, t2) -> NoEffSyntax.Apply (substitute_var_in_term var replacement_term t1, substitute_var_in_term var replacement_term t2)
  | NoEffSyntax.BigLambdaTy (p, t) -> NoEffSyntax.BigLambdaTy (p, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.ApplyTy (t, ty) -> NoEffSyntax.ApplyTy (substitute_var_in_term var replacement_term t, ty)
  | NoEffSyntax.BigLambdaCoerVar (p, tyc, t) -> NoEffSyntax.BigLambdaCoerVar (p, tyc, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.ApplyTyCoercion (t, c) -> NoEffSyntax.ApplyTyCoercion (substitute_var_in_term var replacement_term t, c)
  | NoEffSyntax.Cast (t, c) -> NoEffSyntax.Cast (substitute_var_in_term var replacement_term t, c)
  | NoEffSyntax.Return t -> NoEffSyntax.Return (substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Handler {effect_clauses=efc; value_clause=(p,ty,t)} -> 
      NoEffSyntax.Handler {effect_clauses=(Assoc.map (fun (p1, p2, t) -> (p1, p2, substitute_var_in_term var replacement_term t)) efc); 
                           value_clause=(p,ty, substitute_var_in_term var replacement_term t)}
  | NoEffSyntax.LetVal (t1, (pat, ty, t2)) -> NoEffSyntax.LetVal (substitute_var_in_term var replacement_term t1, (pat, ty, substitute_var_in_term var replacement_term t2))
  | NoEffSyntax.LetRec (var_ty_term_list, t2) -> 
      NoEffSyntax.LetRec (List.map (fun (var, ty, t1) -> (var, ty, substitute_var_in_term var replacement_term t1)) var_ty_term_list, substitute_var_in_term var replacement_term t2)
  | NoEffSyntax.Match (t1, abs_lst) -> NoEffSyntax.Match (substitute_var_in_term var replacement_term t1, (List.map (fun (pat, t2) -> (pat, substitute_var_in_term var replacement_term t2))  abs_lst))
  | NoEffSyntax.Call (e, t1, (p, ty, t2)) -> NoEffSyntax.Call (e, substitute_var_in_term var replacement_term t1, (p, ty, substitute_var_in_term var replacement_term t2))
  | NoEffSyntax.Op (e, t) -> NoEffSyntax.Op (e, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Bind (t1, (pat, t2)) -> NoEffSyntax.Bind (substitute_var_in_term var replacement_term t1, (pat, substitute_var_in_term var replacement_term t2))
  | NoEffSyntax.Do (v, t1, t2) -> NoEffSyntax.Do (v, substitute_var_in_term var replacement_term t1, substitute_var_in_term var replacement_term t2)
  | NoEffSyntax.Handle (t1, t2) -> NoEffSyntax.Handle (substitute_var_in_term var replacement_term t1, substitute_var_in_term var replacement_term t2)

let rec compile_type exeff_ty = 
  match exeff_ty with
    | Types.TyParam ty_param -> NoEffSyntax.TyVar ty_param
    | Types.Apply (ty_name, tys) -> NoEffSyntax.TyApply (ty_name, List.map compile_type tys)
    | Types.Arrow (ty1, drty2) -> NoEffSyntax.TyArrow (compile_type ty1, compile_dirty_type drty2)
    | Types.Tuple tys -> NoEffSyntax.TyTuple (List.map compile_type tys)
    | Types.Handler ((ty1, ty_dirt1), (ty2, ty_dirt2)) -> 
        if is_dirt_empty ty_dirt1
        then NoEffSyntax.TyArrow (compile_type ty1, compile_type ty2) 
        else NoEffSyntax.TyHandler (compile_type ty1, compile_type ty2) 
    | Types.PrimTy ty_const -> NoEffSyntax.TyBasic ty_const
    | Types.QualTy (pi, ty) -> NoEffSyntax.TyQualification (compile_coercion_type pi, compile_type ty)
    | Types.QualDirt (_, ty) -> compile_type ty
    | Types.TySchemeTy (ty_param, _, ty) -> NoEffSyntax.TyForAll (ty_param, compile_type ty)
    | Types.TySchemeDirt (_, ty) -> compile_type ty
    | Types.TySchemeSkel (_, ty) -> compile_type ty

and compile_dirty_type (ty, dirt) =
   if is_dirt_empty dirt
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

let rec fun_apply_dirty_coercion bang_fun sequence_fun exeff_dirty_coer = 
  match exeff_dirty_coer with
  | Typed.BangCoercion (ty_coer, drt_coer) -> bang_fun ty_coer drt_coer
  | Typed.RightArrow ty_coer -> (match ty_coer with
      | Typed.ArrowCoercion (_, dirty_coer1) -> fun_apply_dirty_coercion bang_fun sequence_fun dirty_coer1 (* is this ok? *)
      | _ -> assert false)
  | Typed.RightHandler ty_coer -> (match ty_coer with
      | Typed.HandlerCoercion (_, dirty_coer2) -> fun_apply_dirty_coercion bang_fun sequence_fun dirty_coer2 (* is this ok? *)
      | _ -> assert false)
  | Typed.LeftHandler ty_coer -> (match ty_coer with
      | Typed.HandlerCoercion (dirty_coer1, _) -> fun_apply_dirty_coercion bang_fun sequence_fun dirty_coer1 (* is this ok? *)
      | _ -> assert false)
  | Typed.SequenceDirtyCoer (drt_coer1, drt_coer2) ->
      let t1, t2 = TypeChecker.type_of_dirty_coercion TypeChecker.initial_state drt_coer1 in 
      let t3, t4 = TypeChecker.type_of_dirty_coercion TypeChecker.initial_state drt_coer2 in 
      assert (t2 = t3); (* is this ok? *)
      sequence_fun drt_coer1 drt_coer2

let compile_effect (ef, (ty1, ty2)) = (ef, (compile_type ty1, compile_type ty2))

let rec compile_coercion exeff_ty_coer = 
  match exeff_ty_coer with
  | Typed.ReflTy ty -> NoEffSyntax.ReflTy (compile_type ty)
  | Typed.ArrowCoercion (ty_coer, drt_coer) -> NoEffSyntax.CoerArrow (compile_coercion ty_coer, compile_dirty_coercion drt_coer)
  | Typed.HandlerCoercion (drt_coer1, drt_coer2) -> 
      let ((ty1_dc1, dr1_dc1), (ty2_dc1, dr2_dc1)) = TypeChecker.type_of_dirty_coercion TypeChecker.initial_state drt_coer1 in 
      if is_dirt_empty dr2_dc1
      (* first rule *)
      then NoEffSyntax.CoerArrow (compile_dirty_coercion drt_coer1, compile_dirty_coercion drt_coer2)
      else (let ((ty1_dc2, dr1_dc2), (ty2_dc2, dr2_dc2)) = TypeChecker.type_of_dirty_coercion TypeChecker.initial_state drt_coer2 in 
        if is_dirt_empty dr1_dc1
        then (
          if is_dirt_empty dr1_dc2 (* third and fourth coercion elaboration rule -- delta1 non-empty, delta2 empty *)
          (* third rule *)
          then NoEffSyntax.HandToFun (compile_ty_coer_from_dirty_coer drt_coer1, NoEffSyntax.Unsafe (compile_dirty_coercion drt_coer2))
          (* fourth rule *)
          else NoEffSyntax.HandToFun (compile_ty_coer_from_dirty_coer drt_coer1, compile_dirty_coercion drt_coer2)
        ) 
        (* second rule *)
        else NoEffSyntax.CoerHandler (compile_dirty_coercion drt_coer1, NoEffSyntax.CoerComputation (compile_ty_coer_from_dirty_coer drt_coer2)))
  | Typed.TyCoercionVar ty_coer_param -> NoEffSyntax.CoerVar ty_coer_param
  | Typed.SequenceTyCoer (ty_coer1, ty_coer2) -> NoEffSyntax.SequenceCoercion (compile_coercion ty_coer1, compile_coercion ty_coer2)
  | Typed.ApplyCoercion (ty_name, ty_coers) -> NoEffSyntax.ApplyCoercion (ty_name, List.map (fun coer -> compile_coercion coer) ty_coers)
  | Typed.TupleCoercion ty_coers -> NoEffSyntax.TupleCoercion (List.map (fun coer -> compile_coercion coer) ty_coers)
  | Typed.LeftArrow ty_coer -> (
      match ty_coer with
        | Typed.ArrowCoercion (ty_coer1, _) -> compile_coercion ty_coer1
        | _ -> assert false)
  | Typed.ForallTy (ty_param, ty_coer) -> NoEffSyntax.Forall (ty_param, compile_coercion ty_coer)
  | Typed.ApplyTyCoer (ty_coer, ty) -> NoEffSyntax.ApplyTyCoer (compile_coercion ty_coer, compile_type ty)
  | Typed.ForallDirt (_, ty_coer) -> compile_coercion ty_coer
  | Typed.ApplyDirCoer (ty_coer1, drt) -> (
      match ty_coer1 with
        | Typed.ForallDirt (p, ty_coer2) -> 
            compile_coercion (Substitution.apply_substitutions_to_tycoer (Substitution.add_dirt_substitution_e p drt) ty_coer2)
        | _ -> assert false)   
  | Typed.PureCoercion drt_coer -> compile_ty_coer_from_dirty_coer drt_coer
  | Typed.QualTyCoer (ct_ty, ty_coer) -> NoEffSyntax.CoerQualification (compile_coercion_type ct_ty, compile_coercion ty_coer)
  | Typed.QualDirtCoer (ct_drt, ty_coer) -> compile_coercion ty_coer (* ni pravila za computation? *)
  | Typed.ApplyQualTyCoer (ty_coer1, ty_coer2) -> NoEffSyntax.ApplyQualTyCoer (compile_coercion ty_coer1, compile_coercion ty_coer2)
  | Typed.ApplyQualDirtCoer (ty_coer, drt_coer) -> failwith __LOC__ (* kaj tukaj? compile_coercion ty_coer? *)
  | Typed.ForallSkel (skel_param, ty_coer) -> compile_coercion ty_coer
  | Typed.ApplySkelCoer (ty_coer1, skel) ->
      (match ty_coer1 with
        | Typed.ForallSkel (s, ty_coer2) -> 
            compile_coercion (Substitution.apply_substitutions_to_tycoer (Substitution.add_skel_param_substitution_e s skel) ty_coer2)
        | _ -> assert false)

and compile_dirty_coercion exeff_dirty_coer = fun_apply_dirty_coercion 
  (fun ty_coer drt_coer ->
    let compiled_ty_coer = compile_coercion ty_coer in
    let (d1, d2) = TypeChecker.type_of_dirt_coercion TypeChecker.initial_state drt_coer in 
      if is_dirt_empty d2
      then compiled_ty_coer
      else (
        if is_dirt_empty d1
        then NoEffSyntax.CoerReturn compiled_ty_coer
        else NoEffSyntax.CoerComputation compiled_ty_coer)) 
  (fun drt_coer1 drt_coer2 -> NoEffSyntax.SequenceCoercion (compile_dirty_coercion drt_coer1, compile_dirty_coercion drt_coer2))
  exeff_dirty_coer

and compile_ty_coer_from_dirty_coer exeff_dirty_coer = 
  fun_apply_dirty_coercion 
    (fun ty_coer drt_coer -> compile_coercion ty_coer) 
    (fun drt_coer1 drt_coer2 -> NoEffSyntax.SequenceCoercion (compile_ty_coer_from_dirty_coer drt_coer1, compile_ty_coer_from_dirty_coer drt_coer2))
    exeff_dirty_coer

let rec value_coercion_from_impure_dirt dirt_param dirt ty = 
  match ty with
    | Types.TyParam ty_param -> NoEffSyntax.ReflTy (compile_type (Types.TyParam ty_param))
    | Types.Apply (ty_name, tys) -> NoEffSyntax.ReflTy (compile_type (Types.Apply (ty_name, tys)))
    | Types.Arrow (ty1, drty2) -> 
        NoEffSyntax.CoerArrow (value_coercion_to_impure_dirt dirt dirt_param ty1, computation_coercion_from_impure_dirt dirt_param dirt drty2)
    | Types.Tuple tys -> NoEffSyntax.TupleCoercion (List.map (value_coercion_from_impure_dirt dirt_param dirt) tys)
    | Types.Handler ((ty1, drt1), (ty2, drt2)) -> 
        if is_dirt_empty drt1
        then NoEffSyntax.CoerArrow (value_coercion_to_impure_dirt dirt dirt_param ty1, computation_coercion_from_impure_dirt dirt_param dirt (ty2, drt2))
        else (match drt1.row with
          | ParamRow d -> (
              if d = dirt_param && Types.EffectSet.is_empty drt1.effect_set && is_dirt_empty dirt 
              then 
                let coer1 = value_coercion_to_impure_dirt dirt dirt_param ty1 in
                let coer2 = value_coercion_from_impure_dirt dirt_param dirt ty2 in (
                if is_dirt_empty (Substitution.apply_substitutions_to_dirt (Substitution.add_dirt_substitution_e dirt_param dirt) drt2)
                then NoEffSyntax.HandToFun (coer1, NoEffSyntax.Unsafe coer2)
                else NoEffSyntax.HandToFun (coer1, NoEffSyntax.CoerComputation coer2)) 
              else NoEffSyntax.CoerHandler (
              computation_coercion_to_impure_dirt dirt dirt_param (ty1, drt1), 
              computation_coercion_from_impure_dirt dirt_param dirt (ty2, Types.fresh_dirt ())))
          | EmptyRow -> NoEffSyntax.CoerHandler (
              computation_coercion_to_impure_dirt dirt dirt_param (ty1, drt1), 
              computation_coercion_from_impure_dirt dirt_param dirt (ty2, Types.fresh_dirt ())))
    | Types.PrimTy ty_const -> NoEffSyntax.ReflTy (compile_type (Types.PrimTy ty_const))
    | Types.QualTy ((Types.TyParam a1, Types.TyParam a2), ty2) -> 
        NoEffSyntax.CoerQualification (NoEffSyntax.TyCoercion (NoEffSyntax.TyVar a1, NoEffSyntax.TyVar a2), value_coercion_from_impure_dirt dirt_param dirt ty2)
    | Types.QualTy _ -> assert false (* not type parameters *)
    | Types.QualDirt (_, ty2) -> value_coercion_from_impure_dirt dirt_param dirt ty2
    | Types.TySchemeTy (ty_param, _, ty2) -> NoEffSyntax.Forall (ty_param, value_coercion_from_impure_dirt dirt_param dirt ty2)
    | Types.TySchemeDirt (_, ty2) -> value_coercion_from_impure_dirt dirt_param dirt ty2
    | Types.TySchemeSkel (_, ty2) -> value_coercion_from_impure_dirt dirt_param dirt ty2

and computation_coercion_from_impure_dirt dirt_param dirt (ty1, d1) = 
  let noeff_coer = value_coercion_from_impure_dirt dirt_param dirt ty1 in
  let computation_coercion_case = 
    if is_dirt_empty (Substitution.apply_substitutions_to_dirt (Substitution.add_dirt_substitution_e dirt_param dirt) d1)
    then assert false (* no rule applicable *)
    else NoEffSyntax.CoerComputation noeff_coer in
  if is_dirt_empty d1
  then noeff_coer
  else match d1.row with
    | ParamRow p -> (
        if p = dirt_param && is_dirt_empty dirt
        then NoEffSyntax.Unsafe noeff_coer
        else computation_coercion_case)
    | EmptyRow -> computation_coercion_case

and value_coercion_to_impure_dirt dirt dirt_param ty =
  match ty with
    | Types.TyParam ty_param -> NoEffSyntax.ReflTy (compile_type (Types.TyParam ty_param))
    | Types.Apply (ty_name, tys) -> NoEffSyntax.ReflTy (compile_type (Types.Apply (ty_name, tys)))
    | Types.Arrow (ty1, drty2) -> 
        NoEffSyntax.CoerArrow (value_coercion_from_impure_dirt dirt_param dirt ty1, computation_coercion_to_impure_dirt dirt dirt_param drty2)
    | Types.Tuple tys -> NoEffSyntax.TupleCoercion (List.map (value_coercion_to_impure_dirt dirt dirt_param) tys)
    | Types.Handler ((ty1, drt1), (ty2, drt2)) -> 
        if is_dirt_empty drt1
        then NoEffSyntax.CoerArrow (value_coercion_from_impure_dirt dirt_param dirt ty1, computation_coercion_to_impure_dirt dirt dirt_param (ty2, drt2))
        else (match drt1.row with
          | ParamRow d -> (
              if d = dirt_param && Types.EffectSet.is_empty drt1.effect_set && is_dirt_empty dirt 
              then 
                let coer1 = value_coercion_from_impure_dirt dirt_param dirt ty1 in
                let coer2 = value_coercion_to_impure_dirt dirt dirt_param ty2 in (
                if is_dirt_empty (Substitution.apply_substitutions_to_dirt (Substitution.add_dirt_substitution_e dirt_param dirt) drt2)
                then NoEffSyntax.FunToHand (coer1, NoEffSyntax.CoerReturn coer2)
                else NoEffSyntax.FunToHand (coer1, NoEffSyntax.CoerComputation coer2)) 
              else NoEffSyntax.CoerHandler (
              computation_coercion_from_impure_dirt dirt_param dirt (ty1, drt1), 
              computation_coercion_to_impure_dirt dirt dirt_param (ty2, Types.fresh_dirt ())))
          | EmptyRow -> NoEffSyntax.CoerHandler (
              computation_coercion_from_impure_dirt dirt_param dirt (ty1, drt1), 
              computation_coercion_to_impure_dirt dirt dirt_param (ty2, Types.fresh_dirt ())))
    | Types.PrimTy ty_const -> NoEffSyntax.ReflTy (compile_type (Types.PrimTy ty_const))
    | Types.QualTy ((Types.TyParam a1, Types.TyParam a2), ty2) -> 
        NoEffSyntax.CoerQualification (NoEffSyntax.TyCoercion (NoEffSyntax.TyVar a1, NoEffSyntax.TyVar a2), value_coercion_to_impure_dirt dirt dirt_param ty2)
    | Types.QualTy _ -> assert false (* not type parameters *)
    | Types.QualDirt (_, ty2) -> value_coercion_to_impure_dirt dirt dirt_param ty2
    | Types.TySchemeTy (ty_param, _, ty2) -> NoEffSyntax.Forall (ty_param, value_coercion_to_impure_dirt dirt dirt_param ty2)
    | Types.TySchemeDirt (_, ty2) -> value_coercion_to_impure_dirt dirt dirt_param ty2
    | Types.TySchemeSkel (_, ty2) -> value_coercion_to_impure_dirt dirt dirt_param ty2

and computation_coercion_to_impure_dirt dirt dirt_param (ty1, d1) =
  let noeff_coer = value_coercion_to_impure_dirt dirt dirt_param ty1 in
  let computation_coercion_case = 
    if is_dirt_empty (Substitution.apply_substitutions_to_dirt (Substitution.add_dirt_substitution_e dirt_param dirt) d1)
    then assert false (* no rule applicable *)
    else NoEffSyntax.CoerComputation noeff_coer in
  if is_dirt_empty d1
  then noeff_coer
  else match d1.row with
    | ParamRow p -> (
        if p = dirt_param && is_dirt_empty dirt
        then NoEffSyntax.CoerReturn noeff_coer
        else computation_coercion_case)
    | EmptyRow -> computation_coercion_case

let rec compile_expr exeff_expr = 
  match exeff_expr with
    | Typed.Var v -> NoEffSyntax.Var v
    | Typed.BuiltIn (s, i) -> NoEffSyntax.BuiltIn (s,i)
    | Typed.Const ct -> NoEffSyntax.Const ct
    | Typed.Tuple lst -> NoEffSyntax.Tuple (List.map compile_expr lst)
    | Typed.Record rcd -> NoEffSyntax.Record (Assoc.map compile_expr rcd)
    | Typed.Variant (label, expr) -> NoEffSyntax.Variant (label, compile_expr expr)
    | Typed.Lambda abs_ty -> NoEffSyntax.Lambda (compile_abstraction_with_ty abs_ty)
    | Typed.Effect (eff, (ty1, ty2)) -> NoEffSyntax.Effect (eff, (compile_type ty1, compile_type ty2))
    | Typed.Handler handler -> 
        if Assoc.is_empty handler.effect_clauses
        then NoEffSyntax.Lambda (compile_abstraction_with_ty handler.value_clause)
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
          | Types.TySchemeDirt (drt_param, _) -> NoEffSyntax.Cast (compile_expr expr, value_coercion_from_impure_dirt drt_param drt exeff_ty)
          | _ -> assert false)  (* Fail if wrong type *)
    | Typed.ApplySkelExp (expr, skel) -> compile_expr expr
    | Typed.ApplyTyCoercion (expr, ty_coer) -> NoEffSyntax.ApplyTyCoercion (compile_expr expr, compile_coercion ty_coer)
    | Typed.ApplyDirtCoercion (expr, drt_coer) -> compile_expr expr

and compile_handler_with_effects {effect_clauses = eff_cls; value_clause = (valcl_pat, valcl_ty, valcl_comp)} = 
  match TypeChecker.type_of_handler TypeChecker.initial_state {effect_clauses = eff_cls; value_clause = (valcl_pat, valcl_ty, valcl_comp)} with
    | Types.Handler (_, (ty, drt)) -> 
      if is_dirt_empty drt
      then NoEffSyntax.Handler {
        effect_clauses = compile_effect_clauses_return eff_cls; 
        value_clause = (compile_pattern valcl_pat, compile_type valcl_ty, NoEffSyntax.Return (compile_comp valcl_comp))}
      else NoEffSyntax.Handler {
        effect_clauses = (Assoc.kmap 
          (fun ((ef, (ty1, ty2)), (pat1, pat2, comp)) -> ((ef, (compile_type ty1, compile_type ty2)), (compile_pattern pat1, compile_pattern pat2, compile_comp comp))) 
          eff_cls); 
        value_clause = (compile_abstraction_with_ty (valcl_pat, valcl_ty, valcl_comp))}
    | _ -> assert false (* Fail if wrong type *)

and compile_effect_clauses_return eff_cls = 
  Assoc.kmap 
    (fun ((ef, (ty1, ty2)), (pat1, pat2, comp)) -> (match pat2 with
      | Typed.PVar var -> 
        let noEffTy1 = compile_type ty1 in (
        let noEffTy2 = compile_type ty2 in 
          ((ef, (noEffTy1, noEffTy2)), 
          (compile_pattern pat1, 
           compile_pattern pat2, 
           NoEffSyntax.Return (substitute_var_in_term var 
             (NoEffSyntax.Cast (Var var, NoEffSyntax.CoerArrow (ReflTy noEffTy1, Unsafe (ReflTy noEffTy2))))
             (compile_comp comp)))))
      | _ -> assert false)) (* Fail if wrong pattern *)
    eff_cls

and compile_comp exeff_comp = 
  match exeff_comp with
    | Typed.Value expr -> compile_expr expr
    | Typed.LetVal (expr, abs_ty) -> NoEffSyntax.LetVal (compile_expr expr, compile_abstraction_with_ty abs_ty)
    | Typed.LetRec (var_ty_expr_lst, comp) -> 
        NoEffSyntax.LetRec (List.map (fun (var, ty, expr) -> (var, compile_type ty, compile_expr expr)) var_ty_expr_lst, compile_comp comp)
    | Typed.Match (expr, abs_lst) -> NoEffSyntax.Match (compile_expr expr, List.map compile_abstracion abs_lst)
    | Typed.Apply (expr1, expr2) -> NoEffSyntax.Apply (compile_expr expr1, compile_expr expr2)
    | Typed.Handle (expr, comp) -> (match TypeChecker.type_of_expression TypeChecker.initial_state expr with
        | Types.Handler ((ty1, drt1), (ty2, drt2)) -> 
          if is_dirt_empty drt1
          then NoEffSyntax.Apply (compile_expr expr, compile_comp comp)
          else (let compiled_handle = NoEffSyntax.Handle (compile_expr expr, compile_comp comp) in
            if is_dirt_empty drt2
            then NoEffSyntax.Cast (compiled_handle, NoEffSyntax.Unsafe (NoEffSyntax.ReflTy (compile_type ty2)))
            else compiled_handle)
        | _ -> assert false)
    | Typed.Call (eff, expr, abs_ty) -> NoEffSyntax.Call (compile_effect eff, compile_expr expr, compile_abstraction_with_ty abs_ty)
    | Typed.Op ((eff,(ty1,ty2)), expr) -> NoEffSyntax.Op ((eff, (compile_type ty1, compile_type ty2)), compile_expr expr)
    | Typed.Bind (comp1, abs) -> NoEffSyntax.Bind (compile_comp comp1, compile_abstracion abs)
    | Typed.CastComp (comp, drty_coer) -> NoEffSyntax.Cast (compile_comp comp, compile_dirty_coercion drty_coer)
    | Typed.CastComp_ty (comp, ty_coer) -> NoEffSyntax.Cast (compile_comp comp, compile_coercion ty_coer)
    | Typed.CastComp_dirt (comp, drt_coer) -> compile_comp comp (* je to ok? *)

and compile_abstraction_with_ty (pat, ty, comp) = (compile_pattern pat, compile_type ty, compile_comp comp)

and compile_abstracion (pat, comp) = (compile_pattern pat, compile_comp comp)
