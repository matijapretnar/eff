open NoEffSyntax

let rec substitute_tyvar_in_ty var new_ty ty =
  match ty with
  | TyVar t -> if t = var then new_ty else TyVar t
  | TyApply (t, tys) ->
      TyApply
        (t, List.map (fun ty1 -> substitute_tyvar_in_ty var new_ty ty1) tys)
  | TyTuple tys ->
      TyTuple (List.map (fun ty1 -> substitute_tyvar_in_ty var new_ty ty1) tys)
  | TyBasic c -> TyBasic c
  | TyArrow (ty1, ty2) ->
      TyArrow
        ( substitute_tyvar_in_ty var new_ty ty1,
          substitute_tyvar_in_ty var new_ty ty2 )
  | TyHandler (ty1, ty2) ->
      TyHandler
        ( substitute_tyvar_in_ty var new_ty ty1,
          substitute_tyvar_in_ty var new_ty ty2 )
  | TyForAll (t, ty1) ->
      TyForAll
        (t, if t = var then ty1 else substitute_tyvar_in_ty var new_ty ty1)
  | TyQualification (TyCoercion (ty1, ty2), ty3) ->
      TyQualification
        ( TyCoercion
            ( substitute_tyvar_in_ty var new_ty ty1,
              substitute_tyvar_in_ty var new_ty ty2 ),
          substitute_tyvar_in_ty var new_ty ty3 )
  | TyComputation ty1 -> TyComputation (substitute_tyvar_in_ty var new_ty ty1)

let rec substitute_tyvar_in_coercion var ty coer =
  match coer with
  | CoerVar v -> CoerVar v
  | ReflTy ty1 -> ReflTy (substitute_tyvar_in_ty var ty ty1)
  | ReflVar t -> if t = var then ReflTy ty else ReflVar t
  | CoerArrow (c1, c2) ->
      CoerArrow
        ( substitute_tyvar_in_coercion var ty c1,
          substitute_tyvar_in_coercion var ty c2 )
  | CoerHandler (c1, c2) ->
      CoerHandler
        ( substitute_tyvar_in_coercion var ty c1,
          substitute_tyvar_in_coercion var ty c2 )
  | HandToFun (c1, c2) ->
      HandToFun
        ( substitute_tyvar_in_coercion var ty c1,
          substitute_tyvar_in_coercion var ty c2 )
  | FunToHand (c1, c2) ->
      FunToHand
        ( substitute_tyvar_in_coercion var ty c1,
          substitute_tyvar_in_coercion var ty c2 )
  | Forall (t, c) ->
      if t = var then Forall (t, c)
      else Forall (t, substitute_tyvar_in_coercion var ty c)
  | CoerQualification (TyCoercion (ty1, ty2), c) ->
      CoerQualification
        ( TyCoercion
            ( substitute_tyvar_in_ty var ty ty1,
              substitute_tyvar_in_ty var ty ty2 ),
          substitute_tyvar_in_coercion var ty c )
  | CoerComputation c -> CoerComputation (substitute_tyvar_in_coercion var ty c)
  | CoerReturn c -> CoerReturn (substitute_tyvar_in_coercion var ty c)
  | Unsafe c -> Unsafe (substitute_tyvar_in_coercion var ty c)
  | SequenceCoercion (c1, c2) ->
      SequenceCoercion
        ( substitute_tyvar_in_coercion var ty c1,
          substitute_tyvar_in_coercion var ty c2 )
  | TupleCoercion cs ->
      TupleCoercion
        (List.map (fun c -> substitute_tyvar_in_coercion var ty c) cs)
  | ApplyCoercion (t, cs) ->
      ApplyCoercion
        (t, List.map (fun c -> substitute_tyvar_in_coercion var ty c) cs)
  | ApplyTyCoer (c, ty1) ->
      ApplyTyCoer
        ( substitute_tyvar_in_coercion var ty c,
          substitute_tyvar_in_ty var ty ty1 )
  | ApplyQualTyCoer (c1, c2) ->
      ApplyQualTyCoer
        ( substitute_tyvar_in_coercion var ty c1,
          substitute_tyvar_in_coercion var ty c2 )
  | LeftArrow c -> LeftArrow (substitute_tyvar_in_coercion var ty c)

let rec substitute_coer_var_in_coer var new_coer coer =
  match coer with
  | CoerVar v -> if v = var then new_coer else CoerVar v
  | ReflTy ty1 -> ReflTy ty1
  | ReflVar t -> ReflVar t
  | CoerArrow (c1, c2) ->
      CoerArrow
        ( substitute_coer_var_in_coer var new_coer c1,
          substitute_coer_var_in_coer var new_coer c2 )
  | CoerHandler (c1, c2) ->
      CoerHandler
        ( substitute_coer_var_in_coer var new_coer c1,
          substitute_coer_var_in_coer var new_coer c2 )
  | HandToFun (c1, c2) ->
      HandToFun
        ( substitute_coer_var_in_coer var new_coer c1,
          substitute_coer_var_in_coer var new_coer c2 )
  | FunToHand (c1, c2) ->
      FunToHand
        ( substitute_coer_var_in_coer var new_coer c1,
          substitute_coer_var_in_coer var new_coer c2 )
  | Forall (t, c) -> Forall (t, substitute_coer_var_in_coer var new_coer c)
  | CoerQualification (ty_coer, c) ->
      CoerQualification (ty_coer, substitute_coer_var_in_coer var new_coer c)
  | CoerComputation c ->
      CoerComputation (substitute_coer_var_in_coer var new_coer c)
  | CoerReturn c -> CoerReturn (substitute_coer_var_in_coer var new_coer c)
  | Unsafe c -> Unsafe (substitute_coer_var_in_coer var new_coer c)
  | SequenceCoercion (c1, c2) ->
      SequenceCoercion
        ( substitute_coer_var_in_coer var new_coer c1,
          substitute_coer_var_in_coer var new_coer c2 )
  | TupleCoercion cs ->
      TupleCoercion
        (List.map (fun c -> substitute_coer_var_in_coer var new_coer c) cs)
  | ApplyCoercion (t, cs) ->
      ApplyCoercion
        (t, List.map (fun c -> substitute_coer_var_in_coer var new_coer c) cs)
  | ApplyTyCoer (c, ty1) ->
      ApplyTyCoer (substitute_coer_var_in_coer var new_coer c, ty1)
  | ApplyQualTyCoer (c1, c2) ->
      ApplyQualTyCoer
        ( substitute_coer_var_in_coer var new_coer c1,
          substitute_coer_var_in_coer var new_coer c2 )
  | LeftArrow c -> LeftArrow (substitute_coer_var_in_coer var new_coer c)

let rec substitute_coer_var_in_term var coer term =
  match term with
  | Var v -> Var v
  | BuiltIn (s, i) -> BuiltIn (s, i)
  | Const c -> Const c
  | Tuple ts ->
      Tuple (List.map (fun t -> substitute_coer_var_in_term var coer t) ts)
  | Record rcd ->
      Record (Assoc.map (fun t -> substitute_coer_var_in_term var coer t) rcd)
  | Variant (l, t1) -> Variant (l, substitute_coer_var_in_term var coer t1)
  | Lambda (pat, ty, t1) ->
      Lambda (pat, ty, substitute_coer_var_in_term var coer t1)
  | Effect e -> Effect e
  | Apply (t1, t2) ->
      Apply
        ( substitute_coer_var_in_term var coer t1,
          substitute_coer_var_in_term var coer t2 )
  | BigLambdaTy (p, t) -> BigLambdaTy (p, substitute_coer_var_in_term var coer t)
  | ApplyTy (t, ty) -> ApplyTy (substitute_coer_var_in_term var coer t, ty)
  | BigLambdaCoerVar (tycp, tyc, t) ->
      BigLambdaCoerVar
        ( tycp,
          tyc,
          if tycp = var then t else substitute_coer_var_in_term var coer t )
  | ApplyTyCoercion (t, c) ->
      ApplyTyCoercion
        ( substitute_coer_var_in_term var coer t,
          substitute_coer_var_in_coer var coer c )
  | Cast (t, c) ->
      Cast
        ( substitute_coer_var_in_term var coer t,
          substitute_coer_var_in_coer var coer c )
  | Return t -> Return (substitute_coer_var_in_term var coer t)
  | Handler { effect_clauses = eff_cls; value_clause = pat, ty, t } ->
      Handler
        {
          effect_clauses =
            Assoc.map
              (fun (pat1, pat2, t) ->
                (pat1, pat2, substitute_coer_var_in_term var coer t))
              eff_cls;
          value_clause = (pat, ty, substitute_coer_var_in_term var coer t);
        }
  | LetVal (t1, (pat, ty, t2)) ->
      LetVal
        ( substitute_coer_var_in_term var coer t1,
          (pat, ty, substitute_coer_var_in_term var coer t2) )
  | LetRec (defs, t2) ->
      LetRec
        ( List.map
            (fun (v, ty, t) -> (v, ty, substitute_coer_var_in_term var coer t))
            defs,
          substitute_coer_var_in_term var coer t2 )
  | Match (t, cases) ->
      Match
        ( substitute_coer_var_in_term var coer t,
          List.map
            (fun (p, t) -> (p, substitute_coer_var_in_term var coer t))
            cases )
  | Call (e, t1, (p, ty, t2)) ->
      Call
        ( e,
          substitute_coer_var_in_term var coer t1,
          (p, ty, substitute_coer_var_in_term var coer t2) )
  | Op (e, t) -> Op (e, substitute_coer_var_in_term var coer t)
  | Bind (t1, (p, t2)) ->
      Bind
        ( substitute_coer_var_in_term var coer t1,
          (p, substitute_coer_var_in_term var coer t2) )
  | Handle (t1, t2) ->
      Handle
        ( substitute_coer_var_in_term var coer t1,
          substitute_coer_var_in_term var coer t2 )

let rec substitute_var_in_term var replacement_term term =
  match term with
  | NoEffSyntax.Var v -> if v = var then replacement_term else NoEffSyntax.Var v
  | NoEffSyntax.BuiltIn (s, i) -> NoEffSyntax.BuiltIn (s, i)
  | NoEffSyntax.Const t -> NoEffSyntax.Const t
  | NoEffSyntax.Tuple ts ->
      NoEffSyntax.Tuple
        (List.map (substitute_var_in_term var replacement_term) ts)
  | NoEffSyntax.Record rcrd ->
      NoEffSyntax.Record
        (Assoc.map (substitute_var_in_term var replacement_term) rcrd)
  | NoEffSyntax.Variant (l, t) ->
      NoEffSyntax.Variant (l, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Lambda (p, ty, t) ->
      NoEffSyntax.Lambda (p, ty, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Effect e -> NoEffSyntax.Effect e
  | NoEffSyntax.Apply (t1, t2) ->
      NoEffSyntax.Apply
        ( substitute_var_in_term var replacement_term t1,
          substitute_var_in_term var replacement_term t2 )
  | NoEffSyntax.BigLambdaTy (p, t) ->
      NoEffSyntax.BigLambdaTy (p, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.ApplyTy (t, ty) ->
      NoEffSyntax.ApplyTy (substitute_var_in_term var replacement_term t, ty)
  | NoEffSyntax.BigLambdaCoerVar (p, tyc, t) ->
      NoEffSyntax.BigLambdaCoerVar
        (p, tyc, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.ApplyTyCoercion (t, c) ->
      NoEffSyntax.ApplyTyCoercion
        (substitute_var_in_term var replacement_term t, c)
  | NoEffSyntax.Cast (t, c) ->
      NoEffSyntax.Cast (substitute_var_in_term var replacement_term t, c)
  | NoEffSyntax.Return t ->
      NoEffSyntax.Return (substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Handler { effect_clauses = efc; value_clause = p, ty, t } ->
      NoEffSyntax.Handler
        {
          effect_clauses =
            Assoc.map
              (fun (p1, p2, t) ->
                (p1, p2, substitute_var_in_term var replacement_term t))
              efc;
          value_clause = (p, ty, substitute_var_in_term var replacement_term t);
        }
  | NoEffSyntax.LetVal (t1, (pat, ty, t2)) ->
      NoEffSyntax.LetVal
        ( substitute_var_in_term var replacement_term t1,
          (pat, ty, substitute_var_in_term var replacement_term t2) )
  | NoEffSyntax.LetRec (var_ty_term_list, t2) ->
      NoEffSyntax.LetRec
        ( List.map
            (fun (var, ty, t1) ->
              (var, ty, substitute_var_in_term var replacement_term t1))
            var_ty_term_list,
          substitute_var_in_term var replacement_term t2 )
  | NoEffSyntax.Match (t1, abs_lst) ->
      NoEffSyntax.Match
        ( substitute_var_in_term var replacement_term t1,
          List.map
            (fun (pat, t2) ->
              (pat, substitute_var_in_term var replacement_term t2))
            abs_lst )
  | NoEffSyntax.Call (e, t1, (p, ty, t2)) ->
      NoEffSyntax.Call
        ( e,
          substitute_var_in_term var replacement_term t1,
          (p, ty, substitute_var_in_term var replacement_term t2) )
  | NoEffSyntax.Op (e, t) ->
      NoEffSyntax.Op (e, substitute_var_in_term var replacement_term t)
  | NoEffSyntax.Bind (t1, (pat, t2)) ->
      NoEffSyntax.Bind
        ( substitute_var_in_term var replacement_term t1,
          (pat, substitute_var_in_term var replacement_term t2) )
  | NoEffSyntax.Handle (t1, t2) ->
      NoEffSyntax.Handle
        ( substitute_var_in_term var replacement_term t1,
          substitute_var_in_term var replacement_term t2 )
