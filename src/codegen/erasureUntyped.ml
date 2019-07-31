
let rec typed_to_untyped_ty sub (typed_ty : Types.target_ty) =
  match typed_ty with
    | Types.TyParam t -> Type.TyParam t
    | Types.Apply (t,tys) ->
      Type.Apply (t
                 ,List.map (fun ty -> typed_to_untyped_ty sub ty) tys
                 )
    | Types.Arrow (t1,(t2,_)) -> Type.Arrow
                                   (typed_to_untyped_ty sub t1
                                   , typed_to_untyped_ty sub t2)
    | Types.Tuple tys ->
      Type.Tuple (List.map (fun ty -> typed_to_untyped_ty sub ty) tys)
    | Types.Handler ((ty1,_),(ty2,_)) ->
      Type.Handler { value = typed_to_untyped_ty sub ty1
                   ; finally = typed_to_untyped_ty sub ty2}
    | Types.PrimTy ty -> (match ty with
      | Types.IntTy -> Type.int_ty
      | Types.BoolTy -> Type.bool_ty
      | Types.StringTy -> Type.string_ty
      | Types.FloatTy -> Type.float_ty)
    | Types.QualTy (_,ty) -> typed_to_untyped_ty sub ty
    | Types.QualDirt (_,ty) -> typed_to_untyped_ty sub ty
    | Types.TySchemeTy (_,_,ty) -> typed_to_untyped_ty sub ty
    | Types.TySchemeDirt (_,ty) -> typed_to_untyped_ty sub ty
    | Types.TySchemeSkel (_,ty) -> typed_to_untyped_ty sub ty

and typed_to_untyped_exp sub (typed_exp : Typed.expression) : UntypedSyntax.expression =
  let res = typed_to_untyped_exp_sub sub typed_exp
  in {it=res; at=Location.unknown}


and typed_to_untyped_exp_sub sub (typed_exp : Typed.expression) : UntypedSyntax.plain_expression =
  match typed_exp with
  | Typed.Var v -> UntypedSyntax.Var v
  | Typed.BuiltIn _ -> failwith __LOC__
  | Typed.Const c -> UntypedSyntax.Const c
  | Typed.Tuple elist -> UntypedSyntax.Tuple (List.map (fun x -> typed_to_untyped_exp sub x) elist)
  | Typed.Record _ -> failwith __LOC__
  | Typed.Variant (l,e) ->
    UntypedSyntax.Variant (l, Some (typed_to_untyped_exp sub e))
  | Typed.Lambda abs -> UntypedSyntax.Lambda (typed_to_untyped_abs_with_ty sub abs)
  | Typed.Effect (e,_) -> UntypedSyntax.Effect e
  | Typed.Handler {effect_clauses = effcs;value_clause = valc} ->
    UntypedSyntax.Handler
      {effect_clauses =
         Assoc.kmap
           (fun ((e,effty),a2) ->
              (e,typed_to_untyped_abs_2 sub a2))
           effcs
      ;value_clause =
         typed_to_untyped_abs_with_ty sub valc
      ;finally_clause =
         let var = CoreTypes.Variable.fresh "x" in
         typed_to_untyped_abs sub
           (Typed.PVar var, (Typed.Value (Typed.Var var)))}
  | Typed.BigLambdaTy (_,_,e) -> typed_to_untyped_exp_sub sub e
  | Typed.BigLambdaDirt (_,e) -> typed_to_untyped_exp_sub sub e
  | Typed.BigLambdaSkel (_,e) -> typed_to_untyped_exp_sub sub e
  | Typed.CastExp (e,_) -> typed_to_untyped_exp_sub sub e
  | Typed.ApplyTyExp (e,_) -> typed_to_untyped_exp_sub sub e
  | Typed.LambdaTyCoerVar (_,_,e) -> typed_to_untyped_exp_sub sub e
  | Typed.LambdaDirtCoerVar (_,_,e) -> typed_to_untyped_exp_sub sub e
  | Typed.ApplyDirtExp (e,_) -> typed_to_untyped_exp_sub sub e
  | Typed.ApplySkelExp (e,_) -> typed_to_untyped_exp_sub sub e
  | Typed.ApplyTyCoercion (e,_) -> typed_to_untyped_exp_sub sub e
  | Typed.ApplyDirtCoercion (e,_) -> typed_to_untyped_exp_sub sub e

and typed_to_untyped_comp sub (typed_comp : Typed.computation) : UntypedSyntax.computation =
  let res = typed_to_untyped_comp_sub sub typed_comp
  in {it=res; at=Location.unknown}

and typed_to_untyped_comp_sub sub (typed_comp : Typed.computation) : UntypedSyntax.plain_computation =
  match typed_comp with
  | Typed.Value v -> UntypedSyntax.Value (typed_to_untyped_exp sub v)
  | Typed.LetVal (e,(p,ty,c)) ->
    UntypedSyntax.Let
      ([(typed_to_untyped_pattern p
        ,typed_to_untyped_comp sub (Typed.Value e))]
      ,typed_to_untyped_comp sub c)
  | Typed.LetRec (lrs,c) ->
    (* let lrs' = (List.map
     *     (fun (v,_ty,e) ->
     *       let var = CoreTypes.Variable.fresh "x" in
     *       (v,
     *         (typed_to_untyped_pattern (Typed.PVar var)
     *         ,typed_to_untyped_comp sub
     *             (Typed.Apply (e,Typed.Var var))
     *         )
     *       )
     *     ) lrs)
     * in UntypedSyntax.LetRec (lrs' ,typed_to_untyped_comp sub c) *)
      UntypedSyntax.LetRec
      (List.map
         (fun (v,ty,e) ->
            (v,
             (typed_to_untyped_pattern Typed.PNonbinding
             ,typed_to_untyped_comp sub (Typed.Value e))))
         lrs
      ,typed_to_untyped_comp sub c)
  | Typed.Match (e,alst) ->
    let e' = typed_to_untyped_exp sub e in
    let alst' = List.map (fun (a:Typed.abstraction) -> typed_to_untyped_abs sub a) alst in
    UntypedSyntax.Match (e', alst')
  | Typed.Apply (e1,e2) -> UntypedSyntax.Apply (typed_to_untyped_exp sub e1,typed_to_untyped_exp sub e2)
  | Typed.Handle (e,c) -> UntypedSyntax.Handle (typed_to_untyped_exp sub e,typed_to_untyped_comp sub c)
  | Typed.Call (eff,e,absty) -> failwith __LOC__
  | Typed.Op (eff,e) -> failwith __LOC__
  | Typed.Bind (c1,(p,c2)) ->
    UntypedSyntax.Let
      ([(typed_to_untyped_pattern p
        ,typed_to_untyped_comp sub c1)]
      ,typed_to_untyped_comp sub c2)
  | Typed.CastComp (c,_) -> typed_to_untyped_comp_sub sub c
  | Typed.CastComp_ty (c,_) -> typed_to_untyped_comp_sub sub c
  | Typed.CastComp_dirt (c,_) -> typed_to_untyped_comp_sub sub c

and typed_to_untyped_abs_with_ty sub ((e_p, e_ty, e_c) : Typed.abstraction_with_ty) : UntypedSyntax.abstraction =
  ( typed_to_untyped_pattern e_p
  , typed_to_untyped_comp sub e_c )

and typed_to_untyped_abs sub (abs : Typed.abstraction) : UntypedSyntax.abstraction =
  let ((p:Typed.pattern),(c:Typed.computation)) = abs in
  (typed_to_untyped_pattern p, typed_to_untyped_comp sub c)

and typed_to_untyped_abs_2 sub ((e_p1, e_p2, e_c) : Typed.abstraction2) : UntypedSyntax.abstraction2 =
  ( typed_to_untyped_pattern e_p1
  , typed_to_untyped_pattern e_p2
  , typed_to_untyped_comp sub e_c )

and typed_to_untyped_pattern (pat : Typed.pattern) : UntypedSyntax.pattern =
  let res =
    match pat with
    | Typed.PVar x -> UntypedSyntax.PVar x
    | Typed.PAs (p, x) -> UntypedSyntax.PAs (typed_to_untyped_pattern p, x)
    | Typed.PTuple ps ->
      UntypedSyntax.PTuple
        (List.map (fun p -> typed_to_untyped_pattern p) ps)
    | Typed.PRecord _ -> failwith "PRecord erasure not implemented"
    | Typed.PVariant (l,p) ->
      UntypedSyntax.PVariant (l,Some (typed_to_untyped_pattern p))
    | Typed.PConst const -> UntypedSyntax.PConst const
    | Typed.PNonbinding -> UntypedSyntax.PNonbinding
  in {it = res; at = Location.unknown}
