open UntypedSyntax

let rec typed_to_untyped_ty sub typed_ty =
  match typed_ty with
    | Types.TyParam _ -> failwith __LOC__
    | Types.Apply _ -> failwith __LOC__
    | Types.Arrow (t1,(t2,_)) -> Type.Arrow
                                   (typed_to_untyped_ty sub t1
                                   , typed_to_untyped_ty sub t2)
    | Types.Tuple _ -> failwith __LOC__
    | Types.Handler _ -> failwith __LOC__
    | Types.PrimTy _ -> failwith __LOC__
    | Types.QualTy _ -> failwith __LOC__
    | Types.QualDirt _ -> failwith __LOC__
    | Types.TySchemeTy _ -> failwith __LOC__
    | Types.TySchemeDirt _ -> failwith __LOC__
    | Types.TySchemeSkel _ -> failwith __LOC__

and typed_to_untyped_exp sub typed_exp : UntypedSyntax.expression =
  let res = typed_to_untyped_exp_sub sub typed_exp
  in {it=res; at=Location.unknown}
  
                                              
and typed_to_untyped_exp_sub sub typed_exp : UntypedSyntax.plain_expression =
  match typed_exp with
  | Typed.Var v -> UntypedSyntax.Var v
  | Typed.BuiltIn _ -> failwith __LOC__
  | Typed.Const c -> UntypedSyntax.Const c
  | Typed.Tuple elist -> UntypedSyntax.Tuple (List.map (fun x -> typed_to_untyped_exp sub x) elist)
  | Typed.Record _ -> failwith __LOC__
  | Typed.Variant _ -> failwith __LOC__
  | Typed.Lambda abs -> UntypedSyntax.Lambda (typed_to_untyped_abs_with_ty sub abs)
  | Typed.Effect (e,_) -> UntypedSyntax.Effect e
  | Typed.Handler _ -> failwith __LOC__
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

and typed_to_untyped_comp sub typed_comp : UntypedSyntax.computation =
  let res = typed_to_untyped_comp_sub sub typed_comp
  in {it=res; at=Location.unknown}

and typed_to_untyped_comp_sub sub typed_comp : UntypedSyntax.plain_computation =
  match typed_comp with
  | Typed.Value v -> UntypedSyntax.Value (typed_to_untyped_exp sub v)
  | Typed.LetVal (e,abs) ->
    UntypedSyntax.Let ([typed_to_untyped_abs_with_ty sub abs]
                      ,typed_to_untyped_comp sub (Typed.Value e))
  | Typed.LetRec _ -> failwith __LOC__
  | Typed.Match (e,alst) ->
    UntypedSyntax.Match (typed_to_untyped_exp sub e
                        ,List.map (fun abs -> typed_to_untyped_abs sub abs) alst)
  | Typed.Apply (e1,e2) -> UntypedSyntax.Apply (typed_to_untyped_exp sub e1,typed_to_untyped_exp sub e2)
  | Typed.Handle (e,c) -> UntypedSyntax.Handle (typed_to_untyped_exp sub e,typed_to_untyped_comp sub c)
  | Typed.Call _ -> failwith __LOC__
  | Typed.Op _ -> failwith __LOC__
  | Typed.Bind _ -> failwith __LOC__
  | Typed.CastComp (c,_) -> typed_to_untyped_comp_sub sub c
  | Typed.CastComp_ty (c,_) -> typed_to_untyped_comp_sub sub c
  | Typed.CastComp_dirt (c,_) -> typed_to_untyped_comp_sub sub c

and typed_to_untyped_abs_with_ty sub (e_p, e_ty, e_c) : UntypedSyntax.abstraction =
  ( typed_to_untyped_pattern e_p
  , typed_to_untyped_comp sub e_c )

and typed_to_untyped_abs sub (e_p, e_c) : UntypedSyntax.abstraction =
  (typed_to_untyped_pattern e_p, typed_to_untyped_comp sub e_c)

and typed_to_untyped_abs_2 sub (e_p1, e_p2, e_c) : UntypedSyntax.abstraction2 =
  ( typed_to_untyped_pattern e_p1
  , typed_to_untyped_pattern e_p2
  , typed_to_untyped_comp sub e_c )

and typed_to_untyped_pattern ty : UntypedSyntax.pattern =
  let res =
    match ty with
    | Typed.PVar x -> UntypedSyntax.PVar x
    | Typed.PAs (p, x) -> UntypedSyntax.PAs (typed_to_untyped_pattern p, x)
    | Typed.PNonbinding -> UntypedSyntax.PNonbinding
    | Typed.PConst const -> UntypedSyntax.PConst const
    | _ -> failwith "not implemented"
  in {it = res; at = Location.unknown}
