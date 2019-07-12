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

and typed_to_untyped_exp sub typed_exp =
  let res = match typed_exp with
    | Typed.Var v -> UntypedSyntax.Var v
    | Typed.BuiltIn _ -> failwith __LOC__
    | Typed.Const c -> UntypedSyntax.Const c
    | Typed.Tuple elist -> UntypedSyntax.Tuple (List.map (fun x -> typed_to_untyped_exp sub x) elist)
    | Typed.Record _ -> failwith __LOC__
    | Typed.Variant _ -> failwith __LOC__
    | Typed.Lambda _ -> failwith __LOC__
    | Typed.Effect _ -> failwith __LOC__
    | Typed.Handler _ -> failwith __LOC__
    | Typed.BigLambdaTy _ -> failwith __LOC__
    | Typed.BigLambdaDirt _ -> failwith __LOC__
    | Typed.BigLambdaSkel _ -> failwith __LOC__
    | Typed.CastExp _ -> failwith __LOC__
    | Typed.ApplyTyExp _ -> failwith __LOC__
    | Typed.LambdaTyCoerVar _ -> failwith __LOC__
    | Typed.LambdaDirtCoerVar _ -> failwith __LOC__
    | Typed.ApplyDirtExp _ -> failwith __LOC__
    | Typed.ApplySkelExp _ -> failwith __LOC__
    | Typed.ApplyTyCoercion _ -> failwith __LOC__
    | Typed.ApplyDirtCoercion _ -> failwith __LOC__
  in {it=res; at=Location.unknown}

and typed_to_untyped_comp sub typed_comp : UntypedSyntax.computation =
  let res = match typed_comp with
    | Typed.Value v -> UntypedSyntax.Value (typed_to_untyped_exp sub v)
    | Typed.LetVal _ -> failwith __LOC__
    | Typed.LetRec _ -> failwith __LOC__
    | Typed.Match _ -> failwith __LOC__
    | Typed.Apply _ -> failwith __LOC__
    | Typed.Handle _ -> failwith __LOC__
    | Typed.Call _ -> failwith __LOC__
    | Typed.Op _ -> failwith __LOC__
    | Typed.Bind _ -> failwith __LOC__
    | Typed.CastComp _ -> failwith __LOC__
    | Typed.CastComp_ty _ -> failwith __LOC__
    | Typed.CastComp_dirt _ -> failwith __LOC__
  in {it=res; at=Location.unknown}

and typed_to_untyped_abs_with_ty sub (e_p, e_ty, e_c) =
  ( typed_to_untyped_pattern e_p
  , typed_to_untyped_ty sub e_ty
  , typed_to_untyped_comp sub e_c )

and typed_to_untyped_abs sub (e_p, e_c) =
  (typed_to_untyped_pattern e_p, typed_to_untyped_comp sub e_c)

and typed_to_untyped_abs_2 sub (e_p1, e_p2, e_c) =
  ( typed_to_untyped_pattern e_p1
  , typed_to_untyped_pattern e_p2
  , typed_to_untyped_comp sub e_c )

and typed_to_untyped_pattern ty =
  let res =
    match ty with
    | Typed.PVar x -> UntypedSyntax.PVar x
    | Typed.PAs (p, x) -> UntypedSyntax.PAs (typed_to_untyped_pattern p, x)
    | Typed.PNonbinding -> UntypedSyntax.PNonbinding
    | Typed.PConst const -> UntypedSyntax.PConst const
    | _ -> failwith "not implemented"
  in {it = res; at = Location.unknown}
