open SkelEffSyntax
module SkelEff = SkelEffSyntax

let rec typed_to_erasure_ty sub typed_ty =
  match typed_ty with
  | Type.TyParam p -> (
      match Assoc.lookup p sub with Some x' -> x' | None -> assert false)
  | Type.Arrow (t1, (t2, drt)) ->
      let t1' = typed_to_erasure_ty sub t1 in
      let t2' = typed_to_erasure_ty sub t2 in
      Type.SkelArrow (t1', t2')
  | Type.Tuple tys -> Type.SkelTuple (List.map (typed_to_erasure_ty sub) tys)
  | Type.Handler ((t1, drt1), (t2, drt2)) ->
      let t1' = typed_to_erasure_ty sub t1 in
      let t2' = typed_to_erasure_ty sub t2 in
      Type.SkelHandler (t1', t2')
  | Type.TyBasic p -> Type.SkelBasic p
  | Type.QualTy (_, tty) -> typed_to_erasure_ty sub tty
  | Type.QualDirt (_, tty) -> typed_to_erasure_ty sub tty

and typed_to_erasure_cmp_ty sub (ty, _drt) = typed_to_erasure_ty sub ty

let rec typed_to_erasure_exp sub tt =
  match tt with
  | Term.Var v -> SkelEff.EVar v
  | Term.Const c -> SkelEff.EConst c
  | Term.Tuple elist ->
      SkelEff.ETuple (List.map (fun x -> typed_to_erasure_exp sub x) elist)
  | Term.Lambda abs -> SkelEff.ELambda (typed_to_erasure_abs_with_ty sub abs)
  | Term.Effect e -> SkelEff.EEffect e
  | Term.Handler h ->
      let e_pat, tty, v_comp = h.value_clause in
      let op_c = h.effect_clauses in
      let new_vc = typed_to_erasure_abs_with_ty sub h.value_clause in
      let new_op_c =
        Assoc.kmap
          (fun (eff, e_a2) ->
            let new_e_a2 = typed_to_erasure_abs_2 sub e_a2 in
            (eff, new_e_a2))
          op_c
      in
      let new_h = { effect_clauses = new_op_c; value_clause = new_vc } in
      SkelEff.EHandler new_h
  | CastExp (e, _) -> typed_to_erasure_exp sub e
  | LambdaTyCoerVar (_, _, e) -> typed_to_erasure_exp sub e
  | LambdaDirtCoerVar (_, _, e) -> typed_to_erasure_exp sub e
  | ApplyTyCoercion (e, _) -> typed_to_erasure_exp sub e
  | ApplyDirtCoercion (e, _) -> typed_to_erasure_exp sub e

and typed_to_erasure_comp sub tt =
  match tt with
  | Term.Value e -> SkelEff.EValue (typed_to_erasure_exp sub e)
  | Term.LetVal (e, (p, _, c)) ->
      let p' = typed_to_erasure_pattern p in
      let e' = typed_to_erasure_exp sub e in
      let c' = typed_to_erasure_comp sub c in
      SkelEff.ELetVal (p', e', c')
  | Term.Apply (e1, e2) ->
      let e1' = typed_to_erasure_exp sub e1 in
      let e2' = typed_to_erasure_exp sub e2 in
      SkelEff.EApply (e1', e2')
  | Term.Handle (e, c) ->
      let e' = typed_to_erasure_exp sub e in
      let c' = typed_to_erasure_comp sub c in
      SkelEff.EHandle (e', c')
  | Term.Call (eff, e, abs) ->
      let e' = typed_to_erasure_exp sub e in
      let abs' = typed_to_erasure_abs_with_ty sub abs in
      SkelEff.ECall (eff, e', abs')
  | Term.Bind (c, a) ->
      let c' = typed_to_erasure_comp sub c in
      let a' = typed_to_erasure_abs sub a in
      SkelEff.EBind (c', a')
  | Term.Match (e, ty, alist) ->
      let e' = typed_to_erasure_exp sub e in
      let ty' = typed_to_erasure_cmp_ty sub ty in
      let alist' = List.map (typed_to_erasure_abs sub) alist in
      SkelEff.EMatch (e', ty', alist', Location.unknown)
  | Term.CastComp (c, _) -> typed_to_erasure_comp sub c
  | Term.CastComp_ty (c, _) -> typed_to_erasure_comp sub c
  | Term.CastComp_dirt (c, _) -> typed_to_erasure_comp sub c
  | Term.LetRec ([ (var, argTy, resTy, abs) ], c1) ->
      SkelEff.ELetRec
        ( [
            ( var,
              typed_to_erasure_ty sub argTy,
              typed_to_erasure_cmp_ty sub resTy,
              typed_to_erasure_abs sub abs );
          ],
          typed_to_erasure_comp sub c1 )

and typed_to_erasure_abs_with_ty sub (e_p, e_ty, e_c) =
  ( typed_to_erasure_pattern e_p,
    typed_to_erasure_ty sub e_ty,
    typed_to_erasure_comp sub e_c )

and typed_to_erasure_abs sub (e_p, e_c) =
  (typed_to_erasure_pattern e_p, typed_to_erasure_comp sub e_c)

and typed_to_erasure_abs_2 sub (e_p1, e_p2, e_c) =
  ( typed_to_erasure_pattern e_p1,
    typed_to_erasure_pattern e_p2,
    typed_to_erasure_comp sub e_c )

and typed_to_erasure_pattern = function
  | Term.PVar x -> SkelEff.PEVar x
  | Term.PAs (p, x) -> SkelEff.PEAs (typed_to_erasure_pattern p, x)
  | Term.PTuple ps -> SkelEff.PETuple (List.map typed_to_erasure_pattern ps)
  | Term.PRecord ass ->
      SkelEff.PERecord (Assoc.map typed_to_erasure_pattern ass)
  | Term.PVariant (lbl, p) ->
      SkelEff.PEVariant (lbl, typed_to_erasure_pattern p)
  | Term.PConst const -> SkelEff.PEConst const
  | Term.PNonbinding -> SkelEff.PENonbinding
