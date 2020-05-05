module NoEff = NoEffSyntax
module OCaml = OcamlSyntax

module Variable = Symbol.Make (Symbol.String)
type variable = Variable.t

let rec elab_pattern (in_p : NoEff.n_pattern) : OCaml.pattern=
  match in_p with
  | NoEff.PNVar x -> OCaml.PVar x
  | NoEff.PNAs (p, x) -> OCaml.PAs (elab_pattern p, x)
  | NoEff.PNConst c -> OCaml.PConst c
  | NoEff.PNTuple lst -> OCaml.PTuple (List.map elab_pattern lst)
  | NoEff.PNRecord lst -> OCaml.PRecord
      (Assoc.map elab_pattern lst)
  | NoEff.PNVariant (lbl, None) -> OCaml.PVariant (lbl, None)
  | NoEff.PNVariant (lbl, Some p) -> OCaml.PVariant (lbl, Some (elab_pattern p))
  | NoEff.PNNonbinding -> OCaml.PNonbinding

let rec elab_term (t_in : NoEff.n_term) : OCaml.term =
  match t_in with
  | NoEff.NVar x -> OCaml.Var x
  | NoEff.NConst c -> OCaml.Const c
  | NoEff.NTuple lst -> OCaml.Tuple (List.map elab_term lst)
  | NoEff.NRecord lst -> OCaml.Record
      (Assoc.map elab_term lst)
  | NoEff.NVariant (lbl, None) -> OCaml.Variant (lbl, None)
  | NoEff.NVariant (lbl, Some t) -> OCaml.Variant (lbl, Some (elab_term t))
  | NoEff.NFun (x, _, c) ->
      OCaml.Lambda (elab_pattern x, elab_term c)
  | NoEff.NEffect (eff, (t1, t2)) -> OCaml.Effect (eff, elab_type t1, elab_type t2)
  | NoEff.NHandler h ->
      let (vcp, vct, vcc) = h.return_clause in
      OCaml.Handler (elab_abstraction_with_ty h.return_clause,
        List.map elab_effect_clause (Assoc.to_list h.effect_clauses))
  | NoEff.NLet (e, (p, c)) ->
      OCaml.Let ((elab_pattern p, elab_term e), elab_term c)
  | NoEff.NApplyTerm (e1, e2) ->
      OCaml.Apply (elab_term e1, elab_term e2)
  | NoEff.NHandle (c, e) ->
      OCaml.Apply (elab_term e, elab_term c)
  | NoEff.NCall (eff, e, (p, _, c)) ->
      OCaml.Call (fst eff, elab_term e, (elab_pattern p, elab_term c))
  | NoEff.NBind (c1, a) ->
      OCaml.Bind (elab_term c1, elab_abstraction a)
  | NoEff.NMatch (e, _, alist, _) ->
      OCaml.Match (elab_term e,
        List.map (fun (p, c) ->
          OCaml.ValueClause (elab_pattern p, elab_term c)) alist)
  | NoEff.NLetRec (alist, c) ->
      let alist' = List.map (fun (v, _, _, (p, c))
                  -> (v, (elab_pattern p, elab_term c))) alist in
      OCaml.LetRec (alist', elab_term c)
  | NoEff.NOp (eff, t) -> failwith "No operations supposed to happen"
  | NoEff.NBigLambdaCoer (p, c, t)-> failwith "Not supported without polymorphism"
  | NoEff.NApplyCoer (t, c) -> failwith "Not supported without polymorphism"
  | NoEff.NCast (t, c) -> OCaml.Apply (elab_coercion c, elab_term t)
  | NoEff.NReturn t -> OCaml.Return (elab_term t)

and elab_coercion (coer: NoEff.n_coercion): OCaml.term =
  match coer with
  | NoEff.NCoerRefl t ->
    let x = Variable.fresh "coer_refl_x" in
    OCaml.Lambda (OCaml.PVar x, OCaml.Var x)
  | NoEff.NCoerArrow (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    ( match f with
    | OCaml.Lambda (p_f, c_f) ->
      ( match g with
      | OCaml.Lambda (p_g, c_g) ->
          let x1 = Variable.fresh "coer_x1" in
          let x2 = Variable.fresh "coer_x2" in
          OCaml.Lambda (OCaml.PVar x1,
            OCaml.Lambda (OCaml.PVar x2,
              OCaml.Apply (g, OCaml.Apply (OCaml.Var x1, OCaml.Apply (f, OCaml.Var x2)))))
      | _ -> failwith "Wrong arrow coercion elaboration" )
    | _ -> failwith "Wrong arrow coercion elaboration" )
  | NoEff.NCoerHandler (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    ( match f with
    | OCaml.Lambda (p_f, c_f) ->
      match g with
      | OCaml.Lambda (p_g, c_g) ->
        let x1 = Variable.fresh "x1" in
        let x2 = Variable.fresh "x2" in
        OCaml.Lambda (OCaml.PVar x1,
          OCaml.Lambda (OCaml.PVar x2,
            OCaml.Apply (g,
              OCaml.Apply (OCaml.Var x1, OCaml.Return (OCaml.Apply (f, OCaml.Var x2))))))
    | _ -> failwith "Wrong handler coercion elaboration" )
  | NoEff.NCoerHandToFun (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    let x1 = Variable.fresh "x1" in
    let x2 = Variable.fresh "x2" in
    OCaml.Lambda (OCaml.PVar x1,
      OCaml.Lambda (OCaml.PVar x2,
        OCaml.Apply (g,
          OCaml.Apply (OCaml.Var x1, OCaml.Return (OCaml.Apply (f, OCaml.Var x2))))))
  | NoEff.NCoerFunToHand (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    let x1 = Variable.fresh "x1" in
    let x2 = Variable.fresh "x2" in
    let y = Variable.fresh "y" in
    OCaml.Lambda (OCaml.PVar x1, OCaml.Lambda (OCaml.PVar x2,
      OCaml.Match (OCaml.Var x2,
        [OCaml.ValueClause (OCaml.PReturn (OCaml.PVar y),
          OCaml.Apply (g, OCaml.Apply (OCaml.Var x1, OCaml.Apply (f, OCaml.Var y))))]
    )))
  | NoEff.NCoerQual (x, y) -> failwith "Dropped when dropping polymorphism"
  | NoEff.NCoerReturn c ->
    let f = elab_coercion c in
    let x = Variable.fresh "x" in
    ( match f with
    | OCaml.Lambda (p_f, c_f) ->
        OCaml.Lambda (OCaml.PVar x, OCaml.Return
          (OCaml.Apply (f, OCaml.Var x)))
    | _ -> failwith "Wrong return coercion elaboration" )
  | NoEff.NCoerComp c ->
    let f = elab_coercion c in
    let x = Variable.fresh "x" in
      OCaml.Lambda (PVar x, OCaml.Return
            (OCaml.Apply (f, (OCaml.Var x))))
  | NoEff.NCoerUnsafe c ->
    let f = elab_coercion c in
    ( match f with
    | OCaml.Lambda (f_pat, f_comp) ->
      let x = Variable.fresh "x" in
      let y = Variable.fresh "y" in
      OCaml.Lambda (OCaml.PVar x,
        OCaml.Match (OCaml.Var x,
          [OCaml.ValueClause (OCaml.PReturn (OCaml.PVar y), OCaml.Apply (f, OCaml.Var y))])) )
  | NoEff.NCoerApp (c1, c2) -> failwith "Dropped when dropping polymorphism"
  | NoEff.NCoerTrans (c1, c2) ->
    let f = elab_coercion c1 in
    let g = elab_coercion c2 in
    let x = Variable.fresh "x" in
    OCaml.Lambda (OCaml.PVar x,
      OCaml.Apply (f, OCaml.Apply (g, OCaml.Var x)))

and elab_type t =
  match t with
  | NoEff.NTyParam t -> OCaml.TyParam t
  | NoEff.NTyTuple ts -> OCaml.TyTuple (List.map elab_type ts)
  | NoEff.NTyArrow (ty1, ty2) -> OCaml.TyArrow (elab_type ty1, elab_type ty2)
  | NoEff.NTyHandler (ty1, ty2) -> OCaml.TyArrow (elab_type ty1, elab_type ty2)
  | NoEff.NTyApply (name, tys) -> OCaml.TyApply (name, List.map elab_type tys)
  | NoEff.NTyQual (_, _) -> failwith "No ty qual supported"
  | NoEff.NTyComp ty -> elab_type ty
  | NoEff.NTyApply _ -> failwith "No ty apply supported"
  | NoEff.NTyPrim ty -> OCaml.PrimTy (prim_to_string ty)

and elab_tydef = function
  | NoEff.TyDefRecord assoc -> OCaml.TyDefRecord (Assoc.map elab_type assoc)
  | NoEff.TyDefSum assoc -> OCaml.TyDefSum (Assoc.map help_sum assoc)
  | NoEff.TyDefInline ty -> OCaml.TyDefInline (elab_type ty)

and help_sum ty =
  match ty with
  | Some x -> Some (elab_type x)
  | None -> None

and prim_to_string ty =
  match ty with
  | NoEff.NInt -> "int"
  | NoEff.NBool -> "bool"
  | NoEff.NString -> "string"
  | NoEff.NFloat -> "float"

and elab_abstraction (p, c) = (elab_pattern p, elab_term c)

and elab_abstraction_with_ty (p, t, c) = (elab_pattern p, elab_type t, elab_term c)

and elab_abstraction_2 (p1, p2, c) = (elab_pattern p1, elab_pattern p2, elab_term c)

and elab_effect_clause ((eff, (t1, t2)), abs) = ((eff, elab_type t1, elab_type t2), elab_abstraction_2 abs)
