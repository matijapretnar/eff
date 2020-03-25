module NoEff = NoEffSyntax
module OCamn = OcamlSyntax

let rec elab_pattern in_p =
  match in_p with
  | NoEff.PNVar x -> OCaml.PVar x
  | NoEff.PNAs (p, x) -> OCaml.PAs (elab_pattern p, x)
  | NoEff.PNConst c -> OCaml.PConst c
  | NoEff.PNTuple lst -> OCaml.PTuple (List.map elab_pattern lst)
  | NoEff.PNRecord lst -> OCaml.PRecord
      (Assoc.map (fun (f, p) -> (f, elab_pattern p)) lst)
  | NoEff.PNVariant (lbl, None) -> OCaml.PVariant (lbl, None)
  | NoEff.PNVariant (lbl, Some p) -> OCaml.PVariant (lbl, Some (elab_pattern p))
  | NoEff.PNNonbinding -> OCaml.PNonbinding

let rec elab_term t_in =
  match t_in with
  | NoEff.NVar x -> OCaml.Var x
  | NoEff.NConst c -> OCaml.Const c
  | NoEff.NTuple lst -> OCaml.Tuple (List.map elab_term lst)
  | NoEff.NRecord lst -> OCaml.Record
      (Assoc.map (fun (f, t) -> (f, elab_term t)) lst)
  | NoEff.NVariant (lbl, None) -> OCaml.Variant (lbl, None)
  | NoEff.NVariant (lbl, Some t) -> OCaml.Variant (lbl, Some (elab_term t))
  | NoEff.NFun (x, _, c) ->
      OCaml.Lambda (elab_pattern x, elab_term c)
  | NoEff.NEffect eff -> OCaml.Effect eff
  (* TODO *)
  | NoEff.NHandler h ->
      print ~at_level:2
        "fun c -> handler {@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->\n             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]} c"
        (print_abstraction_with_ty h.Erasure.value_clause)
        (print_effect_clauses (Assoc.to_list h.Erasure.effect_clauses))
  | NoEff.NLetVal (p, e, c) ->
      OCaml.Let ((elab_pattern p, elab_term e), elab_term c)
  | NoEff.NApplyTerm (e1, e2) ->
      OCaml.Apply (elab_term e1, elab_term e2)
  | NoEff.Handle (e, c) ->
      OCaml.Apply (elab_term e, elab_term c)
  | NoEff.NCall (eff, e, (p, _, c)) ->
      OCaml.Call (eff, elab_term e, (elab_pattern p, elab_pattern c))
  (* TODO *)
  | NoEff.NBind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_term ~max_level:0 c1)
        (print_abstraction a)
  | NoEff.NMatch (e, alist) ->
      OCaml.Match (elab_term e,
        List.map (fun (p, c) ->
          OCaml.ValueClause (elab_pattern p, elab_pattern c)) alist)
  | NoEff.NLetRec (alist, c) ->
      let alist' = List.map (fun (v, _, _, (p, c))
                  -> (v, (elab_pattern p, elab_pattern c))) alist in
      OCaml.LetRec (alist*, elab_term c)
  | NoEff.NOp (eff, t) -> failwith "No operations supposed to happen"
  | NoEff.NBigLambdaCoer (p, c, t)-> failwith "Not supported without polymorphism"
  | NoEff.NApplyCoer (t, c) -> failwith "Not supported without polymorphism"
  | NoEff.NCast (t, c) -> OCaml.Apply (elab_coercion c, elab_term t)
  | NoEff.NReturn t -> OCaml.Return (elab_term t)

and elab_coercion (coer: NoEff.n_coercion): OCaml.term =
  match coer with
  | NoEff.NCoerRefl t ->
    let x = CoreTypes.Variable.new_fresh in
    OCaml.Lambda (OCaml.PVar x, OCaml.Var x)
  | NoEff.NCoerArrow (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    match f with
    | OCaml.Lambda (p_f, c_f) ->
      match g with
      | OCaml.Lambda (p_g, c_g) ->
        let x1 = CoreTypes.Variable.new_fresh in
        let x2 = CoreTypes.Variable.new_fresh in
        OCaml.Lambda (OCaml.PVar x1,
          OCaml.Lambda (OCaml.PVar x2,
            OCaml.Apply (g, OCaml.Apply (OCaml.Var x1, OCaml.Apply (f, OCaml.Var x2)))))
    | _ -> failwith "Wrong arrow coercion elaboration"
  | NoEff.NCoerHandler (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    match f with
    | OCaml.Lambda (p_f, c_f) ->
      match g with
      | OCaml.Lambda (p_g, c_g) ->
        let x1 = CoreTypes.Variable.new_fresh in
        let x2 = CoreTypes.Variable.new_fresh in
        OCaml.Lambda (OCaml.PVar x1,
          OCaml.Lambda (OCaml.PVar x2,
            OCaml.Apply (g,
              OCaml.Apply (OCaml.PVar x1, OCaml.Return (OCaml.Apply (f, OCaml.Var x2))))
    | _ -> failwith "Wrong handler coercion elaboration"
  | NoEff.NCoerHandToFun (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    let x1 = CoreTypes.Variable.new_fresh in
    let x2 = CoreTypes.Variable.new_fresh in
    OCaml.Lambda (OCaml.PVar x1,
      OCaml.Lambda (OCaml.PVar x2,
        OCaml.Apply (g,
          OCaml.Apply (OCaml.Var x1, OCaml.Return (OCaml.Apply (f, OCaml.Var x2))))))
  | NoEff.NCoerFunToHand (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    let x1 = CoreTypes.Variable.new_fresh in
    let x2 = CoreTypes.Variable.new_fresh in
    OCaml.Lambda (OCaml.PVar x1, OCaml.Lambda (OCaml.PVar x2,
      OCaml.Match (OCaml.Var x2,
        (OCaml.ValueClause (OCaml.PReturn y,
          OCaml.Apply (g, OCaml.Apply (OCaml.Var x1, OCaml.Apply (f, elab_term y)))))
    )))
  | NoEff.NCoerQual -> failwith "Dropped when dropping polymorphism"
  | NoEff.NCoerReturn c ->
    let f = elab_coercion c in
    let x = CoreTypes.Variable.new_fresh in
    match f with
    | OCaml.Lambda (p_f, c_f) ->
        OCaml.Lambda (OCaml.PVar x, OCaml.Return
          (OCaml.Apply (f, OCaml.Var x)))
    | _ -> failwith "Wrong return coercion elaboration"
  | NoEff.NCoerComp c ->
    let f = elab_coercion c in
    let x = CoreTypes.Variable.new_fresh in
      OCaml.Lambda (PVar x,
        OCaml.Match (OCaml.Var x,
          (OCaml.ValueClause (OCaml.PReturn y, OCaml.Return
            (OCaml.Apply (f, y))))
      fun m -> m >>= \x -> NoEff.NReturn (NoEff.NApplyTerm )
  | NoEff.NCoerUnsafe c ->
    let f = elab_coercion c in
    match f with
    | OCaml.Lambda (f_pat, f_comp) ->
      let x = CoreTypes.Variable.new_fresh in
      OCaml.Lambda (OCaml.PVar x,
        OCaml.Match (OCaml.Var x,
          (OCaml.ValueClause (OCaml.PReturn y, OCaml.Apply (f, elab_term y)))
  | NoEff.NCoerApp (c1, c2) -> failwith "Dropped when dropping polymorphism"
  | NoEff.NCoerTrans (c1, c2) ->
    let f = elab_coercion c1 in
    let g = elab_coercion c2 in
    let x = CoreTypes.Variable.new_fresh in
    OCaml.Lambda (OCaml.PVar x,
      OCaml.Apply (f, OCaml.Apply (g, OCaml.Var x)))
