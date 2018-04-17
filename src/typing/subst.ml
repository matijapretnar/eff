
(**************************)
(* SUBSTITUTION FUNCTIONS *)
(**************************)

let rec subst_expr sbst e =
  {e with term = subst_expr' sbst e.term}
and subst_expr' sbst = function
  | (Var x) as e ->
    begin match Common.lookup x sbst with
      | Some e' -> e'
      | None -> e
    end
  | Lambda a ->
    assert false
  | Handler h ->
    Handler (subst_handler sbst h)
  | Tuple es ->
    Tuple (List.map (subst_expr sbst) es)
  | Record flds ->
    Record (Common.assoc_map (subst_expr sbst) flds)
  | Variant (lbl, e) ->
    Variant (lbl, Common.option_map (subst_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
and subst_comp sbst c =
  {c with term = subst_comp' sbst c.term}
and subst_comp' sbst = function
  | Bind (c1, c2) ->
    Bind (subst_comp sbst c1, subst_abs sbst c2)
  | LetRec (li, c1) ->
    let li' = List.map (fun (x, a) ->
        (* XXX Should we check that x does not appear in sbst? *)
        (x, subst_abs sbst a)
      ) li
    in
    LetRec (li', subst_comp sbst c1)
  | Match (e, li) ->
    Match (subst_expr sbst e, List.map (subst_abs sbst) li)
  | Apply (e1, e2) ->
    Apply (subst_expr sbst e1, subst_expr sbst e2)
  | Handle (e, c) ->
    Handle (subst_expr sbst e, subst_comp sbst c)
  | Call (eff, e, a) ->
    Call (eff, subst_expr sbst e, subst_abs sbst a)
  | Value e ->
    Value (subst_expr sbst e)
and subst_handler sbst h = {
  effect_clauses = Common.assoc_map (subst_abs2 sbst) h.effect_clauses;
  value_clause = subst_abs sbst h.value_clause;
}
and subst_abs sbst a =
  let (p, c) = a.term in
  (* XXX Should we check that p & sbst have disjoint variables? *)
  {a with term = (p, subst_comp sbst c)}
and subst_abs2 sbst a2 =
  (* a2a2 @@ subst_abs sbst @@ a22a @@ a2 *)
  assert false

(********************)
(* HELPER FUNCTIONS *)
(********************)

let assoc_equal eq flds flds' : bool =
  let rec equal_fields flds =
    match flds with
    | [] -> true
    | (f, x) :: flds ->
      begin match Common.lookup f flds' with
        | Some x' when eq x x' -> equal_fields flds
        | _ -> false
      end
  in
  List.length flds = List.length flds' &&
  equal_fields flds

let rec make_equal_pattern eqvars p p' =
  make_equal_pattern' eqvars p.term p'.term
and make_equal_pattern' eqvars p p' =
  match p, p' with
  | PVar x, PVar x' -> Some ((x, x') :: eqvars)
  | PAs (p, x), PAs (p', x') ->
    Common.option_map (fun eqvars ->
        (x, x') :: eqvars
      ) (make_equal_pattern eqvars p p')
  | PTuple ps, PTuple ps' ->
    List.fold_right2 (fun p p' -> function
        | Some eqvars' -> make_equal_pattern eqvars' p p'
        | None -> None
      ) ps ps' (Some eqvars)
  | PConst cst, PConst cst' when Const.equal cst cst' -> Some eqvars
  | PNonbinding, PNonbinding -> Some eqvars
  | PVariant (lbl, None), PVariant (lbl', None) when lbl = lbl' -> Some eqvars
  | PVariant (lbl, Some p), PVariant (lbl', Some p') when lbl = lbl' ->
      make_equal_pattern eqvars p p'
  | _, _ -> None

let rec alphaeq_expr eqvars e e' =
  alphaeq_expr' eqvars e.term e'.term
and alphaeq_expr' eqvars e e' =
  match e, e' with
  | Var x, Var y ->
    List.mem (x, y) eqvars ||  Variable.compare x y = 0
  | Lambda a, Lambda a' ->
    assert false
  | Handler h, Handler h' ->
    alphaeq_handler eqvars h h'
  | Tuple es, Tuple es' ->
    List.for_all2 (alphaeq_expr eqvars) es es'
  | Record flds, Record flds' ->
    assoc_equal (alphaeq_expr eqvars) flds flds'
  | Variant (lbl, None), Variant (lbl', None) ->
    lbl = lbl'
  | Variant (lbl, Some e), Variant (lbl', Some e') ->
    lbl = lbl' && alphaeq_expr eqvars e e'
  | BuiltIn (f, n), BuiltIn (f', n') ->
    f = f' && n = n'
  | Const cst, Const cst' ->
    Const.equal cst cst'
  | Effect eff, Effect eff' ->
    eff = eff'
  | _, _ -> false
and alphaeq_comp eqvars c c' =
  alphaeq_comp' eqvars c.term c'.term
and alphaeq_comp' eqvars c c' =
  match c, c' with
  | Bind (c1, c2), Bind (c1', c2') ->
    alphaeq_comp eqvars c1 c1' && alphaeq_abs eqvars c2 c2'
  | LetRec (li, c1), LetRec (li', c1') ->
    (* XXX Not yet implemented *)
    false
  | Match (e, li), Match (e', li') ->
    alphaeq_expr eqvars e e' && List.for_all2 (alphaeq_abs eqvars) li li'
  | Apply (e1, e2), Apply (e1', e2') ->
    alphaeq_expr eqvars e1 e1' && alphaeq_expr eqvars e2 e2'
  | Handle (e, c), Handle (e', c') ->
    alphaeq_expr eqvars e e' && alphaeq_comp eqvars c c'
  | Call (eff, e, a), Call (eff', e', a') ->
    eff = eff' && alphaeq_expr eqvars e e' && alphaeq_abs eqvars a a'
  | Value e, Value e' ->
    alphaeq_expr eqvars e e'
  | _, _ -> false
and alphaeq_handler eqvars h h' =
  assoc_equal (alphaeq_abs2 eqvars) h.effect_clauses h'.effect_clauses &&
  alphaeq_abs eqvars h.value_clause h'.value_clause
and alphaeq_abs eqvars {term = (p, c)} {term = (p', c')} =
  match make_equal_pattern eqvars p p' with
  | Some eqvars' -> alphaeq_comp eqvars' c c'
  | None -> false
and alphaeq_abs2 eqvars a2 a2' =
  (* alphaeq_abs eqvars (a22a a2) (a22a a2') *)
  assert false

let pattern_match p e =
  (* XXX The commented out part checked that p and e had matching types *)
(*   let _, ty_e, constraints_e = e.scheme
  and _, ty_p, constraints_p = p.scheme in
  let constraints =
    Constraints.union constraints_e constraints_p |>
    Constraints.add_ty_constraint ~loc:e.location ty_e ty_p
  in
  ignore constraints; *)
  let rec extend_subst p e sbst =
    match p.term, e.term with
    | PVar x, e -> Common.update x e sbst
    | PAs (p, x), e' ->
      let sbst = extend_subst p e sbst in
      Common.update x e' sbst
    | PNonbinding, _ -> sbst
    | PTuple ps, Tuple es -> List.fold_right2 extend_subst ps es sbst
    | PRecord ps, Record es ->
      begin
        let rec extend_record ps es sbst =
          match ps with
          | [] -> sbst
          | (f, p) :: ps ->
            let e = List.assoc f es in
            extend_record ps es (extend_subst p e sbst)
        in
        try
          extend_record ps es sbst
        with Not_found -> Error.runtime ~loc:e.location "Incompatible records in substitution."
      end
    | PVariant (lbl, None), Variant (lbl', None) when lbl = lbl' -> sbst
    | PVariant (lbl, Some p), Variant (lbl', Some e) when lbl = lbl' ->
      extend_subst p e sbst
    | PConst c, Const c' when Const.equal c c' -> sbst
    | _, _ -> Error.runtime ~loc:e.location "Cannot substitute an expression in a pattern."
  in
  extend_subst p e []

let (@@@) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)
let (---) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)
let concat_vars vars = List.fold_right (@@@) vars ([], [])

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_expr e
  | LetRec (li, c1) ->
    let xs, vars = List.fold_right (fun (x, a) (xs, vars) ->
        x :: xs, free_vars_abs a @@@ vars
      ) li ([], free_vars_comp c1) in
    vars --- xs
  | Match (e, li) -> free_vars_expr e @@@ concat_vars (List.map free_vars_abs li)
  | Apply (e1, e2) -> free_vars_expr e1 @@@ free_vars_expr e2
  | Handle (e, c1) -> free_vars_expr e @@@ free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_expr e1 @@@ free_vars_abs a1
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
and free_vars_expr e =
  match e.term with
  | Var v -> ([], [v])
  | Tuple es -> concat_vars (List.map free_vars_expr es)
  | Lambda a -> assert false
  | Handler h -> free_vars_handler h
  | Record flds -> concat_vars (List.map (fun (_, e) -> free_vars_expr e) flds)
  | Variant (_, None) -> ([], [])
  | Variant (_, Some e) -> free_vars_expr e
  | (BuiltIn _ | Effect _ | Const _) -> ([], [])
and free_vars_handler h =
  free_vars_abs h.value_clause @@@
  concat_vars (List.map (fun (_, a2) -> free_vars_abs2 a2) h.effect_clauses)
and free_vars_finally_handler (h, finally_clause) =
  free_vars_handler h @@@
  free_vars_abs finally_clause
and free_vars_abs a =
  let (p, c) = a.term in
  let (inside, outside) = free_vars_comp c --- pattern_vars p in
  (inside @ outside, [])
and free_vars_abs2 a2 =
  (* free_vars_abs @@ a22a @@ a2 *)
  assert false

let occurrences x (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x = y) ys) in
  (count inside, count outside)