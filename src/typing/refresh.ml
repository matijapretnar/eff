
(************************)
(* REFRESHING FUNCTIONS *)
(************************)

let rec refresh_pattern sbst p =
  let sbst', p' = refresh_pattern' sbst p.term in
  sbst', {p with term = p'}
and refresh_pattern' sbst = function
  | PVar x ->
    let x' = Variable.refresh x in
    Common.update x x' sbst, PVar x'
  | PAs (p, x) ->
    let x' = Variable.refresh x in
    let sbst, p' = refresh_pattern (Common.update x x' sbst) p in
    sbst, PAs (p', x')
  | PTuple ps ->
    let sbst, ps' =
      List.fold_right (fun p (sbst, ps') ->
          let sbst, p' = refresh_pattern sbst p in
          sbst, p' :: ps'
        ) ps (sbst, []) in
    sbst, PTuple ps'
  | PRecord flds ->
    let sbst, flds' =
      List.fold_right (fun (lbl, p) (sbst, flds') ->
          let sbst, p' = refresh_pattern sbst p in
          sbst, (lbl, p') :: flds'
        ) flds (sbst, []) in
    sbst, PRecord flds'
  | PVariant (lbl, None) ->
    sbst, PVariant (lbl, None)
  | PVariant (lbl, Some p) ->
    let sbst, p' = refresh_pattern sbst p in
    sbst, PVariant (lbl, Some p')
  | (PConst _ | PNonbinding) as p -> sbst, p

let rec refresh_expr sbst e =
  {e with term = refresh_expr' sbst e.term}
and refresh_expr' sbst = function
  | (Var x) as e ->
    begin match Common.lookup x sbst with
      | Some x' -> Var x'
      | None -> e
    end
   | Lambda a ->
    assert false
  | Handler h ->
    Handler (refresh_handler sbst h)
  | Tuple es ->
    Tuple (List.map (refresh_expr sbst) es)
  | Record flds ->
    Record (Common.assoc_map (refresh_expr sbst) flds)
  | Variant (lbl, e) ->
    Variant (lbl, Common.option_map (refresh_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
and refresh_comp sbst c =
  {c with term = refresh_comp' sbst c.term}
and refresh_comp' sbst = function
  | Bind (c1, c2) ->
    Bind (refresh_comp sbst c1, refresh_abs sbst c2)
  | LetRec (li, c1) ->
    let new_xs, sbst' = List.fold_right (fun (x, _) (new_xs, sbst') ->
        let x' = Variable.refresh x in
        x' :: new_xs, Common.update x x' sbst'
      ) li ([], sbst) in
    let li' =
      List.combine new_xs (List.map (fun (_, a) -> refresh_abs sbst' a) li)
    in
    LetRec (li', refresh_comp sbst' c1)
  | Match (e, li) ->
    Match (refresh_expr sbst e, List.map (refresh_abs sbst) li)
  | Apply (e1, e2) ->
    Apply (refresh_expr sbst e1, refresh_expr sbst e2)
  | Handle (e, c) ->
    Handle (refresh_expr sbst e, refresh_comp sbst c)
  | Call (eff, e, a) ->
    Call (eff, refresh_expr sbst e, refresh_abs sbst a)
  | Value e ->
    Value (refresh_expr sbst e)
and refresh_handler sbst h = {
  effect_clauses = Common.assoc_map (refresh_abs2 sbst) h.effect_clauses;
  value_clause = refresh_abs sbst h.value_clause;
}
and refresh_abs sbst a =
  let (p, c) = a.term in
  let sbst, p' = refresh_pattern sbst p in
  {a with term = (p', refresh_comp sbst c)}
and refresh_abs2 sbst a2 =
  (* a2a2 @@ refresh_abs sbst @@ a22a @@ a2 *)
  assert false
