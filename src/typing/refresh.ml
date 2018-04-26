(************************)
(* REFRESHING FUNCTIONS *)
(************************)
module Variable = Symbol.Make(Symbol.String)

let rec refresh_pattern sbst p =
  let sbst', p' = refresh_pattern' sbst p.Typed.term in
  sbst', {p with Typed.term = p'}
and refresh_pattern' sbst = function
  | Typed.PVar x ->
    let x' = Variable.refresh x in
    OldUtils.update x x' sbst, Typed.PVar x'
  | Typed.PAs (p, x) ->
    let x' = Variable.refresh x in
    let sbst, p' = refresh_pattern (OldUtils.update x x' sbst) p in
    sbst, Typed.PAs (p', x')
  | Typed.PTuple ps ->
    let sbst, ps' =
      List.fold_right (fun p (sbst, ps') ->
          let sbst, p' = refresh_pattern sbst p in
          sbst, p' :: ps'
        ) ps (sbst, []) in
    sbst, Typed.PTuple ps'
  | Typed.PRecord flds ->
    let sbst, flds' =
      List.fold_right (fun (lbl, p) (sbst, flds') ->
          let sbst, p' = refresh_pattern sbst p in
          sbst, (lbl, p') :: flds'
        ) flds (sbst, []) in
    sbst, Typed.PRecord flds'
  | Typed.PVariant (lbl, None) ->
    sbst, Typed.PVariant (lbl, None)
  | Typed.PVariant (lbl, Some p) ->
    let sbst, p' = refresh_pattern sbst p in
    sbst, Typed.PVariant (lbl, Some p')
  | (Typed.PConst _ | Typed.PNonbinding) as p -> sbst, p

let rec refresh_expr sbst e =
  {e with Typed.term = refresh_expr' sbst e.Typed.term}
and refresh_expr' sbst = function
  | (Typed.LetVar x) as e ->
    begin match OldUtils.lookup x sbst with
      | Some x' -> Typed.LetVar x'
      | None -> e
    end
  | (Typed.LambdaVar x) as e ->
    begin match OldUtils.lookup x sbst with
      | Some x' -> Typed.LambdaVar x'
      | None -> e
    end
   | Typed.Lambda a ->
    assert false
  | Typed.Handler h ->
    Typed.Handler (refresh_handler sbst h)
  | Typed.Tuple es ->
    Typed.Tuple (List.map (refresh_expr sbst) es)
  | Typed.Record flds ->
    Typed.Record (OldUtils.assoc_map (refresh_expr sbst) flds)
  | Typed.Variant (lbl, e) ->
    Typed.Variant (lbl, OldUtils.option_map (refresh_expr sbst) e)
  | (Typed.BuiltIn _ | Typed.Const _ | Typed.Effect _) as e -> e
and refresh_comp sbst c =
  {c with Typed.term = refresh_comp' sbst c.Typed.term}
and refresh_comp' sbst = function
  | Typed.Bind (c1, c2) ->
    Typed.Bind (refresh_comp sbst c1, refresh_abs sbst c2)
  | Typed.LetRec (li, c1) ->
    let new_xs, sbst' = List.fold_right (fun (x, _) (new_xs, sbst') ->
        let x' = Variable.refresh x in
        x' :: new_xs, OldUtils.update x x' sbst'
      ) li ([], sbst) in
    let li' =
      List.combine new_xs (List.map (fun (_, a) -> refresh_abs sbst' a) li)
    in
    Typed.LetRec (li', refresh_comp sbst' c1)
  | Typed.Match (e, li) ->
    Typed.Match (refresh_expr sbst e, List.map (refresh_abs sbst) li)
  | Typed.Apply (e1, e2) ->
    Typed.Apply (refresh_expr sbst e1, refresh_expr sbst e2)
  | Typed.Handle (e, c) ->
    Typed.Handle (refresh_expr sbst e, refresh_comp sbst c)
  | Typed.Call (eff, e, a) ->
    Typed.Call (eff, refresh_expr sbst e, refresh_abs sbst a)
  | Typed.Value e ->
    Typed.Value (refresh_expr sbst e)
and refresh_handler sbst h = {
  effect_clauses = OldUtils.assoc_map (refresh_abs2 sbst) h.effect_clauses;
  value_clause = refresh_abs sbst h.value_clause;
}
and refresh_abs sbst a =
  let (p, c) = a.Typed.term in
  let sbst, p' = refresh_pattern sbst p in
  {a with Typed.term = (p', refresh_comp sbst c)}
and refresh_abs2 sbst a2 =
  (* a2a2 @@ refresh_abs sbst @@ a22a @@ a2 *)
  assert false
