(** Desugaring of syntax into the core language. *)

module C = Common
module T = Type

(** [fresh_variable ()] creates a fresh variable ["$gen1"], ["$gen2"], ... on
    each call *)
let fresh_variable =
  let next_variable = Common.fresh "variable" in
  fun () -> "$gen" ^ string_of_int (next_variable ())

let id_abstraction pos =
  let x = fresh_variable () in
  ((Pattern.Var x, pos), (Core.Value (Core.Var x, pos), pos))


(** [ty s k t] desugars type [t] where it applies the substitution [s] to parameters. *)
let rec ty_fv = function
  | Syntax.TyApply (_, lst) -> List.flatten (List.map ty_fv lst)
  | Syntax.TyParam s -> [s]
  | Syntax.TyArrow (t1, t2) -> ty_fv t1 @ ty_fv t2
  | Syntax.TyTuple lst -> List.flatten (List.map ty_fv lst)
  | Syntax.TyHandler (t1, t2) -> ty_fv t1 @ ty_fv t2

let rec ty s = function
  | Syntax.TyApply (t, lst) -> T.Apply (t, List.map (ty s) lst)
  | Syntax.TyParam str ->
    begin match C.lookup str s with
    | None -> Error.syntax ~pos:C.Nowhere "Unbound type parameter '%s" str
    | Some t -> t
    end
  | Syntax.TyArrow (t1, t2) -> T.Arrow (ty s t1, (ty s t2, Type.fresh_dirt ()))
  | Syntax.TyTuple lst -> T.Tuple (List.map (ty s) lst)
  | Syntax.TyHandler (t1, t2) -> T.Handler { T.value = ty s t1; T.finally = ty s t2 }

let external_ty t =
  let lst = List.fold_right (fun p lst -> (p, Type.fresh_ty_param ()) :: lst) (ty_fv t) [] in
  let s = C.assoc_map (fun p -> Type.TyParam p) lst in
  (* XXX fix this, the dirt and region parameters are wrong *)
  ((List.map snd lst, [], []), ty s t)


(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec expression (t, pos) =
  let w, e = match t with
  | Syntax.Var x ->
      [], Core.Var x
  | Syntax.Const k ->
      [], Core.Const k
  | Syntax.Lambda a ->
      let a = abstraction a in
      [], Core.Lambda a
  | Syntax.Function cs ->
      let x = fresh_variable () in
      let cs = List.map abstraction cs in
      [], Core.Lambda ((Pattern.Var x, pos), (Core.Match ((Core.Var x, pos), cs), pos))
  | Syntax.Handler cs ->
      let w, h = handler pos cs in
      w, Core.Handler h
  | Syntax.Tuple ts ->
      let w, es = expressions ts in
      w, Core.Tuple es
  | Syntax.Record ts ->
      if not (C.injective fst ts) then Error.syntax ~pos "Fields in a record must be distinct";
      let w, es = record_expressions ts in
      w, Core.Record es
  | Syntax.Variant (lbl, None) ->
      [], Core.Variant (lbl, None)
  | Syntax.Variant (lbl, Some t) ->
      let w, e = expression t in
      w, Core.Variant (lbl, Some e)
  | Syntax.Operation (t, op) ->
      let w, e = expression t in
      w, Core.Operation (e, op)
  (* Terms that are desugared into computations. We list them explicitly in
     order to catch any future constructs. *)
  | Syntax.Apply _ | Syntax.Match _ | Syntax.Let _ | Syntax.LetRec _
  | Syntax.Handle _ | Syntax.Conditional _ | Syntax.While _ | Syntax.For _ | Syntax.New _ | Syntax.Check _ ->
      let x = fresh_variable () in
      let c = computation (t, pos) in
      let w = [(Pattern.Var x, pos), c] in
      w, Core.Var x
  in
  w, (e, pos)

and computation (t, pos) =
  let w, c = match t with
    | Syntax.Apply ((Syntax.Apply ((Syntax.Var "&&", pos1), t1), pos2), t2) ->
      let w1, e1 = expression t1 in
      let c2 = computation t2 in
          w1, Core.Match (e1, [((Pattern.Const (C.Boolean false), pos1), (Core.Value (Core.Const (C.Boolean false), C.Nowhere), pos1));
                            ((Pattern.Const (C.Boolean true), pos2), c2)])
    | Syntax.Apply ((Syntax.Apply ((Syntax.Var "||", pos1), t1), pos2), t2) ->
      let w1, e1 = expression t1 in
      let c2 = computation t2 in
          w1, Core.Match (e1, [((Pattern.Const (C.Boolean true), pos1), (Core.Value (Core.Const (C.Boolean true), C.Nowhere), pos1));
                            ((Pattern.Const (C.Boolean false), pos2), c2)])
    | Syntax.Apply (t1, t2) ->
        let w1, e1 = expression t1 in
        let w2, e2 = expression t2 in
          (w1 @ w2), Core.Apply (e1, e2)
    | Syntax.Match (t, cs) ->
        let cs = List.map abstraction cs in
        let w, e = expression t in
          w, Core.Match (e, cs)
    | Syntax.New (eff, None) ->
        [], Core.New (eff, None)
    | Syntax.New (eff, Some (t, lst)) ->
        let w, e = expression t in
        let lst = List.map (fun (op, a) -> (op, abstraction2 a)) lst in
          w, Core.New (eff, Some (e, lst))
    | Syntax.Handle (t1, t2) ->
        let w1, e1 = expression t1 in
        let c2 = computation t2 in
          w1, Core.Handle (e1, c2)
    | Syntax.Conditional (t, t1, t2) ->
        let w, e = expression t in
        let c1 = computation t1 in
        let c2 = computation t2 in
          w, Core.Match (e, [((Pattern.Const (C.Boolean true), C.Nowhere), c1);
                          ((Pattern.Const (C.Boolean false), C.Nowhere), c2)])
    | Syntax.While (t1, t2) ->
        let c1 = computation t1 in
        let c2 = computation t2 in
          [], Core.While (c1, c2)

    | Syntax.For (i, t1, t2, t, b) ->
      let w1, e1 = expression t1 in
      let w2, e2 = expression t2 in
      let c = computation t in
        w1 @ w2, Core.For (i, e1, e2, c, b)
    | Syntax.Check t ->
        [], Core.Check (computation t)
    | Syntax.Let (defs, t) ->
        let defs = C.assoc_map computation defs in
        let c = computation t in
          [], Core.Let (defs, c)
    | Syntax.LetRec (defs, t) ->
        let defs = C.assoc_map let_rec defs in
        let c = computation t in
          [], Core.LetRec (defs, c)
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | (Syntax.Var _ | Syntax.Const _ | Syntax.Tuple _ | Syntax.Record _  | Syntax.Variant _ | Syntax.Lambda _ | Syntax.Function _ | Syntax.Handler _ | Syntax.Operation _) ->
        let w, e = expression (t, pos) in
          w, Core.Value e
  in
    match w with
      | [] -> (c, pos)
      | _ :: _ -> Core.Let (w, (c, pos)), pos

and abstraction (p, t) = (p, computation t)

and abstraction2 (p1, p2, t) = (p1, p2, computation t)

and let_rec = function
  | (Syntax.Lambda (p, t), _) -> (p, computation t)
  | (Syntax.Function cs, pos) ->
    let x = fresh_variable () in
    let cs = List.map abstraction cs in
    ((Pattern.Var x, pos), (Core.Match ((Core.Var x, pos), cs), pos))
  | (_, pos) -> Error.syntax ~pos "This kind of expression is not allowed in a recursive definition"

and expressions = function
  | [] -> [], []
  | t :: ts ->
    let w, e = expression t in
    let ws, es = expressions ts in
    w @ ws, (e :: es)

and record_expressions = function
  | [] -> [], []
  | (f, t) :: ts ->
    let w, e = expression t in
    let ws, es = record_expressions ts in
    w @ ws, ((f, e) :: es)

and handler pos {Syntax.operations=ops; Syntax.value=val_a; Syntax.finally=fin_a} =
  let rec operation_cases = function
  | [] -> [], []
  | ((t, op), a2) :: cs ->
    let w, e = expression t in
    let ws, cs' = operation_cases cs in
    w @ ws, ((e, op), abstraction2 a2) :: cs'
  in
  let ws, ops = operation_cases ops in
  ws, { Core.operations = ops;
    Core.value =
      (match val_a with None -> id_abstraction pos | Some a -> abstraction a);
    Core.finally =
      (match fin_a with None -> id_abstraction pos | Some a -> abstraction a)}

(** [tydef t ps d] desugars the definition of type [t] with parameters [ps]
    and definition [d]. *)
let tydef ps d =
  let sbst, lst = 
    List.fold_right (fun p (sbst,lst) ->
                       let u = Type.fresh_ty_param () in
                         (p, T.TyParam u)::sbst, u::lst) ps ([],[])
  in
    ((lst, [], []),
     begin match d with
       | Syntax.TyRecord lst -> Tctx.Record (List.map (fun (f,t) -> (f, ty sbst t)) lst)
       | Syntax.TySum lst -> Tctx.Sum (List.map (fun (lbl, t) -> (lbl, C.option_map (ty sbst) t)) lst)
       | Syntax.TyEffect lst -> Tctx.Effect (List.map (fun (op,(t1,t2)) -> (op, (ty sbst t1, ty sbst t2))) lst)
       | Syntax.TyInline t -> Tctx.Inline (ty sbst t)
     end)
