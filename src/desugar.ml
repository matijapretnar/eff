(** Desugaring of syntax into the intermediate language. *)

module C = Common
module S = Syntax
module I = Inter
module T = Type

let id_abstraction pos =
  let x = C.fresh_variable () in
  ((Pattern.Var x, pos), (I.Value (I.Var x, pos), pos))


(** [ty s k t] desugars type [t] where it applies the substitution [s] to parameters. *)
let rec ty_fv = function
  | S.TyApply (_, lst) -> List.flatten (List.map ty_fv lst)
  | S.TyParam s -> [s]
  | S.TyArrow (t1, t2) -> ty_fv t1 @ ty_fv t2
  | S.TyTuple lst -> List.flatten (List.map ty_fv lst)
  | S.TyHandler (t1, t2) -> ty_fv t1 @ ty_fv t2

let rec ty s = function
  | S.TyApply (t, lst) -> T.Apply (t, List.map (ty s) lst)
  | S.TyParam str ->
    begin match C.lookup str s with
    | None -> Error.syntax "Unbound type parameter '%s" str
    | Some t -> t
    end
  | S.TyArrow (t1, t2) -> T.Arrow (ty s t1, ty s t2)
  | S.TyTuple lst -> T.Tuple (List.map (ty s) lst)
  | S.TyHandler (t1, t2) -> T.Handler { T.value = ty s t1; T.finally = ty s t2 }

let external_ty t =
  let lst = List.fold_right (fun p lst -> (p, Type.next_param ()) :: lst) (ty_fv t) [] in
  let s = C.assoc_map (fun p -> Type.Param p) lst in
  (List.map snd lst, ty s t)


(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec expression (t, pos) =
  let w, e = match t with
  | S.Var x ->
      [], I.Var x
  | S.Const k ->
      [], I.Const k
  | S.Lambda a ->
      let a = abstraction a in
      [], I.Lambda a
  | S.Function cs ->
    let x = C.fresh_variable () in
    let cs = List.map abstraction cs in
    [], I.Lambda ((Pattern.Var x, pos), (I.Match ((I.Var x, pos), cs), pos))
  | S.Handler cs ->
      let w, h = handler pos cs in
      w, I.Handler h
  | S.Tuple ts ->
      let w, es = expressions ts in
      w, I.Tuple es
  | S.Record ts ->
      if not (C.injective fst ts) then Error.syntax ~pos:pos "Fields in a record must be distinct" ;
      let w, es = record_expressions ts in
      w, I.Record es
  | S.Variant (lbl, None) ->
      [], I.Variant (lbl, None)
  | S.Variant (lbl, Some t) ->
      let w, e = expression t in
      w, I.Variant (lbl, Some e)
  | S.Operation (t, op) ->
      let w, e = expression t in
      w, I.Operation (e, op)
  (* Terms that are desugared into computations. We list them explicitly in
     order to catch any future constructs. *)
  | S.Apply _ | S.Match _ | S.Let _ | S.LetRec _
  | S.Handle _ | S.Conditional _ | S.While _ | S.For _ | S.New _ | S.Check _ ->
      let x = C.fresh_variable () in
      let c = computation (t, pos) in
      let w = [(Pattern.Var x, pos), c] in
      w, I.Var x
  in
  w, (e, pos)

and computation (t, pos) =
  let w, c = match t with
    | S.Apply ((S.Apply ((S.Var "&&", pos1), t1), pos2), t2) ->
      let w1, e1 = expression t1 in
      let c2 = computation t2 in
          w1, I.Match (e1, [((Pattern.Const (C.Boolean false), pos1), (I.Value (I.Const (C.Boolean false), C.Nowhere), pos1));
                            ((Pattern.Const (C.Boolean true), pos2), c2)])
    | S.Apply ((S.Apply ((S.Var "||", pos1), t1), pos2), t2) ->
      let w1, e1 = expression t1 in
      let c2 = computation t2 in
          w1, I.Match (e1, [((Pattern.Const (C.Boolean true), pos1), (I.Value (I.Const (C.Boolean true), C.Nowhere), pos1));
                            ((Pattern.Const (C.Boolean false), pos2), c2)])
    | S.Apply (t1, t2) ->
        let w1, e1 = expression t1 in
        let w2, e2 = expression t2 in
          (w1 @ w2), I.Apply (e1, e2)
    | S.Match (t, cs) ->
        let cs = List.map abstraction cs in
        let w, e = expression t in
          w, I.Match (e, cs)
    | S.New (eff, None) ->
        [], I.New (eff, None)
    | S.New (eff, Some (t, lst)) ->
        let w, e = expression t in
        let lst = List.map (fun (op, a) -> (op, abstraction2 a)) lst in
          w, I.New (eff, Some (e, lst))
    | S.Handle (t1, t2) ->
        let w1, e1 = expression t1 in
        let c2 = computation t2 in
          w1, I.Handle (e1, c2)
    | S.Conditional (t, t1, t2) ->
        let w, e = expression t in
        let c1 = computation t1 in
        let c2 = computation t2 in
          w, I.Match (e, [((Pattern.Const (C.Boolean true), C.Nowhere), c1);
                          ((Pattern.Const (C.Boolean false), C.Nowhere), c2)])
    | S.While (t1, t2) ->
        let c1 = computation t1 in
        let c2 = computation t2 in
          [], I.While (c1, c2)

    | S.For (i, t1, t2, t, b) ->
      let w1, e1 = expression t1 in
      let w2, e2 = expression t2 in
      let c = computation t in
        w1 @ w2, I.For (i, e1, e2, c, b)
    | S.Check t ->
        [], I.Check (computation t)
    | S.Let (defs, t) ->
        let defs = C.assoc_map computation defs in
        let c = computation t in
          [], I.Let (defs, c)
    | S.LetRec (defs, t) ->
        let defs = C.assoc_map let_rec defs in
        let c = computation t in
          [], I.LetRec (defs, c)
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | (S.Var _ | S.Const _ | S.Tuple _ | S.Record _  | S.Variant _ | S.Lambda _ | S.Function _ | S.Handler _ | S.Operation _) ->
        let w, e = expression (t, pos) in
          w, I.Value e
  in
    match w with
      | [] -> (c, pos)
      | _ :: _ -> I.Let (w, (c, pos)), pos

and abstraction (p, t) = (p, computation t)

and abstraction2 (p1, p2, t) = (p1, p2, computation t)

and let_rec = function
  | (S.Lambda (p, t), _) -> (p, computation t)
  | (S.Function cs, pos) ->
    let x = C.fresh_variable () in
    let cs = List.map abstraction cs in
    ((Pattern.Var x, pos), (I.Match ((I.Var x, pos), cs), pos))
  | (_, pos) -> Error.syntax ~pos:pos "This kind of expression is not allowed in a recursive definition"

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

and handler pos {S.operations=ops; S.value=val_a; S.finally=fin_a} =
  let rec operation_cases = function
  | [] -> [], []
  | ((t, op), a2) :: cs ->
    let w, e = expression t in
    let ws, cs' = operation_cases cs in
    w @ ws, ((e, op), abstraction2 a2) :: cs'
  in
  let ws, ops = operation_cases ops in
  ws, { I.operations = ops;
    I.value =
      (match val_a with None -> id_abstraction pos | Some a -> abstraction a);
    I.finally =
      (match fin_a with None -> id_abstraction pos | Some a -> abstraction a)}

(** [tydef t ps d] desugars the definition of type [t] with parameters [ps]
    and definition [d]. *)
let tydef ps d =
  let sbst, lst = 
    List.fold_right (fun p (sbst,lst) ->
                       let u = T.next_param () in
                         (p, T.Param u)::sbst, u::lst) ps ([],[])
  in
    (lst,
     begin match d with
       | S.TyRecord lst -> T.Record (List.map (fun (f,t) -> (f, ty sbst t)) lst)
       | S.TySum lst -> T.Sum (List.map (fun (lbl, t) -> (lbl, C.option_map (ty sbst) t)) lst)
       | S.TyEffect lst -> T.Effect (List.map (fun (op,(t1,t2)) -> (op, (ty sbst t1, ty sbst t2))) lst)
       | S.TyInline t -> ty sbst t
     end)
