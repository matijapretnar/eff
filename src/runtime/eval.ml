(* Evaluation of the intermediate language, big step. *)

module V = Value

exception PatternMatch of Location.t

let rec extend_value p v env =
  match p.Typed.term, v with
  | Typed.PVar x, v -> RuntimeEnv.update x v env
  | Typed.PAs (p, x), v ->
    let env = extend_value p v env in
    RuntimeEnv.update x v env
  | Typed.PNonbinding, _ -> env
  | Typed.PTuple ps, Value.Tuple vs -> List.fold_right2 extend_value ps vs env
  | Typed.PRecord ps, Value.Record vs ->
    begin
      let rec extend_record ps vs env =
        match ps with
        | [] -> env
        | (f, p) :: ps ->
          let v = List.assoc f vs in
          extend_record ps vs (extend_value p v env)
      in
      try
        extend_record ps vs env
      with Not_found -> raise (PatternMatch p.Typed.location)
    end
  | Typed.PVariant (lbl, None), Value.Variant (lbl', None) when lbl = lbl' -> env
  | Typed.PVariant (lbl, Some p), Value.Variant (lbl', Some v) when lbl = lbl' ->
    extend_value p v env
  | Typed.PConst c, Value.Const c' when Const.equal c c' -> env
  | _, _ -> raise (PatternMatch p.Typed.location)

let extend p v env =
  try extend_value p v env
  with PatternMatch loc -> Error.runtime "Pattern match failure."

let rec sequence k = function
  | V.Value v -> k v
  | V.Call (op, v, k') ->
    let k'' u = sequence k (k' u) in
    V.Call (op, v, k'')

let rec ceval env c =
  let loc = c.Typed.location in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
    let v1 = veval env e1
    and v2 = veval env e2 in
    begin match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied."
    end

  | Typed.Value e ->
    V.Value (veval env e)

  | Typed.Match (e, cases) ->
    let v = veval env e in
    let rec eval_case = function
      | [] -> Error.runtime "No branches succeeded in a pattern match."
      | a :: lst ->
        let (p, c) = a.Typed.term in
        try ceval (extend_value p v env) c
        with PatternMatch _ -> eval_case lst
    in
    eval_case cases

  | Typed.Handle (e, c) ->
    let v = veval env e in
    let r = ceval env c in
    let h = V.to_handler v in
    h r

  | Typed.Bind (c, a) ->
    sequence (eval_closure env a) (ceval env c)

  | Typed.LetRec (defs, c) ->
    let env = extend_let_rec env defs in
    ceval env c


and extend_let_rec env defs =
  let env' = ref env in
  let env = List.fold_right
      (fun (f, a) env ->
         let (p, c) = a.Typed.term in
         let g = V.Closure (fun v -> ceval (extend p v !env') c) in
         RuntimeEnv.update f g env)
      defs env in
  env' := env;
  env

and veval env e =
  match e.Typed.term with
  | Typed.Var x ->
    begin match RuntimeEnv.lookup x env with
      | Some v -> v
      | None -> Error.runtime "Name %t is not defined." (Typed.Variable.print x)
    end
  | Typed.Const c -> V.Const c
  | Typed.Tuple es -> V.Tuple (List.map (veval env) es)
  | Typed.Record es -> V.Record (List.map (fun (f, e) -> (f, veval env e)) es)
  | Typed.Variant (lbl, None) -> V.Variant (lbl, None)
  | Typed.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval env e))
  | Typed.Lambda a -> assert false
  | Typed.Effect eff ->
    V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | Typed.Handler h -> V.Handler (eval_handler env h)

and eval_handler env {Typed.effect_clauses=ops; Typed.value_clause=value} =
  let eval_op (op, a2) =
    let (p, kvar, c) = a2.Typed.term in
    let f u k = eval_closure (extend kvar (V.Closure k) env) (Typed.abstraction ~loc:a2.Typed.location p c) u in
    (op, f)
  in
  let ops = List.map eval_op ops in
  let rec h = function
    | V.Value v -> eval_closure env value v
    | V.Call (eff, v, k) ->
      let k' u = h (k u) in
      begin match Common.lookup eff ops with
        | Some f -> f v k'
        | None -> V.Call (eff, v, k')
      end
  in
  h

and eval_closure env a v =
  let p, c = a.Typed.term in
  ceval (extend p v env) c

and eval_closure2 env a2 v1 v2 =
  let (p1, p2, c) = a2.Typed.term in
  ceval (extend p2 v2 (extend p1 v1 env)) c

let rec top_handle = function
  | V.Value v -> v
  | V.Call (eff, v, k) ->
    Error.runtime "uncaught effect %t %t." (Value.print_effect eff) (Value.print_value v)

let run env c =
  top_handle (ceval env c)
