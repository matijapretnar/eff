(* Evaluation of the intermediate language, big step. *)

module V = Value

exception PatternMatch of Location.t

let rec extend_value p v env =
  match fst p, v with
  | Pattern.Var x, v -> RuntimeEnv.update x v env
  | Pattern.As (p, x), v ->
      let env = extend_value p v env in
        RuntimeEnv.update x v env
  | Pattern.Nonbinding, _ -> env
  | Pattern.Tuple ps, Value.Tuple vs -> List.fold_right2 extend_value ps vs env
  | Pattern.Record ps, Value.Record vs ->
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
          with Not_found -> raise (PatternMatch (snd p))
      end
  | Pattern.Variant (lbl, None), Value.Variant (lbl', None) when lbl = lbl' -> env
  | Pattern.Variant (lbl, Some p), Value.Variant (lbl', Some v) when lbl = lbl' ->
      extend_value p v env
  | Pattern.Const c, Value.Const c' when Const.equal c c' -> env
  | _, _ -> raise (PatternMatch (snd p))

let extend p v env =
  try extend_value p.Typed.term v env
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
            try ceval (extend_value p.Typed.term v env) c
            with PatternMatch _ -> eval_case lst
      in
        eval_case cases

  | Typed.While (c1, c2) ->
      let rec loop () =
        let k v =
          let b = V.to_bool v in
          if b then
            sequence (fun _ -> loop ()) (ceval env c2)
          else
            V.unit_result
        in
        sequence k (ceval env c1)
      in
      loop ()
          
  | Typed.For (i, e1, e2, c, up) ->
      let n1 = V.to_int (veval env e1) in
      let n2 = V.to_int (veval env e2) in
      let le = if up then Big_int.le_big_int else Big_int.ge_big_int in
      let next = if up then Big_int.succ_big_int else Big_int.pred_big_int in
      let rec loop n =
        if le n n2 then
          let r = ceval (RuntimeEnv.update i (V.Const (Const.of_integer n)) env) c in
          sequence (fun _ -> loop (next n)) r
        else
          V.unit_result
      in
      loop n1

  | Typed.Handle (e, c) ->
      let v = veval env e in
      let r = ceval env c in
      let h = V.to_handler v in
      h r

  | Typed.Let (lst, c) ->
      eval_let env lst c

  | Typed.LetRec (defs, c) ->
      let env = extend_let_rec env defs in
      ceval env c

  | Typed.Check c ->
      let r = ceval env c in
      Print.check ~loc "%t" (Value.print_result r);
      V.unit_result

and eval_let env lst c =
  match lst with
    | [] -> ceval env c
    | (p, d) :: lst ->
      let r = ceval env d in
      sequence (fun v -> eval_let (extend p v env) lst c) r

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
  | Typed.Lambda a -> V.Closure (eval_closure env a)
  | Typed.Effect eff ->
      V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | Typed.Handler h -> V.Handler (eval_handler env h)

and eval_handler env {Typed.effect_clauses=ops; Typed.value_clause=value; Typed.finally_clause=fin} =
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
  fun r -> sequence (eval_closure env fin) (h r)

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
