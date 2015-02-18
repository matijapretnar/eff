(* Evaluation of the intermediate language, big step. *)

module C = Common
module V = Value

exception PatternMatch of C.position

module EnvMap = Map.Make(
  struct
    type t = int 
    let compare = Pervasives.compare
  end)

type env = Value.value EnvMap.t

let initial = EnvMap.empty

let update (x, _) = EnvMap.add x

let lookup (x, _) env =
  try
    Some (EnvMap.find x env)
  with
    | Not_found -> None      

let rec extend_value p v env =
  match fst p, v with
  | Pattern.Var x, v -> update x v env
  | Pattern.As (p, x), v ->
      let env = extend_value p v env in
        update x v env
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
  | Pattern.Const c, Value.Const c' when Common.equal_const c c' -> env
  | _, _ -> raise (PatternMatch (snd p))

let extend p v env =
  try extend_value p v env
  with PatternMatch pos -> Error.runtime "Pattern match failure."

let rec sequence (k : Value.closure) : Value.result -> Value.result =
  fun (Value.Result r) ->
    Value.Result (
      fun val_case op_cases ->
        r (fun v -> let Value.Result r = k v in r val_case op_cases)
        (Common.assoc_map (fun op_case -> fun par k' -> op_case par (fun u -> sequence k (k' u))) op_cases)
    )

let value v = Value.Result (fun val_case _ -> val_case v)

let operation ((((i, _, res) as inst), opsym) as op) v : Value.result = Value.Result (fun val_case op_cases ->
  match C.lookup ~compare:(fun ((i1, _, _), o1) ((i2, _, _), o2) -> (i1, o1) = (i2, o2)) op op_cases with
  | Some f -> f v value
  | None ->
      begin match res with
      | Some (s_ref, resource) ->
        begin match C.lookup opsym resource with
        | Some f ->
            let (Value.Result r) = f v !s_ref in
            begin match r (fun v -> v) [] with
            | V.Tuple [u; s] ->
                s_ref := s;
                val_case u
            | _ -> Error.runtime "pair expected in a resource handler for %t." (Value.print_instance inst)
            end
        | None -> Error.runtime "the resource for %t is missing an operation case for %t" (Value.print_instance inst) (Value.print_operation op)
        end
      | None -> Error.runtime "uncaught operation %t %t." (Value.print_operation op) (Value.print_value v)
      end
)

let rec ceval env (c, pos) = match c with
  | Syntax.Apply (e1, e2) ->
      let v1 = veval env e1
      and v2 = veval env e2 in
      begin match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied."
      end

  | Syntax.Value e ->
      value (veval env e)

  | Syntax.Match (e, cases) ->
      let v = veval env e in
      let rec eval_case = function
        | [] -> Error.runtime "No branches succeeded in a pattern match."
        | (p, c) :: lst ->
            try ceval (extend_value p v env) c
            with PatternMatch _ -> eval_case lst
      in
        eval_case cases

  | Syntax.While (c1, c2) ->
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
          
  | Syntax.For (i, e1, e2, c, up) ->
      let n1 = V.to_int (veval env e1) in
      let n2 = V.to_int (veval env e2) in
      let le = if up then Big_int.le_big_int else Big_int.ge_big_int in
      let next = if up then Big_int.succ_big_int else Big_int.pred_big_int in
      let rec loop n =
        if le n n2 then
          let r = ceval (update i (V.Const (C.Integer n)) env) c in
          sequence (fun _ -> loop (next n)) r
        else
          V.unit_result
      in
      loop n1

  | Syntax.Handle (e, c) ->
      let v = veval env e in
      let r = ceval env c in
      let h = V.to_handler v in
      h r

  | Syntax.New (eff, r) ->
      let r = (match r with
                 | None -> None
                 | Some (e, lst) ->
                     let v = veval env e in
                     let lst = List.map (fun (op, a) -> (op, eval_closure2 env a)) lst in
                       Some (ref v, lst))
      in
      let e = V.fresh_instance None r in
        value e

  | Syntax.Let (lst, c) ->
      eval_let env lst c

  | Syntax.LetRec (defs, c) ->
      let env = extend_let_rec env defs in
      ceval env c

  | Syntax.Check c ->
      let Value.Result r = ceval env c in
      let val_case v =
        Print.check ~pos "%t" (Value.print_value v);
        V.unit_value
      in
      Value.value (r val_case [])


and eval_let env lst c =
  match lst with
    | [] -> ceval env c
    | (p, d) :: lst ->
      let r = ceval env d in
      sequence (fun v -> eval_let (extend p v env) lst c) r

and extend_let_rec env defs =
  let env' = ref env in
  let env = List.fold_right
    (fun (f, (p, c)) env ->
       let g = V.Closure (fun v -> ceval (extend p v !env') c) in
       update f g env)
    defs env in
  env' := env;
  env

and veval env (e, pos) = match e with
  | Syntax.Var x ->
      begin match lookup x env with
      | Some v -> v
      | None -> Error.runtime "Name %t is not defined." (Print.variable x)
      end
  | Syntax.Const c -> V.Const c
  | Syntax.Tuple es -> V.Tuple (List.map (veval env) es)
  | Syntax.Record es -> V.Record (List.map (fun (f, e) -> (f, veval env e)) es)
  | Syntax.Variant (lbl, None) -> V.Variant (lbl, None)
  | Syntax.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval env e))
  | Syntax.Lambda a -> V.Closure (eval_closure env a)
  | Syntax.Operation (e, op) ->
      let n = V.to_instance (veval env e) in
      V.Closure (operation (n, op))
  | Syntax.Handler h -> V.Handler (eval_handler env h)

and eval_closure env (p, c) v : Value.result = ceval (extend p v env) c

and eval_closure2 env (p1, p2, c) v1 v2 : Value.result = ceval (extend p2 v2 (extend p1 v1 env)) c

and eval_handler env {Syntax.operations=ops; Syntax.value=value; Syntax.finally=fin} =
  let fin = eval_closure env fin in

  let rec change_cases val_case op_cases =
    let eval_op ((e, op), (arg_pat, k_pat, c)) =
      let i = V.to_instance (veval env e) in
      let f arg k =
        let k' = change_closure k in
        let Value.Result r = eval_closure (extend k_pat (V.Closure k') env) (arg_pat, c) arg in
        r val_case op_cases
      in
        ((i, op), f)
    in
    (
      (fun v -> let Value.Result r = eval_closure env value v in r val_case op_cases),
      List.map eval_op ops @ (Common.assoc_map (fun op_case -> fun arg k -> op_case arg (change_closure k)) op_cases)
    )

  and change_closure k =
    fun y ->
      let (Value.Result r) = k y in
      Value.Result (fun val_case op_cases ->
        let (val_case', op_cases') = change_cases val_case op_cases in
        r val_case' op_cases')

  in

  fun (Value.Result r) ->
  sequence fin
  (Value.Result (fun val_case op_cases ->
    let (val_case', op_cases') = change_cases val_case op_cases in
    r val_case' op_cases'))

let run env c =
  let (Value.Result r) = ceval env c in
  r Common.id []
