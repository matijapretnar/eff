(* Evaluation of the intermediate language, big step. *)

module C = Common
module V = Value

exception PatternMatch of C.position

module EnvMap = Map.Make(
  struct
    type t = string 
    let compare = String.compare
  end)

let initial = EnvMap.empty

let update = EnvMap.add 

let lookup x env =
  try
    Some (EnvMap.find x env)
  with
    | Not_found -> None      

let rec extend_value p v env =
  match fst p, v with
  | Pattern.Var x, _ -> update x v env
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
  with PatternMatch pos -> Error.runtime ~pos "Pattern match failure."

let rec sequence k = function
  | V.Value v -> k v
  | V.Operation (op, v, k') ->
      let k'' u = sequence k (k' u) in
      V.Operation (op, v, k'')

let rec ceval env (c, pos) = match c with
  | Core.Apply (e1, e2) ->
      let v1 = veval env e1
      and v2 = veval env e2 in
      begin match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime ~pos:(snd e1) "Only functions can be applied."
      end

  | Core.Value e ->
      V.Value (veval env e)

  | Core.Match (e, cases) ->
      let v = veval env e in
      let rec eval_case = function
        | [] -> Error.runtime ~pos "No branches succeeded in a pattern match."
        | (p, c) :: lst ->
            try ceval (extend_value p v env) c
            with PatternMatch _ -> eval_case lst
      in
        eval_case cases

  | Core.While (c1, c2) ->
      let rec loop () =
        let k v =
          let b = V.to_bool ~pos:(snd c1) v in
          if b then
            sequence (fun _ -> loop ()) (ceval env c2)
          else
            V.Value V.from_unit
        in
        sequence k (ceval env c1)
      in
      loop ()
          
  | Core.For (i, e1, e2, c, up) ->
      let n1 = V.to_int ~pos:(snd e1) (veval env e1) in
      let n2 = V.to_int ~pos:(snd e2) (veval env e2) in
      let le = if up then Big_int.le_big_int else Big_int.ge_big_int in
      let next = if up then Big_int.succ_big_int else Big_int.pred_big_int in
      let rec loop n =
        if le n n2 then
          let r = ceval (update i (V.Const (C.Integer n)) env) c in
          sequence (fun _ -> loop (next n)) r
        else
          V.Value V.from_unit
      in
      loop n1

  | Core.Handle (e, c) ->
      let v = veval env e in
      let r = ceval env c in
      let h = V.to_handler ~pos:(snd e) v in
      h r

  | Core.New (eff, r) ->
      let r = (match r with
                 | None -> None
                 | Some (e, lst) ->
                     let v = veval env e in
                     let lst = List.map (fun (op, a) -> (op, eval_closure2 env a)) lst in
                       Some (ref v, lst))
      in
      let e = V.fresh_instance None r in
        V.Value e

  | Core.Let (lst, c) ->
      eval_let env lst c

  | Core.LetRec (defs, c) ->
      let env = extend_let_rec env defs in
      ceval env c

  | Core.Check c ->
      let r = ceval env c in
      Print.check ~pos "%t" (Print.result r);
      V.value_unit

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
  | Core.Var x ->
      begin match lookup x env with
      | Some v -> v
      | None -> Error.runtime ~pos "Name %s is not defined." x
      end
  | Core.Const c -> V.Const c
  | Core.Tuple es -> V.Tuple (List.map (veval env) es)
  | Core.Record es -> V.Record (List.map (fun (f, e) -> (f, veval env e)) es)
  | Core.Variant (lbl, None) -> V.Variant (lbl, None)
  | Core.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval env e))
  | Core.Lambda a -> V.Closure (eval_closure env a)
  | Core.Operation (e, op) ->
      let n = V.to_instance ~pos:(snd e) (veval env e) in
      V.Closure (fun v -> V.Operation ((n, op), v, V.value))
  | Core.Handler h -> V.Handler (eval_handler env h)

and eval_handler env {Core.operations=ops; Core.value=value; Core.finally=fin} =
  let eval_op ((e, op), (p, kvar, c)) =
    let f u k = eval_closure (extend kvar (V.Closure k) env) (p, c) u in
    let (i, _, _) = V.to_instance ~pos:(snd e) (veval env e) in
      ((i, op), f)
  in
  let ops = List.map eval_op ops in
  let rec h = function
    | V.Value v -> eval_closure env value v
    | V.Operation (((i, _, _), opname) as op, v, k) ->
        let k' u = h (k u) in
        begin match C.lookup (i,opname) ops with
        | Some f -> f v k'
        | None -> V.Operation (op, v, k')
        end
  in
  fun r -> sequence (eval_closure env fin) (h r)

and eval_closure env (p, c) v = ceval (extend p v env) c

and eval_closure2 env (p1, p2, c) v1 v2 = ceval (extend p2 v2 (extend p1 v1 env)) c

let rec top_handle = function
  | V.Value v -> v
  | V.Operation (((_, _, Some (s_ref, resource)) as inst, opsym) as op, v, k) ->
      begin match C.lookup opsym resource with
        | None -> Error.runtime ~pos:C.Nowhere "uncaught operation %t %t." (Print.operation op) (Print.value v)
        | Some f ->
            begin match f v !s_ref with
              | V.Value (V.Tuple [u; s]) ->
                  s_ref := s;
                  top_handle (k u)
              | V.Value _ -> Error.runtime ~pos:C.Nowhere "pair expected in a resource handler for %t." (Print.instance inst)
              | _ -> Error.runtime ~pos:C.Nowhere "pair expected in a resource handler for %t." (Print.instance inst)
            end
      end
  | V.Operation (((_, _, None), _) as op, v, k) ->
      Error.runtime ~pos:C.Nowhere "uncaught operation %t %t." (Print.operation op) (Print.value v)

let run env c =
  top_handle (ceval env c)
