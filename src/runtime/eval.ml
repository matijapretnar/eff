(* Evaluation of the intermediate language, big step. *)

module V = Value
module Core = Untyped

module RuntimeEnv = Map.Make(Untyped.Variable)

type state = Value.value RuntimeEnv.t

let empty = RuntimeEnv.empty

let update x = RuntimeEnv.add x

let lookup x env =
  try
    Some (RuntimeEnv.find x env)
  with
    | Not_found -> None      

exception PatternMatch of Location.t

let rec extend_value p v env =
  match p.Core.term, v with
  | Core.PVar x, v -> update x v env
  | Core.PAs (p, x), v ->
    let env = extend_value p v env in
    update x v env
  | Core.PNonbinding, _ -> env
  | Core.PTuple ps, Value.Tuple vs -> List.fold_right2 extend_value ps vs env
  | Core.PRecord ps, Value.Record vs ->
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
      with Not_found -> raise (PatternMatch p.Core.location)
    end
  | Core.PVariant (lbl, None), Value.Variant (lbl', None) when lbl = lbl' -> env
  | Core.PVariant (lbl, Some p), Value.Variant (lbl', Some v) when lbl = lbl' ->
    extend_value p v env
  | Core.PConst c, Value.Const c' when Const.equal c c' -> env
  | _, _ -> raise (PatternMatch p.Core.location)

let extend p v env =
  try extend_value p v env
  with PatternMatch loc -> Error.runtime "Pattern match failure."

let rec sequence k = function
  | V.Value v -> k v
  | V.Call (op, v, k') ->
    let k'' u = sequence k (k' u) in
    V.Call (op, v, k'')

let rec ceval env c =
  let loc = c.Core.location in
  match c.Core.term with
  | Core.Apply (e1, e2) ->
    let v1 = veval env e1
    and v2 = veval env e2 in
    begin match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied."
    end

  | Core.Value e ->
    V.Value (veval env e)

  | Core.Match (e, cases) ->
    let v = veval env e in
    let rec eval_case = function
      | [] -> Error.runtime "No branches succeeded in a pattern match."
      | (p, c) :: lst ->
        try ceval (extend_value p v env) c
        with PatternMatch _ -> eval_case lst
    in
    eval_case cases

  | Core.Handle (e, c) ->
    let v = veval env e in
    let r = ceval env c in
    let h = V.to_handler v in
    h r

  | Core.LetRec (defs, c) ->
    let env = extend_let_rec env defs in
    ceval env c


and extend_let_rec env defs =
  let env' = ref env in
  let env = List.fold_right
      (fun (f, (p, c)) env ->
         let g = V.Closure (fun v -> ceval (extend p v !env') c) in
         update f g env)
      defs env in
  env' := env;
  env

and veval env e =
  match e.Core.term with
  | Core.Var x ->
    begin match lookup x env with
      | Some v -> v
      | None -> Error.runtime "Name %t is not defined." (Core.Variable.print x)
    end
  | Core.Const c -> V.Const c
  | Core.Tuple es -> V.Tuple (List.map (veval env) es)
  | Core.Record es -> V.Record (List.map (fun (f, e) -> (f, veval env e)) es)
  | Core.Variant (lbl, None) -> V.Variant (lbl, None)
  | Core.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval env e))
  | Core.Lambda a -> assert false
  | Core.Effect eff ->
    V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | Core.Handler h -> V.Handler (eval_handler env h)

and eval_handler env {Core.effect_clauses=ops; Core.value_clause=value} =
  let eval_op (op, (p, kvar, c)) =
    let f u k = eval_closure (extend kvar (V.Closure k) env) (p, c) u in
    (op, f)
  in
  let ops = List.map eval_op ops in
  let rec h = function
    | V.Value v ->
        begin match value with
        | Some value -> eval_closure env value v
        | None -> V.Value v
        end
    | V.Call (eff, v, k) ->
      let k' u = h (k u) in
      begin match OldUtils.lookup eff ops with
        | Some f -> f v k'
        | None -> V.Call (eff, v, k')
      end
  in
  h

and eval_closure env (p, c) v =
  ceval (extend p v env) c

and eval_closure2 env (p1, p2, c) v1 v2 =
  ceval (extend p2 v2 (extend p1 v1 env)) c

let rec top_handle = function
  | V.Value v -> v
  | V.Call (eff, v, k) ->
    Error.runtime "uncaught effect %t %t." (Value.print_effect eff) (Value.print_value v)

let run env c =
  top_handle (ceval env c)