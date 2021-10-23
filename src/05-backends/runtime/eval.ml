(* Evaluation of the ExEff language, big step. *)
open Utils
open Language
module V = Value
module RuntimeEnv = Map.Make (CoreTypes.Variable)

type state = {
  environment : V.value RuntimeEnv.t;
  runners : (CoreTypes.Effect.t, V.value -> V.value) Assoc.t;
}

let initial_state = { environment = RuntimeEnv.empty; runners = Assoc.empty }

let update x v state =
  { state with environment = RuntimeEnv.add x v state.environment }

let lookup x state =
  try Some (RuntimeEnv.find x state.environment) with Not_found -> None

let add_runner (eff, _) runner state =
  { state with runners = Assoc.update eff runner state.runners }

exception PatternMatch of Location.t

let rec extend_value p v state =
  match (p.term, v) with
  | Term.PVar x, v -> update x v state
  (* | Term.PAnnotated (p, _t), v -> extend_value p v state *)
  | Term.PAs (p, x), v ->
      let state = extend_value p v state in
      update x v state
  | Term.PNonbinding, _ -> state
  | Term.PTuple ps, V.Tuple vs -> List.fold_right2 extend_value ps vs state
  | Term.PRecord ps, V.Record vs -> (
      let extender state (f, p) =
        match Assoc.lookup f vs with
        | None -> raise Not_found
        | Some v -> extend_value p v state
      in
      try Assoc.fold_left extender state ps
      with Not_found -> raise (PatternMatch Location.unknown))
  | Term.PVariant (lbl, None), V.Variant (lbl', None) when lbl = lbl' -> state
  | Term.PVariant (lbl, Some p), V.Variant (lbl', Some v) when lbl = lbl' ->
      extend_value p v state
  | Term.PConst c, V.Const c' when Const.equal c c' -> state
  | _, _ -> raise (PatternMatch Location.unknown)

let extend p v state =
  try extend_value p v state
  with PatternMatch _loc -> Error.runtime "Pattern match failure."

let rec sequence k = function
  | V.Value v -> k v
  | V.Call (op, v, k') ->
      let k'' u = sequence k (k' u) in
      V.Call (op, v, k'')

let rec ceval state c =
  match c.term with
  | Term.Apply (e1, e2) -> (
      let v1 = veval state e1 and v2 = veval state e2 in
      match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied.")
  | Term.Value e -> V.Value (veval state e)
  | Term.Match (e, cases) ->
      let v = veval state e in
      let rec eval_case = function
        | [] -> Error.runtime "No branches succeeded in a pattern match."
        | a :: lst -> (
            let p, c = a.term in
            try ceval (extend_value p v state) c
            with PatternMatch _ -> eval_case lst)
      in
      eval_case cases
  | Term.Handle (e, c) ->
      let v = veval state e in
      let r = ceval state c in
      let h = V.to_handler v in
      h r
  | Term.LetVal (e, { term = p, c; _ }) ->
      eval_let state [ (p, Term.value e) ] c
  | Term.LetRec (defs, c) ->
      let state = extend_let_rec state defs in
      ceval state c
  | Term.Call ((eff, _), e, a) ->
      let e' = veval state e in
      V.Call (eff, e', eval_closure state a.term)
  | Term.Bind (c1, { term = p, c2; _ }) -> eval_let state [ (p, c1) ] c2
  | Term.CastComp (c, _) -> ceval state c

and eval_let state lst c =
  match lst with
  | [] -> ceval state c
  | (p, d) :: lst ->
      let r = ceval state d in
      sequence (fun v -> eval_let (extend p v state) lst c) r

and extend_let_rec state defs =
  let state' = ref state in
  let state =
    Assoc.fold_right
      (fun (f, (_ws, a)) state ->
        let p, c = a.term in
        let g = V.Closure (fun v -> ceval (extend p v !state') c) in
        update f g state)
      defs state
  in
  state' := state;
  state

and veval state e =
  match e.term with
  | Term.Var x -> (
      match lookup x.variable state with
      | Some v -> v
      | None ->
          Error.runtime "Name %t is not defined."
            (CoreTypes.Variable.print x.variable))
  | Term.Const c -> V.Const c
  (* | Term.Annotated (t, _ty) -> veval state t *)
  | Term.Tuple es -> V.Tuple (List.map (veval state) es)
  | Term.Record es -> V.Record (Assoc.map (fun e -> veval state e) es)
  | Term.Variant (lbl, e) -> V.Variant (lbl, Option.map (veval state) e)
  | Term.Lambda a -> V.Closure (eval_closure state a.term)
  | Term.Handler h -> V.Handler (eval_handler state h)
  | Term.CastExp (e, _coercion) -> veval state e

and eval_handler state
    {
      term =
        {
          Term.effect_clauses = { Term.effect_part = ops; _ };
          Term.value_clause = value;
        };
      _;
    } =
  let eval_op ((eff, _), a2) =
    let p, kvar, c = a2.term in
    let f u k = eval_closure (extend kvar (V.Closure k) state) (p, c) u in
    (eff, f)
  in
  let ops = Assoc.kmap eval_op ops in
  let rec h = function
    | V.Value v -> eval_closure state value.term v
    | V.Call (eff, v, k) -> (
        let k' u = h (k u) in
        match Assoc.lookup eff ops with
        | Some f -> f v k'
        | None -> V.Call (eff, v, k'))
  in
  (* fun r -> sequence (eval_closure state fin) (h r) *)
  h

and eval_closure state a v =
  let p, c = a in
  ceval (extend p v state) c

let rec top_handle state op =
  match op with
  | V.Value v -> v
  | V.Call (eff, v, k) -> (
      match Assoc.lookup eff state.runners with
      | Some f ->
          let w = f v in
          top_handle state (k w)
      | None ->
          Error.runtime "uncaught effect %t %t." (V.print_effect eff)
            (V.print_value v))

let eval_expression state exp = veval state exp

let run state c = top_handle state (ceval state c)