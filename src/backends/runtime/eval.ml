(* Evaluation of ExEff, big step without intermediate SkelEff step. *)
open CoreUtils
module V = Value
module RuntimeEnv = Map.Make (CoreTypes.Variable)
module ExEff = Typed

type state = Value.value RuntimeEnv.t

let initial_state = RuntimeEnv.empty

let update x = RuntimeEnv.add x

let lookup x state =
  try Some (RuntimeEnv.find x state) with Not_found -> None

exception PatternMatch

exception ExhaustivenessCheck of Location.t

let rec extend_value p v state =
  match (p, v) with
  | ExEff.PVar x, v -> update x v state
  | ExEff.PAs (p, x), v ->
      let state = extend_value p v state in
      update x v state
  | ExEff.PNonbinding, _ -> state
  | ExEff.PTuple ps, Value.Tuple vs ->
      List.fold_right2 extend_value ps vs state
  | ExEff.PRecord ps, Value.Record vs -> (
      let extender state (f, p) =
        match Assoc.lookup f vs with
        | None -> raise Not_found
        | Some v -> extend_value p v state
      in
      try Assoc.fold_left extender state ps with Not_found ->
        raise (PatternMatch) )
  | ExEff.PVariant (lbl, p), Value.Variant (lbl', Some v)
    when lbl = lbl' ->
      extend_value p v state
  | ExEff.PConst c, Value.Const c' when Const.equal c c' -> state
  | _, _ -> raise (PatternMatch)

let extend p v state =
  try extend_value p v state with PatternMatch ->
    Error.runtime "Pattern match failure."

let rec sequence k = function
  | V.Value v -> k v
  | V.Call (op, v, k') ->
      let k'' u = sequence k (k' u) in
      V.Call (op, v, k'')

let rec ceval state c =
  match c with
  | ExEff.Apply (e1, e2) -> (
      let v1 = veval state e1 and v2 = veval state e2 in
      match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied." )
  | ExEff.Value e -> V.Value (veval state e)
  | ExEff.Match (e, cases, loc) ->
      let v = veval state e in
      let rec eval_case = function
        | [] -> raise (ExhaustivenessCheck loc)
        | a :: lst -> (
            let p, c = a in
            try ceval (extend_value p v state) c with PatternMatch ->
              eval_case lst )
      in
      eval_case cases
  | ExEff.Handle (e, c) ->
      let v = veval state e in
      let r = ceval state c in
      let h = V.to_handler v in
      h r
  | ExEff.LetVal (e, abs) -> eval_let state e abs
  | ExEff.LetRec (defs, c) ->
      let converter (var, _, _, c) = (var, c) in
      let state = extend_let_rec state (Assoc.of_list (List.map converter defs)) in
      ceval state c
  | ExEff.Call ((eff, (_, _)), exp, (p, _, c)) ->
      V.Call (eff, veval state exp, eval_closure state (p, c))
  | ExEff.Op (eff, exp) -> failwith "ExEff op"
  | ExEff.Bind (c, a) -> (
      match (ceval state c) with
      | V.Value v -> eval_closure state a v
      | V.Call (eff, v, clo) -> sequence (eval_closure state a) (V.Call (eff, v, clo))
      )
  | ExEff.CastComp (c, _) -> ceval state c
  | ExEff.CastComp_ty (c, _) -> ceval state c
  | ExEff.CastComp_dirt (c, _) -> ceval state c

and eval_let state e (p, _, c) =
  let v = veval state e in
  let state' = extend p v state in
  ceval state' c

and extend_let_rec state defs =
  let state' = ref state in
  let state =
    Assoc.fold_right
      (fun (f, a) state ->
        let p, c = a in
        let g = V.Closure (fun v -> ceval (extend p v !state') c) in
        update f g state )
      defs state
  in
  state' := state ;
  state

and veval state e =
  match e with
  | ExEff.Var x -> (
    match lookup x state with
    | Some v -> v
    | None ->
        Error.runtime "Name %t is not defined." (CoreTypes.Variable.print x) )
  | ExEff.Const c -> V.Const c
  | ExEff.Tuple es -> V.Tuple (List.map (veval state) es)
  | ExEff.Record es -> V.Record (Assoc.map (fun e -> veval state e) es)
  | ExEff.Variant (lbl, e) -> V.Variant (lbl, Some (veval state e))
  | ExEff.Lambda (p, _, c) -> V.Closure (eval_closure state (p, c))
  | ExEff.Effect (eff, (_, _)) ->
      V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | ExEff.Handler h -> V.Handler (eval_handler state h)
  | ExEff.BigLambdaTy (_, _, e) -> veval state e
  | ExEff.BigLambdaDirt (_, e) -> veval state e
  | ExEff.BigLambdaSkel (_, e) -> veval state e
  | ExEff.CastExp (e, _) -> veval state e
  | ExEff.ApplyTyExp (e, _) -> veval state e
  | ExEff.LambdaTyCoerVar (_, _, e) -> veval state e
  | ExEff.LambdaDirtCoerVar (_, _, e) -> veval state e
  | ExEff.ApplyDirtExp (e, _) -> veval state e
  | ExEff.ApplySkelExp (e, _) -> veval state e
  | ExEff.ApplyTyCoercion (e, _) -> veval state e
  | ExEff.ApplyDirtCoercion (e, _) -> veval state e

and eval_handler state
    { ExEff.effect_clauses= ops
    ; ExEff.value_clause= (pat, _, com) } =
  let eval_op a2 =
    let p, kvar, c = a2 in
    let f u k = eval_closure (extend kvar (V.Closure k) state) (p, c) u in
    f
  in
  let ops = Assoc.map eval_op ops in
  let check_effect x = function (e, (_, _)) -> e = x in
  let rec h = function
    | V.Value v -> eval_closure state (pat, com) v
    | V.Call (eff, v, k) -> (
        let k' u = h (k u) in
        match Assoc.to_list (Assoc.filter (check_effect eff) ops) with
        | (_, f) :: rest -> f v k'
        | [] -> V.Call (eff, v, k') )
  in
  h

and eval_closure state a v =
  let p, c = a in
  ceval (extend p v state) c

and eval_closure2 state a2 v1 v2 =
  let p1, p2, c = a2.it in
  ceval (extend p2 v2 (extend p1 v1 state)) c

let rec top_handle op =
  match op with
  | V.Value v -> v
  | V.Call (eff, v, k) -> (
    match CoreTypes.Effect.fold (fun annot n -> annot) eff with
    | "Print" ->
        let str = V.to_str v in
        Format.pp_print_string !Config.output_formatter str ;
        Format.pp_print_flush !Config.output_formatter () ;
        top_handle (k V.unit_value)
    | "Raise" -> Error.runtime "%t" (Value.print_value v)
    | "RandomInt" ->
        let rnd_int = Random.int (Value.to_int v) in
        let rnd_int_v = V.Const (Const.of_integer rnd_int) in
        top_handle (k rnd_int_v)
    | "RandomFloat" ->
        let rnd_float = Random.float (Value.to_float v) in
        let rnd_float_v = V.Const (Const.of_float rnd_float) in
        top_handle (k rnd_float_v)
    | "Read" ->
        let str = read_line () in
        let str_v = V.Const (Const.of_string str) in
        top_handle (k str_v)
    | eff_annot ->
        Error.runtime "uncaught effect %t %t." (Value.print_effect eff)
          (Value.print_value v) )

let run state c = top_handle (ceval state c)
