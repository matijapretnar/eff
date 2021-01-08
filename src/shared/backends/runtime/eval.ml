(* Evaluation of the intermediate language, big step. *)
open Utils
open Language
open CoreUtils
module V = Value
module Untyped = UntypedSyntax
module RuntimeEnv = Map.Make (CoreTypes.Variable)

type state = Value.value RuntimeEnv.t

let initial_state = RuntimeEnv.empty

let update x = RuntimeEnv.add x

let lookup x state = try Some (RuntimeEnv.find x state) with Not_found -> None

exception PatternMatch of Location.t

let rec extend_value p v state =
  match (p.it, v) with
  | Untyped.PVar x, v -> update x v state
  | Untyped.PAnnotated (p, _t), v -> extend_value p v state
  | Untyped.PAs (p, x), v ->
      let state = extend_value p v state in
      update x v state
  | Untyped.PNonbinding, _ -> state
  | Untyped.PTuple ps, Value.Tuple vs ->
      List.fold_right2 extend_value ps vs state
  | Untyped.PRecord ps, Value.Record vs -> (
      let extender state (f, p) =
        match Assoc.lookup f vs with
        | None -> raise Not_found
        | Some v -> extend_value p v state
      in
      try Assoc.fold_left extender state ps
      with Not_found -> raise (PatternMatch p.at))
  | Untyped.PVariant (lbl, None), Value.Variant (lbl', None) when lbl = lbl' ->
      state
  | Untyped.PVariant (lbl, Some p), Value.Variant (lbl', Some v) when lbl = lbl'
    ->
      extend_value p v state
  | Untyped.PConst c, Value.Const c' when Const.equal c c' -> state
  | _, _ -> raise (PatternMatch p.at)

let extend p v state =
  try extend_value p v state
  with PatternMatch _loc -> Error.runtime "Pattern match failure."

let rec sequence k = function
  | V.Value v -> k v
  | V.Call (op, v, k') ->
      let k'' u = sequence k (k' u) in
      V.Call (op, v, k'')

let rec ceval state c =
  let loc = c.at in
  match c.it with
  | Untyped.Apply (e1, e2) -> (
      let v1 = veval state e1 and v2 = veval state e2 in
      match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied.")
  | Untyped.Value e -> V.Value (veval state e)
  | Untyped.Match (e, cases) ->
      let v = veval state e in
      let rec eval_case = function
        | [] -> Error.runtime "No branches succeeded in a pattern match."
        | a :: lst -> (
            let p, c = a in
            try ceval (extend_value p v state) c
            with PatternMatch _ -> eval_case lst)
      in
      eval_case cases
  | Untyped.Handle (e, c) ->
      let v = veval state e in
      let r = ceval state c in
      let h = V.to_handler v in
      h r
  | Untyped.Let (lst, c) -> eval_let state lst c
  | Untyped.LetRec (defs, c) ->
      let state = extend_let_rec state (Assoc.of_list defs) in
      ceval state c
  | Untyped.Check c ->
      let r = ceval state c in
      Print.check ~loc "%t" (Value.print_result r);
      V.unit_result

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
      (fun (f, a) state ->
        let p, c = a in
        let g = V.Closure (fun v -> ceval (extend p v !state') c) in
        update f g state)
      defs state
  in
  state' := state;
  state

and veval state e =
  match e.it with
  | Untyped.Var x -> (
      match lookup x state with
      | Some v -> v
      | None ->
          Error.runtime "Name %t is not defined." (CoreTypes.Variable.print x))
  | Untyped.Const c -> V.Const c
  | Untyped.Annotated (t, _ty) -> veval state t
  | Untyped.Tuple es -> V.Tuple (List.map (veval state) es)
  | Untyped.Record es -> V.Record (Assoc.map (fun e -> veval state e) es)
  | Untyped.Variant (lbl, None) -> V.Variant (lbl, None)
  | Untyped.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval state e))
  | Untyped.Lambda a -> V.Closure (eval_closure state a)
  | Untyped.Effect eff ->
      V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | Untyped.Handler h -> V.Handler (eval_handler state h)

and eval_handler state
    {
      Untyped.effect_clauses = ops;
      Untyped.value_clause = value;
      Untyped.finally_clause = fin;
    } =
  let eval_op a2 =
    let p, kvar, c = a2 in
    let f u k = eval_closure (extend kvar (V.Closure k) state) (p, c) u in
    f
  in
  let ops = Assoc.map eval_op ops in
  let rec h = function
    | V.Value v -> eval_closure state value v
    | V.Call (eff, v, k) -> (
        let k' u = h (k u) in
        match Assoc.lookup eff ops with
        | Some f -> f v k'
        | None -> V.Call (eff, v, k'))
  in
  fun r -> sequence (eval_closure state fin) (h r)

and eval_closure state a v =
  let p, c = a in
  ceval (extend p v state) c

let rec top_handle op =
  match op with
  | V.Value v -> v
  | V.Call (eff, v, k) -> (
      match CoreTypes.Effect.fold (fun annot _n -> annot) eff with
      | "Print" ->
          let str = V.to_str v in
          Format.pp_print_string !Config.output_formatter str;
          Format.pp_print_flush !Config.output_formatter ();
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
      | "Write" -> (
          match v with
          | V.Tuple
              [ V.Const (Const.String file_name); V.Const (Const.String str) ]
            ->
              let file_handle =
                open_out_gen
                  [ Open_wronly; Open_append; Open_creat; Open_text ]
                  0o666 file_name
              in
              Printf.fprintf file_handle "%s" str;
              close_out file_handle;
              top_handle (k V.unit_value)
          | _ -> Error.runtime "A pair of a file name and string expected")
      | _eff_annot ->
          Error.runtime "uncaught effect %t %t." (Value.print_effect eff)
            (Value.print_value v))

let run state c = top_handle (ceval state c)
