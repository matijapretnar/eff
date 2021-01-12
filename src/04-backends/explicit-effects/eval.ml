(* Evaluation of the ExEff language, big step. *)
open Utils
open Language
module V = Value
module RuntimeEnv = Map.Make (CoreTypes.Variable)

type state = V.value RuntimeEnv.t

let initial_state = RuntimeEnv.empty

let update x = RuntimeEnv.add x

let lookup x state = RuntimeEnv.find_opt x state

exception PatternMatch of Location.t

let rec extend_value p v state =
  match (p, v) with
  | Typed.PVar x, v -> update x v state
  (* | Typed.PAnnotated (p, _t), v -> extend_value p v state *)
  | Typed.PAs (p, x), v ->
      let state = extend_value p v state in
      update x v state
  | Typed.PNonbinding, _ -> state
  | Typed.PTuple ps, V.Tuple vs -> List.fold_right2 extend_value ps vs state
  | Typed.PRecord ps, V.Record vs -> (
      let extender state (f, p) =
        match Assoc.lookup f vs with
        | None -> raise Not_found
        | Some v -> extend_value p v state
      in
      try Assoc.fold_left extender state ps
      with Not_found -> raise (PatternMatch Location.unknown))
  | Typed.PVariant (lbl, p), V.Variant (lbl', v) when lbl = lbl' ->
      extend_value p v state
  | Typed.PConst c, V.Const c' when Const.equal c c' -> state
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
  match c with
  | Typed.Apply (e1, e2) -> (
      let v1 = veval state e1 and v2 = veval state e2 in
      match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied.")
  | Typed.Value e -> V.Value (veval state e)
  | Typed.Match (e, _ty, cases) ->
      let v = veval state e in
      let rec eval_case = function
        | [] -> Error.runtime "No branches succeeded in a pattern match."
        | a :: lst -> (
            let p, c = a in
            try ceval (extend_value p v state) c
            with PatternMatch _ -> eval_case lst)
      in
      eval_case cases
  | Typed.Handle (e, c) ->
      let v = veval state e in
      let r = ceval state c in
      let h = V.to_handler v in
      h r
  | Typed.LetVal (e, (p, _ty, c)) -> eval_let state [ (p, Typed.Value e) ] c
  | Typed.LetRec (defs, c) ->
      (* strip types *)
      let stripped =
        List.map (fun (v, _, _, abs) -> (v, abs)) defs |> Assoc.of_list
      in
      let state = extend_let_rec state stripped in
      ceval state c
  | Typed.Call (_, _, _) -> assert false
  | Typed.Op (_, _) -> assert false
  | Typed.Bind (_, _) -> assert false
  | Typed.CastComp (c, _) | Typed.CastComp_ty (c, _) | Typed.CastComp_dirt (c, _)
    ->
      ceval state c

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
  match e with
  | Typed.Var x -> (
      match lookup x state with
      | Some v -> v
      | None ->
          Error.runtime "Name %t is not defined." (CoreTypes.Variable.print x))
  | Typed.Const c -> V.Const c
  (* | Typed.Annotated (t, _ty) -> veval state t *)
  | Typed.Tuple es -> V.Tuple (List.map (veval state) es)
  | Typed.Record es -> V.Record (Assoc.map (fun e -> veval state e) es)
  | Typed.Variant (lbl, e) -> V.Variant (lbl, veval state e)
  | Typed.Lambda a -> V.Closure (eval_closure state a)
  | Typed.Effect (eff, _) ->
      V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | Typed.Handler h -> V.Handler (eval_handler state h)
  | Typed.CastExp (e, _coercion) -> veval state e
  | Typed.LambdaTyCoerVar (_, _, _)
  | Typed.LambdaDirtCoerVar (_, _, _)
  | Typed.ApplyTyCoercion (_, _)
  | Typed.ApplyDirtCoercion (_, _) ->
      assert false

and eval_handler state
    { Typed.effect_clauses = ops; Typed.value_clause = value } =
  let eval_op ((eff, (_, to_ty)), a2) =
    let p, kvar, c = a2 in
    let f u k =
      eval_closure (extend kvar (V.Closure k) state) (p, to_ty, c) u
    in
    (eff, f)
  in
  let ops = Assoc.kmap eval_op ops in
  let rec h = function
    | V.Value v -> eval_closure state value v
    | V.Call (eff, v, k) -> (
        let k' u = h (k u) in
        match Assoc.lookup eff ops with
        | Some f -> f v k'
        | None -> V.Call (eff, v, k'))
  in
  (* fun r -> sequence (eval_closure state fin) (h r) *)
  h

and eval_closure state a v =
  let p, _, c = a in
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
      | "Raise" -> Error.runtime "%t" (V.print_value v)
      | "RandomInt" ->
          let rnd_int = Random.int (V.to_int v) in
          let rnd_int_v = V.Const (Const.of_integer rnd_int) in
          top_handle (k rnd_int_v)
      | "RandomFloat" ->
          let rnd_float = Random.float (V.to_float v) in
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
          Error.runtime "uncaught effect %t %t." (V.print_effect eff)
            (V.print_value v))

let run state c = top_handle (ceval state c)
