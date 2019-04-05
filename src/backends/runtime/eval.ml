(* Evaluation of the intermediate language, big step. *)
open CoreUtils
module V = Value
module Untyped = UntypedSyntax

exception PatternMatch of Location.t

let help_text =
  "Toplevel commands:\n"
  ^ "#type <expr>;;     print the type of <expr> without evaluating it\n"
  ^ "#reset;;           forget all definitions (including pervasives)\n"
  ^ "#help;;            print this help\n" ^ "#quit;;            exit eff\n"
  ^ "#use \"<file>\";;  load commands from file\n"

module type OutputFormatter = sig
    val ppf : Format.formatter
 end

module Backend (OutF : OutputFormatter) : BackendSignature.T = struct
  module RuntimeEnv = Map.Make (CoreTypes.Variable)
  
  let ppf = OutF.ppf

  (* prints tells us wheter or not to print, while mute depth makes sure that
  printing is muted in the case of nested #use *)
  type state = {prints: bool; mute_depth : int; env: Value.value RuntimeEnv.t}

  let initial_state = {prints= true; mute_depth= 0; env= RuntimeEnv.empty}

  let load_mode state = 
    {state with prints= false; mute_depth = state.mute_depth + 1}

  let execute_mode state = 
    if state.mute_depth <= 1 then
      {state with prints= true; mute_depth = 0}
    else
      {state with mute_depth= state.mute_depth - 1}

  (* Auxiliary functions *)
  let update x v state = {state with env= RuntimeEnv.add x v state.env}

  let lookup x state = 
    try Some (RuntimeEnv.find x state.env) with Not_found -> None

  let rec extend_value p v state =
    match (p.it, v) with
    | Untyped.PVar x, v -> update x v state
    | Untyped.PAnnotated (p, t), v -> extend_value p v state
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
        try Assoc.fold_left extender state ps with Not_found ->
          raise (PatternMatch p.at) )
    | Untyped.PVariant (lbl, None), Value.Variant (lbl', None) when lbl = lbl' ->
        state
    | Untyped.PVariant (lbl, Some p), Value.Variant (lbl', Some v)
      when lbl = lbl' ->
        extend_value p v state
    | Untyped.PConst c, Value.Const c' when Const.equal c c' -> state
    | _, _ -> raise (PatternMatch p.at)
  
  let extend p v state =
    try extend_value p v state with PatternMatch loc ->
      Error.runtime "Pattern match failure."
  
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
        | _ -> Error.runtime "Only functions can be applied." )
    | Untyped.Value e -> V.Value (veval state e)
    | Untyped.Match (e, cases) ->
        let v = veval state e in
        let rec eval_case = function
          | [] -> Error.runtime "No branches succeeded in a pattern match."
          | a :: lst -> (
              let p, c = a in
              try ceval (extend_value p v state) c with PatternMatch _ ->
                eval_case lst )
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
        Print.check ~loc "%t" (Value.print_result r) ;
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
          update f g state )
        defs state
    in
    state' := state ;
    state
  
  and veval state e =
    match e.it with
    | Untyped.Var x -> (
      match lookup x state with
      | Some v -> v
      | None ->
          Error.runtime "Name %t is not defined." (CoreTypes.Variable.print x) )
    | Untyped.Const c -> V.Const c
    | Untyped.Annotated (t, ty) -> veval state t
    | Untyped.Tuple es -> V.Tuple (List.map (veval state) es)
    | Untyped.Record es -> V.Record (Assoc.map (fun e -> veval state e) es)
    | Untyped.Variant (lbl, None) -> V.Variant (lbl, None)
    | Untyped.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval state e))
    | Untyped.Lambda a -> V.Closure (eval_closure state a)
    | Untyped.Effect eff ->
        V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
    | Untyped.Handler h -> V.Handler (eval_handler state h)
  
  and eval_handler state
      { Untyped.effect_clauses= ops
      ; Untyped.value_clause= value
      ; Untyped.finally_clause= fin } =
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
          | None -> V.Call (eff, v, k') )
    in
    fun r -> sequence (eval_closure state fin) (h r)
  
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

  (* Processing functions *)
  let process_computation state c ty =
    let v = run state c in
    (if state.prints then
      Format.fprintf ppf "@[- : %t = %t@]@." (Type.print_beautiful ty)
        (Value.print_value v) 
    else () );
    state

  let process_type_of state c ty =
    (if state.prints then
      Format.fprintf ppf "@[- : %t@]@." (Type.print_beautiful ty)
    else () );
    state

  let process_reset state =
    (if state.prints then
      Format.fprintf ppf "Environment reset."
    else () );
    initial_state

  let process_help state =
    (if state.prints then
      Format.fprintf ppf "%s" help_text
    else () );
    state
  
  let process_def_effect state (eff, (ty1, ty2)) = state

  let process_top_let state defs vars =
    let state' =
      List.fold_right
        (fun (p, c) st -> let v = run st c in extend p v st )
        defs state
    in
    List.iter
      (fun (x, tysch) ->
        match lookup x state' with
        | None -> assert false
        | Some v ->
            (if state.prints then
              Format.fprintf ppf "@[val %t : %t = %t@]@."
                (CoreTypes.Variable.print x)
                (Type.print_beautiful tysch)
                (Value.print_value v) 
            else () ))
      vars ;
    state'

  let process_top_let_rec state defs vars =
    let state' = extend_let_rec state defs in
    List.iter
      (fun (x, tysch) ->
        (if state.prints then
          Format.fprintf ppf "@[val %t : %t = <fun>@]@."
            (CoreTypes.Variable.print x)
            (Type.print_beautiful tysch) 
        else () ))
      vars ;
    state'

  let process_external state (x, ty, f) =
    match Assoc.lookup f External.values with
      | Some v -> update x v state
      | None -> Error.runtime "unknown external symbol %s." f

  let process_tydef state tydefs = state

  let finalize state = ()

end