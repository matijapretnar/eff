(* Evaluation of the intermediate language, big step. *)

module V = Value
module Core = CoreSyntax
module RuntimeEnv = Map.Make (CoreSyntax.Variable)

type state = Value.value RuntimeEnv.t

let empty = RuntimeEnv.empty

let update x = RuntimeEnv.add x

let lookup x env = try Some (RuntimeEnv.find x env) with Not_found -> None

exception PatternMatch of Location.t

let rec extend_value p v env =
  match (p.Core.term, v) with
  | Core.PVar x, v -> update x v env
  | Core.PAs (p, x), v ->
      let env = extend_value p v env in
      update x v env
  | Core.PNonbinding, _ -> env
  | Core.PTuple ps, Value.Tuple vs -> List.fold_right2 extend_value ps vs env
  | Core.PRecord ps, Value.Record vs -> (
      let rec extend_record ps vs env =
        match ps with
        | [] -> env
        | (f, p) :: ps ->
            let v = List.assoc f vs in
            extend_record ps vs (extend_value p v env)
      in
      try extend_record ps vs env with Not_found ->
        raise (PatternMatch p.Core.location) )
  | Core.PVariant (lbl, None), Value.Variant (lbl', None) when lbl = lbl' ->
      env
  | Core.PVariant (lbl, Some p), Value.Variant (lbl', Some v) when lbl = lbl' ->
      extend_value p v env
  | Core.PConst c, Value.Const c' when Const.equal c c' -> env
  | _, _ -> raise (PatternMatch p.Core.location)


let extend p v env =
  try extend_value p v env with PatternMatch loc ->
    Error.runtime "Pattern match failure."


let rec sequence k = function
  | V.Value v -> k v
  | V.Call (op, v, k') ->
      let k'' u = sequence k (k' u) in
      V.Call (op, v, k'')


let rec ceval env c =
  let loc = c.Core.location in
  match c.Core.term with
  | Core.Apply (e1, e2) -> (
      let v1 = veval env e1 and v2 = veval env e2 in
      match v1 with
      | V.Closure f -> f v2
      | _ -> Error.runtime "Only functions can be applied." )
  | Core.Value e -> V.Value (veval env e)
  | Core.Match (e, cases) ->
      let v = veval env e in
      let rec eval_case = function
        | [] -> Error.runtime "No branches succeeded in a pattern match."
        | a :: lst ->
            let p, c = a in
            try ceval (extend_value p v env) c with PatternMatch _ ->
              eval_case lst
      in
      eval_case cases
  | Core.Handle (e, c) ->
      let v = veval env e in
      let r = ceval env c in
      let h = V.to_handler v in
      h r
  | Core.Let (lst, c) -> eval_let env lst c
  | Core.LetRec (defs, c) ->
      let env = extend_let_rec env defs in
      ceval env c
  | Core.Check c ->
      let r = ceval env c in
      Print.check ~loc "%t" (Value.print_result r) ;
      V.unit_result


and eval_let env lst c =
  match lst with
  | [] -> ceval env c
  | (p, d) :: lst ->
      let r = ceval env d in
      sequence (fun v -> eval_let (extend p v env) lst c) r


and extend_let_rec env defs =
  let env' = ref env in
  let env =
    List.fold_right
      (fun (f, a) env ->
        let p, c = a in
        let g = V.Closure (fun v -> ceval (extend p v !env') c) in
        update f g env )
      defs env
  in
  env' := env ;
  env


and veval env e =
  match e.Core.term with
  | Core.Var x -> (
    match lookup x env with
    | Some v -> v
    | None -> Error.runtime "Name %t is not defined." (Core.Variable.print x) )
  | Core.Const c -> V.Const c
  | Core.Tuple es -> V.Tuple (List.map (veval env) es)
  | Core.Record es -> V.Record (List.map (fun (f, e) -> (f, veval env e)) es)
  | Core.Variant (lbl, None) -> V.Variant (lbl, None)
  | Core.Variant (lbl, Some e) -> V.Variant (lbl, Some (veval env e))
  | Core.Lambda a -> V.Closure (eval_closure env a)
  | Core.Effect eff -> V.Closure (fun v -> V.Call (eff, v, fun r -> V.Value r))
  | Core.Handler h -> V.Handler (eval_handler env h)


and eval_handler env
    { Core.effect_clauses= ops
    ; Core.value_clause= value
    ; Core.finally_clause= fin } =
  let eval_op (op, a2) =
    let p, kvar, c = a2 in
    let f u k = eval_closure (extend kvar (V.Closure k) env) (p, c) u in
    (op, f)
  in
  let ops = List.map eval_op ops in
  let rec h = function
    | V.Value v -> eval_closure env value v
    | V.Call (eff, v, k) ->
        let k' u = h (k u) in
        match OldUtils.lookup eff ops with
        | Some f -> f v k'
        | None -> V.Call (eff, v, k')
  in
  fun r -> sequence (eval_closure env fin) (h r)


and eval_closure env a v =
  let p, c = a in
  ceval (extend p v env) c


and eval_closure2 env a2 v1 v2 =
  let p1, p2, c = a2.Core.term in
  ceval (extend p2 v2 (extend p1 v1 env)) c


let rec top_handle = function
  | V.Value v -> v
  | V.Call ("Print", v, k) ->
      let str = V.to_str v in
      print_string str ;
      flush stdout ;
      top_handle (k V.unit_value)
  | V.Call ("Raise", v, k) -> Error.runtime "%t" (Value.print_value v)
  | V.Call ("Random_int", v, k) ->
      let rnd_int = Random.int (Value.to_int v) in
      let rnd_int_v = V.Const (Const.of_integer rnd_int) in
      top_handle (k rnd_int_v)
  | V.Call ("Random_float", v, k) ->
      let rnd_float = Random.float (Value.to_float v) in
      let rnd_float_v = V.Const (Const.of_float rnd_float) in
      top_handle (k rnd_float_v)
  | V.Call ("Read", v, k) ->
      let str = read_line () in
      let str_v = V.Const (Const.of_string str) in
      top_handle (k str_v)
	 
	 
  | V.Call ("Read_file", v, k) ->
      let filename =  V.to_str v in
 	 let channel = open_in filename in
 	 let text = ref "" in
 	 (
 	 try
 	    while true do
 	      text := !text  ^ (input_line channel) ^ "\n"   (* Gather text into a single string. *)
 	    done; 
 	    close_in channel;
 	    top_handle (k (V.Const (Const.of_string !text)))   (* This is only for typechecking. *)
 	 with End_of_file ->
 	     close_in channel;
 	     top_handle (k (V.Const (Const.of_string !text)))
 	 )
	  
  (*  effect Open_in : string -> in_channel *)
  | V.Call ("Open_in", v , k) ->
      let filename =  V.to_str v in
 	 let channel = open_in filename in
 	 (
	 try
 		top_handle (k (V.Const (Const.of_in_channel channel) ))
 	 with e ->                      (* some unexpected exception occurs *)
 		close_in channel;
 		top_handle (k (V.Const (Const.of_in_channel channel) ))
 	 )
  (* effect effect Open_out : string -> out_channel *)
  | V.Call ("Open_out", v , k) ->
      let filename =  V.to_str v in
 	 let channel = open_out filename in
 	 (
	 try
 		top_handle (k (V.Const (Const.of_out_channel channel) ))
 	 with e ->                      (* some unexpected exception occurs *)
 		close_out channel;
 		top_handle (k (V.Const (Const.of_out_channel channel) ))
 	 )
	
  (* effect  effect Close_in : in_channel -> unit *)
  | V.Call ("Close_in", v , k) ->
      let channel =  V.to_in_channel v in
 	 close_in channel;
      top_handle (k V.unit_value)
	
  (*  effect Close_out : out_channel -> unit *)
  | V.Call ("Close_out", v , k) ->
      let channel =  V.to_out_channel v in
 	 close_out channel;
      top_handle (k V.unit_value)
	 
  (* effect Write_file : (out_channel * string) -> unit *)
  | V.Call ("Write_file", v , k) ->
      let channel = V.to_out_channel (V.first v) in
 	 let text =  V.to_str (V.second v) in
 	 (
	 try
 		output_string channel text;
 		flush channel;
 		top_handle (k V.unit_value)
 	 with End_of_file ->              (* some unexpected exception occurs *)
 		close_out channel;
 		top_handle (k V.unit_value)
 	 )
  (* effect Read_line : in_channel -> string  *) 
  | V.Call ("Read_line", v, k) ->
      let channel =  V.to_in_channel v in
 	 let text = ref "" in
 	 (
 	 try
 	     text := !text  ^ (input_line channel) ^ "\n";   (* Gather text into a single string. *)
 	   	top_handle (k (V.Const (Const.of_string !text)))   (* This is only for typechecking. *)
 	 with End_of_file ->
 	     close_in channel;
 	     top_handle (k (V.Const (Const.of_string !text)))
 	 ) 

  | V.Call (eff, v, k) ->
      Error.runtime "uncaught effect %t %t." (Value.print_effect eff)
        (Value.print_value v)


let run env c = top_handle (ceval env c)
