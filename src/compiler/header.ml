type instance = int
type operation_symbol = string

type ('op_arg, 'op_res) operation = operation_symbol * instance

type 'a computation =
  | Value : 'a -> 'a computation
  | Op : ('op_arg, 'op_res) operation * 'op_arg * ('op_res -> 'a computation) -> 'a computation

type ('a, 'b) value_case = 'a -> 'b computation
type ('a, 'b) finally_case = 'a -> 'b computation

type _ operation_cases =
  | Nil : 'a operation_cases
  | Cons : ('op_arg, 'op_res) operation * ('op_arg -> ('op_res -> 'a computation) -> 'a computation) * 'a operation_cases -> 'a operation_cases

type ('a, 'b, 'c) handler = {
  value: ('a, 'b) value_case;
  finally: ('b, 'c) finally_case;
  operation_cases: 'b operation_cases;
}

let rec find_case : 'op_arg 'op_res. ('op_arg, 'op_res) operation -> 'a operation_cases -> ('op_arg -> ('op_res -> 'a computation) -> 'a computation) =
  fun op op_cases ->
    match op_cases with
    | Nil ->
      (fun x k -> Op (op, x, k))
    | Cons (op', case, op_cases) ->
      if op = op' then Obj.magic case else find_case op op_cases

let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Op (op, arg, k) -> Op (op, arg, fun y -> k y >> f)

let rec handle (h : ('a, _, 'b) handler) (c : 'a computation) : 'b computation =
  let c' = match c with
  | Value x -> h.value x
  | Op (op, arg, k) ->
    let f = find_case op h.operation_cases in
    f arg (fun y -> handle h (k y))
  in
  c' >> h.finally

let value (x : 'a) : 'a computation = Value x

let instance_count = ref 0
let new_instance () = incr instance_count; !instance_count

let apply_operation (op : ('a, 'b) operation) (arg : 'a) : 'b computation =
  Op (op, arg, value)

let run = function
  | Value x -> x
  | Op ((op, _), _, _) -> failwith ("Uncaught operation " ^ op)

let abs = fun x -> value (if x < 0 then -x else x)
let (<) = fun x -> value (fun y -> value (x < y))
let (=) = fun x -> value (fun y -> value (x = y))
let (+) = fun x -> value (fun y -> value (x + y))
let (&&) = fun x -> value (fun y -> value (x && y))
let (<>) = fun x -> value (fun y -> value (x <> y))
let (-) = fun x -> value (fun y -> value (x - y))
let raise exc = value (fun x -> Op (("raise", exc), x, fun _ -> assert false))
