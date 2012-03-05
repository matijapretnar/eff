module V = Value
module T = Type

let types = [
  ("bool", ([], T.bool_ty));
  ("unit", ([], T.unit_ty));
  ("int", ([], T.int_ty));
  ("string", ([], T.string_ty));
  ("float", ([], T.float_ty));
  ("list", (let a = T.next_param () in
              ([a],
               T.Sum [(Common.nil, None);
                      (Common.cons, Some (T.Tuple [T.Param a; T.Apply ("list", [T.Param a])]))])));
  ("empty", ([], T.empty_ty));
]

(* Transformations from functions on constants to functions on values *)
let val_val_to f = V.from_fun (fun v1 -> V.value_fun (fun v2 -> f v1 v2))
let int_int_to f = val_val_to (fun v1 v2 -> f (V.to_int v1) (V.to_int v2))
let float_float_to f = val_val_to (fun v1 v2 -> f (V.to_float v1) (V.to_float v2))
let int_int_to_int f = int_int_to (fun n1 n2 -> V.value_int (f n1 n2))
let int_int_to_bool p = int_int_to (fun n1 n2 -> V.value_bool (p n1 n2))
let float_float_to_float f = float_float_to (fun n1 n2 -> V.value_float (f n1 n2))

(* Transformation of a built-in co-operation to a Value.continuation *)
let coop f v s =
  let (v, s) = f v s in V.Value (V.Tuple [v; s])

let symbols = [
  ("~-", V.from_fun (fun v -> V.value_int (Big_int.minus_big_int (V.to_int v))));
  ("~-.", V.from_fun (fun v -> V.value_float (-.(V.to_float v))));
  ("-", int_int_to_int Big_int.sub_big_int);
  ("+", int_int_to_int Big_int.add_big_int);
  ("*", int_int_to_int Big_int.mult_big_int);
  ("/", int_int_to_int Big_int.div_big_int);
  ("**", int_int_to_int Big_int.power_big_int_positive_big_int);
  ("-.", float_float_to_float (-.));
  ("+.", float_float_to_float (+.));
  ("*.", float_float_to_float ( *. ));
  ("/.", float_float_to_float (/.));
  ("%", int_int_to_int Big_int.mod_big_int);
  ("=", val_val_to (fun v1 v2 -> V.value_bool (V.equal v1 v2)));
  ("<", val_val_to (fun v1 v2 -> V.value_bool (V.less_than v1 v2)));
  ("^", val_val_to (fun v1 v2 -> V.value_str (V.to_str v1 ^ V.to_str v2)));
  ("string_length", V.from_fun (fun v -> V.value_int (Big_int.big_int_of_int (String.length (V.to_str v)))));
  ("to_string", V.from_fun (fun v -> let s = Print.to_string "%t" (Print.value v) in V.value_str s));
  ("float", V.from_fun (fun v -> V.value_float (Big_int.float_of_big_int (V.to_int v))));
  ("std", V.fresh_instance "standard I/O" (Some (ref V.from_unit, [
            ("write", coop (fun v s ->
                              let str = V.to_str v in
                                print_string str; flush stdout ;
                                (V.from_unit, s)));
             ("read", coop (fun v s ->
                              let str = read_line () in
                                (V.from_str str, s)));
            ])));
  ("err", V.fresh_instance "standard error" (Some (ref V.from_unit, [
             ("raise", coop (fun v s ->
                               let str = V.to_str v in
                                 Error.runtime "%s" str))])));

  ("rnd", (Random.self_init () ;
           V.fresh_instance "random number generator" (Some (ref V.from_unit, [
             ("int", coop (fun k s -> (V.from_int (Big_int.big_int_of_int (Random.int (Big_int.int_of_big_int (V.to_int k))))), s));
             ("float", coop (fun x s -> (V.from_float (Random.float (V.to_float x))), s));
           ]))
   ));
]
