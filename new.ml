effect Print : string -> unit
effect Read : unit -> string
effect RandomInt : int -> int
effect RandomFloat : float -> float
let _ocaml_tophandler = (fun c ->  match c () with
  | effect (Print s) k -> (print_string s; continue k ())
  | effect (RandomInt i) k -> continue k (Random.int i)
  | effect (RandomFloat f) k -> continue k (Random.float f)
  | effect (Read ()) k -> continue k (read_line ())
  | x -> x )

let _op_1 (* = *) = (=)
let _op_2 (* < *) = (<)
let failwith = failwith
let infinity = infinity
let neg_infinity = neg_infinity
let nan = nan
let _op_7 (* ~- *) = (~-)
let _op_8 (* + *) = (+)
let _op_9 (* * *) = ( * )
let _op_10 (* - *) = (-)
let _op_11 (* mod *) = (mod)
let _op_12 (* ~-. *) = (~-.)
let _op_13 (* +. *) = (+.)
let _op_14 (* *. *) = ( *. )
let _op_15 (* -. *) = (-.)
let _op_16 (* /. *) = (/.)
let _op_17 (* ** *) = ( ** )
let _op_18 (* / *) = (/)
let exp = exp
let expm1 = expm1
let log = log
let log1p = log1p
let cos = cos
let sin = sin
let tan = tan
let acos = acos
let asin = asin
let atan = atan
let sqrt = sqrt
let float_of_int = float_of_int
let int_of_float = int_of_float
let _op_32 (* ^ *) = (^)
let string_length = String.length
let string_of_float = string_of_float
let string_of_int = string_of_int
type ('ty_5) option = None | Some of 'ty_5

effect Decide : unit -> bool
let _ = 
(_ocaml_tophandler) (fun _ -> 
(fun _comp_44 ->
   (match (_comp_44) (()) with
    | y -> y
    | effect (Decide ()) l ->
        (let l x = continue (Obj.clone_continuation l) x in 
        (l) (true)))) 
  (fun _ ->
     (fun x -> (fun _b_41 -> (_b_41) (1)) ((_op_10 (* - *)) (x))) 
       ((fun _b_40 -> (match _b_40 with | true -> 10 | false -> 20)) 
          (perform (Decide ()))))
);;
