type tree = Leaf | Node of tree * int * tree

let rec make = function
  | 0 -> Leaf
  | n ->
      let t = make (n - 1) in
      Node (t, n, t)

(* The values in the order in which the generator yields them *)
let rec sum a = function Leaf -> a | Node (l, v, r) -> sum (sum a l + v) r
let () = Printf.printf "%d\n" (sum 0 (make (int_of_string Sys.argv.(1))))
