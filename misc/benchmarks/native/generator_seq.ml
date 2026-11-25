type tree = Leaf | Node of tree * int * tree

let rec make = function
  | 0 -> Leaf
  | n ->
      let t = make (n - 1) in
      Node (t, n, t)

let rec iterate t rest () =
  match t with
  | Leaf -> rest ()
  | Node (l, v, r) -> iterate l (fun () -> Seq.Cons (v, iterate r rest)) ()

let run n = Seq.fold_left ( + ) 0 (iterate (make n) Seq.empty)
let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
