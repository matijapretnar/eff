type tree = Leaf | Node of tree * int * tree

let operator x y = abs (x - (503 * y) + 37) mod 1009

let rec make = function
  | 0 -> Leaf
  | n ->
      let t = make (n - 1) in
      Node (t, n, t)

(* The state goes through the whole search: the right subtree starts with the
   state that the left subtree leaves. [path] holds the values above [t], the
   nearest first. The result is the largest value of a path and the final
   state. *)
let rec explore t path state =
  match t with
  | Leaf -> (List.fold_left (fun y v -> operator v y) state path, state)
  | Node (l, v, r) ->
      let left, state = explore l (v :: path) (operator state v) in
      let right, state = explore r (v :: path) (operator state v) in
      (max left right, state)

let run n =
  let tree = make n in
  let rec loop i state =
    if i = 0 then state
    else
      let best, _ = explore tree [] state in
      loop (i - 1) best
  in
  loop 10 0

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
