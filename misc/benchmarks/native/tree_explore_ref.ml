type tree = Leaf | Node of tree * int * tree

let operator x y = abs (x - (503 * y) + 37) mod 1009

let rec make = function
  | 0 -> Leaf
  | n ->
      let t = make (n - 1) in
      Node (t, n, t)

let run n =
  let tree = make n in
  let state = ref 0 in
  (* [path] holds the values above [t], the nearest first *)
  let rec explore t path =
    match t with
    | Leaf -> List.fold_left (fun y v -> operator v y) !state path
    | Node (l, v, r) ->
        state := operator !state v;
        let left = explore l (v :: path) in
        state := operator !state v;
        let right = explore r (v :: path) in
        max left right
  in
  let rec loop i =
    if i = 0 then !state
    else (
      state := explore tree [];
      loop (i - 1))
  in
  loop 10

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
