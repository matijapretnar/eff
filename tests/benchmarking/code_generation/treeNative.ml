type tree = Empty | Node of tree * int * tree

let tester (k : int) =
  let leaf (a : int) = Node (Empty, a * k, Empty) in
  let bot (t : tree) (t2 : tree) =
    Node
      ( Node (Node (t, 0, t2), 2, leaf 13),
        5,
        Node (leaf 9, 7, Node (t2, 3, Node (leaf 3, 5, t2))) )
  in
  let n1 = Node (bot (leaf 3) (leaf 4), 10, bot (leaf 1) (leaf 3)) in
  let n2 =
    bot (Node (bot (leaf 3) (leaf 4), 10, bot (leaf 1) (leaf 3))) (leaf 10)
  in
  bot n1 n2

let max a b = if a > b then a else b

let rec find_max t =
  match t with
  | Empty -> 0
  | Node (Empty, x, Empty) -> x
  | Node (left, x, right) -> x + max (find_max left) (find_max right)

let test_max m =
  let t = tester m in
  find_max t
