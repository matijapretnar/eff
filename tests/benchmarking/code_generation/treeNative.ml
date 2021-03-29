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

let op x y = x - (3 * y)

let test_general m =
  let rec maxl l = List.fold_left max 0 l in
  let t = tester m in
  let rec explore t =
    match t with
    | Empty -> [ 0 ]
    | Node (left, x, right) -> List.map (op x) (explore left @ explore right)
  in
  List.fold_left max 0 (explore t)

let rec count_leafs = function
  | Node (l, _, r) -> count_leafs l + count_leafs r
  | Empty -> 1

let test_leaf_state m =
  let leafs = ref (List.init 154 (fun i -> i * 3)) in
  let rec maxl l = List.fold_left max 0 l in
  let t = tester m in
  let rec explore t =
    match t with
    | Empty -> (
        match !leafs with
        | x :: xs ->
            leafs := xs;
            [ x ]
        | [] -> assert false)
    | Node (left, x, right) ->
        let lef = explore left in
        List.map (op x) (lef @ explore right)
  in

  List.fold_left max 0 (explore t)

(* 
# test_leaf_state 100;;
  - : int = 187924331 
*)
