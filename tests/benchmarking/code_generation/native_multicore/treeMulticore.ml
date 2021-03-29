type tree
 = Empty
 | Node of tree * int * tree

effect Choose : unit -> bool

let tester k =
    let leaf a = Node (Empty, a * k, Empty) in
    let bot t t2 =
      Node
        ( Node (Node (t, 0, t2), 2, leaf 13),
          5,
          Node (leaf 9, 7, Node (t2, 3, Node (leaf 3, 5, t2))) )
    in
    let n1 = Node (bot (leaf 3) (leaf 4), 10, bot (leaf 1) (leaf 3)) in
    let n2 = bot (Node (bot (leaf 3) (leaf 4), 10, bot (leaf 1) (leaf 3))) (leaf 10) in
    bot n1 n2

;;

let max a b = if a > b then a else b

let op x y = x - 3*y


type intlist = Nil | Cons of (int * intlist)


let test_general (m: int) : int= 
  let t = tester m in
  let rec explore t = match t with
    | Empty -> 0
     | Node (left, x, right) -> 
      let next = if (perform (Choose ())) then (op x (explore left)) else op x (explore right) in
      next
  in
  List.fold_left max 0 (match explore t
  with
  | effect (Choose ()) k -> let k' = Obj.clone_continuation k in (continue k true) @ (continue k' false)
  | x -> [x]
  )

let test_leaf_state (m: int)= 
  let leafs = ref (List.init 154 (fun i -> i * 3)) in
  let t = tester m in
  let rec explore t = match t with
    | Empty -> (
      match !leafs with
        | x :: xs ->
            leafs := xs;
            x
        | [] -> assert false
     )
     | Node (left, x, right) -> 
      let next = if (perform (Choose ())) then left else right in
      (op x (explore next))
  in
  List.fold_left max 0 (match explore t
  with
  | effect (Choose ()) k -> 
    let k' = Obj.clone_continuation k in 
    (* 
    Explicit sequencing, as there is no guarantee on element evaluation order 
    Since both branches produce side effects and are non orthogonal, this is important.
    Not performance wise, but result wise. 
    *)
    let left_branch = (continue k' true) in 
    left_branch @ (continue k false)
  | x -> [x]
  )


(* 
# test_leaf_state 100;;
  - : int = 187924331 
*)