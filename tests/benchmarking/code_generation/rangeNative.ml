type int_list = Nil | Cons of int * int_list

let test n =
  let rec range n = match n with 0 -> Nil | _ -> Cons (42, range (n - 1)) in
  range n
