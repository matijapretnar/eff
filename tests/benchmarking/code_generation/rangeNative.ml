type int_list = Nil | Cons of int * int_list

let test n =
  let rec range n = match n with 0 -> Nil | _ -> Cons (42, range (n - 1)) in
  range n

let testGenerator m =
  let n = 42 in
  let rec su i acc = if i = 0 then acc else su (i - 1) (acc + (i mod n)) in
  su m 0
