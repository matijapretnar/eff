(******************************************************************************)

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec not_attacked x' = function
  | [] -> true
  | x :: xs -> if no_attack x' x then not_attacked x' xs else false

let available (number_of_queens, x, qs) =
  let rec loop (possible, y) =
    if y < 1 then possible
    else if not_attacked (x, y) qs then loop (y :: possible, y - 1)
    else loop (possible, y - 1)
  in
  loop ([], number_of_queens)

(******************************************************************************)

exception Fail

let queens_one_exceptions number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then qs
    else
      let rec choose = function
        | [] -> raise Fail
        | y :: ys -> ( try place (x + 1, (x, y) :: qs) with Fail -> choose ys)
      in
      choose (available (number_of_queens, x, qs))
  in
  place (1, [])

(******************************************************************************)

let queens_one_option number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then Some qs
    else
      let rec choose = function
        | [] -> None
        | y :: ys -> (
            match place (x + 1, (x, y) :: qs) with
            | Some qs -> Some qs
            | None -> choose ys)
      in
      choose (available (number_of_queens, x, qs))
  in
  place (1, [])

(******************************************************************************)

let queens_one_cps number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then fun _ -> qs
    else
      let rec choose = function
        | [] -> fun k -> k ()
        | y :: ys ->
            fun k ->
              place (x + 1, (x, y) :: qs) (fun () -> choose ys (fun () -> k ()))
      in
      fun a -> choose (available (number_of_queens, x, qs)) a
  in
  place (1, []) (fun () -> [])

(******************************************************************************)

let queens_all number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then [ qs ]
    else
      let rec choose = function
        | [] -> []
        | y :: ys -> place (x + 1, (x, y) :: qs) @ choose ys
      in
      choose (available (number_of_queens, x, qs))
  in
  place (1, [])
