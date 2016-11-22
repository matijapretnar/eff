exception Fail

(******************************************************************************)

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available number_of_queens x qs =
  let rec loop possible y =
    if y < 1 then
      possible
    else if List.for_all (no_attack (x, y)) qs then
      loop (y :: possible) (y - 1)
    else
      loop possible (y - 1)
  in
  loop [] number_of_queens

(******************************************************************************)

let queens_one_fail number_of_queens =
  let rec place x qs =
    if x > number_of_queens then qs else
      let rec choose = function
        | [] -> raise Fail
        | y :: ys ->
            begin try place (x + 1) ((x, y) :: qs) with
            | Fail -> choose ys
            end
      in
      choose (available number_of_queens x qs)
  in
  place 1 []

(******************************************************************************)

let queens_one_option number_of_queens =
  let rec place x qs =
    if x > number_of_queens then Some qs else
      let rec choose = function
        | [] -> None
        | y :: ys ->
          begin match place (x + 1) ((x, y) :: qs) with
            | Some qs -> Some qs
            | None -> choose ys
          end
      in
      choose (available number_of_queens x qs)
  in
  place 1 []

(******************************************************************************)

let queens_all number_of_queens =
  let rec place x qs =
    if x > number_of_queens then [qs] else
      let rec choose = function
        | [] -> []
        | y :: ys ->
            place (x + 1) ((x, y) :: qs) @ choose ys
      in
      choose (available number_of_queens x qs)
  in
  place 1 []

