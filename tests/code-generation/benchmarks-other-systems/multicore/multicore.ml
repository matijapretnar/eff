type empty;;

let absurd void = match void with | _ -> assert false;;

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec not_attacked x' = function
  | [] -> true
  | x :: xs -> if no_attack x' x then not_attacked x' xs else false

let available (number_of_queens, x, qs) =
  let rec loop (possible, y) =
    if y < 1 then
      possible
    else if not_attacked (x, y) qs then
      loop ((y :: possible), (y - 1))
    else
      loop (possible, (y - 1))
  in
  loop ([], number_of_queens)

(******************************************************************************)

effect Decide : unit -> bool
effect Fail : unit -> empty

type 'a option = None | Some of 'a

let rec choose = function
  | [] -> absurd (perform @@ Fail ())
  | x::xs -> if (perform @@ Decide ()) then x else choose xs

(******************************************************************************)

let queens number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then qs else
      let y = choose (available (number_of_queens, x, qs)) in
      place ((x + 1), ((x, y) :: qs))
  in
  place (1, [])

let queens_one_option number_of_queens =
  match (queens number_of_queens)
  with
  | effect (Decide _) k -> (match continue (Obj.clone_continuation k) true with Some x -> Some x | None -> continue (Obj.clone_continuation k) false)
  | effect (Fail _) k -> None
  | x -> (Some x)

let queens_one_cps number_of_queens =
  (
    match (queens number_of_queens)
    with
    | effect (Decide _) k -> (fun kf -> continue (Obj.clone_continuation k) true (fun () -> continue (Obj.clone_continuation k) false kf) )
    | effect (Fail _) k -> (fun kf -> kf ())
    | x -> (fun _ -> x)
  )
    (fun () -> (absurd (perform @@ Fail ())))

let queens_all number_of_queens =
  match (queens number_of_queens)
  with
  | effect (Decide _) k -> continue (Obj.clone_continuation k) true @ continue (Obj.clone_continuation k) false
  | effect (Fail _) k -> []
  | x -> [x]
