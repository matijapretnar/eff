(* Taken varbatim from 
https://github.com/ocaml-multicore/effects-examples/blob/68f16120873f1ade4536ab3916ccce47fd424f9e/queens.ml 
*)

let absurd x = failwith "error"

effect Decide : unit -> bool
effect Fail : unit -> unit


let no_attack (x,y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let rec not_attacked x' qs =
  match qs with
  | [] -> true
  | x:: xs ->
      if no_attack x' x then not_attacked x' xs else false

let available number_of_queens x qs =
  let rec loop (possible, y) =
    if y < 1 then possible
    else if not_attacked ((x, y)) qs then
      loop ( (y:: possible), y - 1)
    else loop (possible, y - 1)
  in
  loop ([], number_of_queens)

let rec choose xs =
  match xs with
  | [] -> (absurd (perform (Fail ()))) 
  | (x:: xs') -> if perform (Decide ()) then x else choose xs'

let queens number_of_queens =
  let rec place (x, qs) =
    if x > number_of_queens then qs
    else
      let y = choose (available number_of_queens x qs) in
      place (x + 1, ((x, y):: qs))
  in
  place (1, [])

let queens_one_option number_of_queens =
  match queens number_of_queens
  with
  | effect (Decide _) k -> (
    let k' = Obj.clone_continuation k in
      match (continue k true) with
      | Some x -> Some x
      | None -> (continue k' false)
      )
  | effect (Fail _) _k -> None
  | y -> (Some y)

let queens_all number_of_queens =
  match queens number_of_queens
  with
    | effect (Decide _) k -> 
      let k' = Obj.clone_continuation k in 
      (continue k true) @ (continue k' false)
    | effect (Fail _) _k -> []
    | x -> [x]

let queens_one_cps number_of_queens =
  (match queens number_of_queens with
    | effect (Decide _) k ->
      let k' = Obj.clone_continuation k in 
      (fun kf -> (continue k true (fun _ -> (continue k' false kf)) ))
    | effect (Fail _) _k -> (fun kf -> kf ())
    | y -> (fun _ -> y))
  (fun () -> (absurd (perform (Fail ()))))

