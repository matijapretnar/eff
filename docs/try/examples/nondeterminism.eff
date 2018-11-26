(** Non-determinism *)

(* We will model non-determinism by implementing two operations, Decide and
   Fail. Decide will be used to `non-deterministically' choose the correct path
   while Fail signals that a choice fails to return a suitable answer.

   Effects that do not need any input can be defined by using unit as input
   or with the alternative syntax (demonstrated below) where they are implicitly
   treated as effect with input of type unit.*)

effect Fail : empty   (* This is equivalent to the type unit -> empty. *)
effect Decide : bool

(* We use a trick to ensure that using Fail typechecks correctly by wrapping
   it in a function. For aesthetic purposes we also wrap Decide in a function. *)

let fail () = absurd (perform Fail) (* Equivalent to perform (Fail ()). *)
let decide () = perform Decide
;;

(* We create a few different handlers to handle the above effects. The simplest
   handler is "choose_true" that always decides to use true. A more interesting
   example is the "choose_max" handler, that returns the maximal result of all
   possible choices, while "choose_all" instead returns a list of all possible
   results. *)

let choose_true = handler
    | effect Decide k -> continue k true

(* In the case of choose_max and choose_all the continuation is used twice.*)
let choose_max = handler
    | effect Decide k -> max (continue k true) (continue k false)

let choose_all = handler
    | x -> [x]
    | effect Fail _ -> []
    | effect Decide k -> (continue k true) @ (continue k false)
;;

(* Even on a small example the behaviour of the three handlers varies greatly. *)
with choose_true handle
  let x = (if decide () then 10 else 20) in
  let y = (if decide () then 0 else 5) in
  x - y
;;

with choose_max handle
  let x = (if decide () then 10 else 20) in
  let y = (if decide () then 0 else 5) in
  x - y
;;

with choose_all handle
  let x = (if decide () then 10 else 20) in
  let y = (if decide () then 0 else 5) in
  x - y
;;

(* We can use our boolean decision to construct a decision over integers.
   In the decision we only consider integers on an interval [m,n]. *)

let rec choose_int m n =
  if m > n then
    fail ()
  else if decide () then
    m
  else
    choose_int (m + 1) n
;;

(* This can be used for finding pythagorean triples. *)

let int_sqrt m =
  (* Returns an integer square root if it exists. *)
  let rec try n =
    let n2 = n ** 2 in
    if n2 > m then
      None
    else if n2 = m then
      Some n
    else
      try (n + 1)
  in
  try 0
;;

let pythagorean m n =
  (* Choose the bigger integer. *)
  let a = choose_int m (n - 1) in
  (* Choose the smaller integer. *)
  let b = choose_int a n in
  (* Check if they are part of a pythagorean triple. *)
  match int_sqrt (a ** 2 + b ** 2) with
  | None -> fail ()
  | Some c -> (a, b, c)
;;

(* We also construct an additional handler that simply tries to get one viable
   solution. *)
let backtrack = handler
  | effect Decide k ->
    (* We use a second handler to handle the continuation. *)
    handle continue k false with
    | effect Fail _ -> continue k true
;;

(* You can test the different handlers on the following examples. *)
with backtrack handle
  pythagorean 5 15
;;

with choose_all handle
  pythagorean 3 4
;;

with choose_all handle
  pythagorean 5 15
;;

(* Eight queens problem *)

(* Using the non-determinism approach we can also solve more complex problems,
   for instance the well known eight queens problem. *)

let rec choose = function
  | [] -> fail ()
  | x :: xs -> if decide () then x else choose xs

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y');;

(* For a given x check available y. *)
let available x qs =
  filter (fun y -> forall (no_attack (x, y)) qs) [1; 2; 3; 4; 5; 6; 7; 8];;

let rec place x qs =
  if x = 9 then qs else
  let y = choose (available x qs) in
  place (x + 1) ((x, y) :: qs)

;;

with backtrack handle
  place 1 []
;;
