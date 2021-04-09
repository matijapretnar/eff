(* Triple -> Unknown *)

(* Queens *)

(* Taken verbatim from 
https://github.com/ocaml-multicore/effects-examples/blob/68f16120873f1ade4536ab3916ccce47fd424f9e/queens.ml 
*)

effect Select : 'a list -> 'a

let rec filter p = function
  | [] -> []
  | x :: xs ->
    if p x then (x :: filter p xs) else filter p xs

let rec forall p = function
  | [] -> true
  | x :: xs -> if p x then forall p xs else false

let no_attack (x,y) (x',y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available x qs l =
  filter (fun y -> forall (no_attack (x,y)) qs) l

let find_solution n =
  try
    let l = ref [] in
    for i = n downto 1 do
      l := i::!l;
    done;
    let rec place x qs =
      if x = n+1 then Some qs else
        let y = perform @@ Select (available x qs !l) in
        place (x+1) ((x, y) :: qs)
    in place 1 []
  with
  | effect (Select lst) k ->
      let rec loop = function
        | [] -> None
        | x::xs ->
            match continue (Obj.clone_continuation k) x with
            | None -> loop xs
            | Some x -> Some x
      in loop lst

let queens_all number_of_queens =
  find_solution number_of_queens

(* Count *)

effect CountPut: int -> unit
effect CountGet: unit -> int 
;;
let rec count () = 
  let i = perform (CountGet ()) in
  if i = 0 then i 
  else(
    (perform (CountPut (i-1)));
    count ()
  )

let testCount m = 
  (match count () 
  with
    | y -> (fun _ -> y)
    | effect (CountGet ()) k -> (
      fun (s: int) -> (continue k s) s
    )
    | effect (CountPut s) k -> (
      fun (_: int) -> (continue k ()) s
    )
  ) m

(* Generator *)

effect GeneratorPut: int -> unit
effect GeneratorGet: unit -> int 
effect GeneratorYield: int -> unit
;;

let testGenerator n =
  let rec generateFromTo l u =
    if (l > u)
      then ()
  else (
      perform (GeneratorYield l);
      generateFromTo (l + 1) u
  )
  in
  let comp =
    match (
        try (generateFromTo 1 n) with
        | effect (GeneratorYield e) k -> (perform (GeneratorPut (perform (GeneratorGet ()) + e)); continue k ())
    ) with
    | x -> (fun s -> s)
    | effect (GeneratorPut s') k -> (fun s -> continue k () s')
    | effect (GeneratorGet _) k -> (fun s -> continue k s s)
  in comp 0
  
    