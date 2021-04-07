let absurd x = failwith "error"
let rec loop_pure n =
  if n = 0 then
      ()
  else
      loop_pure (n - 1)

let test_pure n =
  loop_pure n

effect Fail : unit -> unit

let rec loop_latent n =
    if n = 0 then
        ()
    else if n < 0 then
        ( absurd (perform (Fail ())))
    else
        loop_latent (n - 1)

let test_latent n =
    loop_latent n

effect Incr : unit -> unit

let rec loop_incr n =
    if n = 0 then
        ()
    else
        (perform (Incr ()); loop_incr (n - 1))

let test_incr n =
    (match loop_incr n
    with 
    | effect (Incr ()) k -> (fun x -> (continue k ()) (x + 1))
    | _ -> (fun x -> x) 
    ) 0


let rec loop_incr' n =
  if n = 0 then
      ()
  else
      (loop_incr' (n - 1); perform (Incr ()))
  
let test_incr' n =
  (match loop_incr' n with
  | y -> (fun x -> x)
  | effect (Incr ()) k -> (fun x -> (continue k ()) (x + 1))      
  ) 0

effect Get: unit -> int
effect Put: int -> unit
  
let rec loop_state n =
  if n = 0 then
    ()
  else
    (perform (Put ((perform (Get ())) + 1)); loop_state (n - 1))

let test_state n =
  (match loop_state n
  with
  | y -> (fun x -> x)
  | effect (Get ()) k -> (fun (s:int) -> (continue k s) s) (* Annotation is needed for type inference *)
  | effect (Put s') k -> (fun _ -> (continue k ()) s')
  ) 0