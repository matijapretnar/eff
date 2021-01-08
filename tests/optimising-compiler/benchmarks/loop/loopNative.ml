let rec loop_pure n = if n = 0 then () else loop_pure (n - 1)

let test_pure n = loop_pure n

(******************************************************************************)

exception Fail

let rec loop_latent n =
  if n = 0 then () else if n < 0 then raise Fail else loop_latent (n - 1)

let test_latent n = loop_latent n

(******************************************************************************)

let rec loop_incr counter n =
  if n = 0 then ()
  else (
    incr counter;
    loop_incr counter (n - 1))

let test_incr n =
  let counter = ref 0 in
  loop_incr counter n

(******************************************************************************)

let rec loop_incr' counter n =
  if n = 0 then ()
  else (
    loop_incr' counter (n - 1);
    incr counter)

let test_incr' n =
  let counter = ref 0 in
  loop_incr' counter n

(******************************************************************************)

let rec loop_state state n =
  if n = 0 then ()
  else (
    state := !state + 1;
    loop_state state (n - 1))

let test_state n =
  let state = ref 0 in
  loop_state state n
