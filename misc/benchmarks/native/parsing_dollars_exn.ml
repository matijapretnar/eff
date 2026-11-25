(* Read, Emit and Stop as a function on a mutable input, a callback, and an
   exception *)
exception Stop

let newline = 10
let dollar = 36

let rec parse read emit a =
  let c = read () in
  if c = dollar then parse read emit (a + 1)
  else if c = newline then (
    emit a;
    parse read emit 0)
  else raise Stop

let run n =
  let i = ref 0 and j = ref 0 and s = ref 0 in
  let read () =
    if !i > n then raise Stop
    else if !j = 0 then (
      incr i;
      j := !i;
      newline)
    else (
      decr j;
      dollar)
  in
  (try parse read (fun e -> s := !s + e) 0 with Stop -> ());
  !s

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
