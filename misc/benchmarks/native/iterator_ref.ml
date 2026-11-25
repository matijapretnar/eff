let rec range l u emit =
  if l > u then ()
  else (
    emit l;
    range (l + 1) u emit)

let run n =
  let s = ref 0 in
  range 0 n (fun e -> s := !s + e);
  !s

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
