let rec fibonacci n =
  if n = 0 then 0 else if n = 1 then 1 else fibonacci (n - 1) + fibonacci (n - 2)

let () = Printf.printf "%d\n" (fibonacci (int_of_string Sys.argv.(1)))
