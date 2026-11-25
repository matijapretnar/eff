let rec range l u a = if l > u then a else range (l + 1) u (a + l)
let () = Printf.printf "%d\n" (range 0 (int_of_string Sys.argv.(1)) 0)
