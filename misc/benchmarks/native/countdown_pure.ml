let rec countdown s = if s = 0 then s else countdown (s - 1)
let () = Printf.printf "%d\n" (countdown (int_of_string Sys.argv.(1)))
