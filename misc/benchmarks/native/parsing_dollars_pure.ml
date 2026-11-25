let newline = 10
let dollar = 36

(* The input is the line [i], with [j] dollars still to read. Its next
   character is computed on demand, as in the suite. [a] counts the dollars on
   the current line and [s] sums the emitted counts. *)
let run n =
  let rec parse a i j s =
    if i > n then s
    else
      let c, i, j =
        if j = 0 then (newline, i + 1, i + 1) else (dollar, i, j - 1)
      in
      if c = dollar then parse (a + 1) i j s
      else if c = newline then parse 0 i j (s + a)
      else s
  in
  parse 0 0 0 0

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
