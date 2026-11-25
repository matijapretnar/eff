let rec safe queen diag xs =
  match xs with
  | [] -> true
  | q :: qs ->
      queen <> q
      && queen <> q + diag
      && queen <> q - diag
      && safe queen (diag + 1) qs

(* The number of ways to complete the placement [rest] with [column] more
   queens *)
let rec place size column rest =
  if column = 0 then 1
  else
    let rec loop i a =
      if i > size then a
      else
        let a =
          if safe i 1 rest then a + place size (column - 1) (i :: rest) else a
        in
        loop (i + 1) a
    in
    loop 1 0

let run n = place n n []
let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
