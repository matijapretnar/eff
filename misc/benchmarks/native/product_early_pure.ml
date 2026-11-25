(* Without an early exit: at a zero, the product returns 0, and every frame
   above it still multiplies by it. *)
let rec product = function
  | [] -> 0
  | y :: ys -> if y = 0 then 0 else y * product ys

let rec enumerate i = if i < 0 then [] else i :: enumerate (i - 1)

let run n =
  let xs = enumerate 1000 in
  let rec loop i a = if i = 0 then a else loop (i - 1) (a + product xs) in
  loop n 0

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
