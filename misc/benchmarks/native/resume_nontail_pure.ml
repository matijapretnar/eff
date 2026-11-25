let operator x y = abs (x - (503 * y) + 37) mod 1009

(* Not tail-recursive, as the continuation is resumed in a non-tail position *)
let rec loop i s = if i = 0 then s else operator i (loop (i - 1) s)

let repeat n =
  let rec step l s = if l = 0 then s else step (l - 1) (loop n s) in
  step 1000 0

let () = Printf.printf "%d\n" (repeat (int_of_string Sys.argv.(1)))
