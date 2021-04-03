(* Triple -> Unknown *)

(* Queens *)

(* Count *)
let testCount m =
  let state = ref m in
  let rec count () =
    let i = !state in
    if i = 0 then i
    else (
      state := i - 1;
      count ())
  in
  count ()

(* Generator *)

let testGenerator m =
  let n = 42 in
  let rec su i acc = if i = 0 then acc else su (i - 1) (acc + (i mod n)) in
  su m 0
