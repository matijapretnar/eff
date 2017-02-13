exception Fail

let rec loop_fail n =
  if n < 0 then
    raise Fail
  else if n = 0 then
    0
  else
    loop_fail (n - 1) + 1

let rec loop_acc_fail n acc =
  if n < 0 then
    raise Fail
  else if n = 0 then
    acc
  else
    loop_acc_fail (n - 1) (acc + 1)

(******************************************************************************)

let rec loop_option n =
  if n < 0 then
    None
  else if n = 0 then
    Some 0
  else
    match loop_option (n - 1) with
    | Some x -> Some (x + 1)
    | None -> None

let rec loop_acc_option n acc =
  if n < 0 then
    None
  else if n = 0 then
    Some acc
  else
    loop_acc_option (n - 1) (acc + 1)
