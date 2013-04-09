let ascii = ref false

let less () = if !ascii then "<=" else "≤"
let handler_arrow () = if !ascii then "=>" else "⟹ "

let subscript sub =
  match sub with
  | None -> ""
  | Some i ->
      if !ascii then
        string_of_int i
      else
        let rec sub i =
          let last = List.nth ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"] (i mod 10) in
          if i < 10 then last else sub (i / 10) ^ last
        in
        sub i

let ty_param skel index poly ppf =
  if !ascii then
    let c = if poly then "'_" else "'" in
    if skel <= 25 then
      Print.print ppf "%s%c%s" c (char_of_int (skel + int_of_char 'a')) (subscript index)
    else
      Print.print ppf "%st%i%s" c (skel - 25) (subscript index)
  else
    let c = if poly then "_" else "" in
    let letters =
      ["α"; "β"; "γ"]
    in
    if skel <= List.length letters then
      Print.print ppf "%s%s%s" c (List.nth letters skel) (subscript index)
    else
      Print.print ppf "%sτ%s₍%s₎" c (subscript (Some (skel - List.length letters))) (subscript index)

let dirt_param index poly ppf =
  if !ascii then
    let c = if poly then "_drt" else "drt" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))
  else
    let c = if poly then "_δ" else "δ" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))

let region_param index poly ppf =
  if !ascii then
    let c = if poly then "_rgn" else "rgn" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))
  else
    let c = if poly then "_ρ" else "ρ" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))
(*     



  let print_ty_param ?(non_poly=Trio.empty) skeletons p ppf =
  let (ps, _, _) = non_poly in
  let Ty_Param k = p in 
  let rec get_skel_id skel id = function
  | [] -> k - List.length (List.flatten skeletons) + List.length skeletons, -1
  | [] :: skels -> get_skel_id (succ skel) 0 skels
  | (Ty_Param l :: xs) :: _ when k == l ->
      if id = 0 && List.length xs = 0 then skel, -1 else skel, id
  | (_ :: xs) :: skels -> get_skel_id skel (succ id) (xs :: skels)
  in
  let skel, id = get_skel_id 0 0 skeletons in
  let c = (if List.mem p ps then "'_" else "'") in
  let index = if !effects && id != -1 then string_of_int (id + 1) else "" in
  if skel <= 25 then
    Print.print ppf "%s%c%s" c (char_of_int (skel + int_of_char 'a')) index
  else
    Print.print ppf "%st%i%s" c (skel - 25) index
 *)

(* let letters () =
    if !ascii then
        ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ"; "ο"]
 *)
(* let type_letters () =
  if !ascii then
    ['']

=======
let print_ty_param ?(non_poly=Trio.empty) ?skeletons p ppf =
  let (ps, _, _) = non_poly in
  match skeletons with
  | None ->
        let (Ty_Param k) = p in
        let c = (if List.mem p ps then "'_" else "'") in
      (*  if 0 <= k && k <= 6
          then print ppf "%s%c" c (char_of_int (k + int_of_char 't'))
          else print ppf "%st%i" c (k - 6)
       *)    if 0 <= k && k <= 25
          then Print.print ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
          else Print.print ppf "%st%i" c (k - 25)
  | Some skeletons ->
    let rec get_skel_id skel id = function
    | [] -> assert false
    | [] :: skels -> get_skel_id (succ skel) 0 skels
    | (x :: _) :: _ when p == x -> skel, id
    | (_ :: xs) :: skels -> get_skel_id skel (succ id) (xs :: skels)
    in
    let letters = ["α"; "β"; "γ"; "δ"; "ε"; "ζ"; "η"; "θ"; "ι"; "κ"; "λ"; "μ"; "ν"; "ξ"; "ο"] in
    let numbers = ["₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"] in
    let skel, id = get_skel_id 0 0 skeletons in
    let c = (if List.mem p ps then "_" else "") in
  (*  if 0 <= k && k <= 6
      then print ppf "%s%c" c (char_of_int (k + int_of_char 't'))
      else print ppf "%st%i" c (k - 6)
 *)    if skel <= List.length letters
      then Print.print ppf "%s%s%s" c (List.nth letters skel) (List.nth numbers id)
      else Print.print ppf "%st%i%d" c (skel - 25) id
>>>>>>> Stashed changes *)