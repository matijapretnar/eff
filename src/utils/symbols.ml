let less () = if !Config.ascii then "<=" else "≤"
let handler_arrow () = if !Config.ascii then "=>" else "⟹ "
let arrow () = if !Config.ascii then "->" else "⟶ "
let short_arrow () = if !Config.ascii then "->" else "→"
let times () = if !Config.ascii then " * " else " × "
let union () = if !Config.ascii then "+" else "∪"

let subscript sub =
  match sub with
  | None -> ""
  | Some i ->
      if !Config.ascii then
        string_of_int i
      else
        let rec sub i =
          let last = List.nth ["₀"; "₁"; "₂"; "₃"; "₄"; "₅"; "₆"; "₇"; "₈"; "₉"] (i mod 10) in
          if i < 10 then last else sub (i / 10) ^ last
        in
        sub i

let ty_param skel index poly ppf =
  if !Config.ascii then
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
    if skel < List.length letters then
      Print.print ppf "%s%s%s" c (List.nth letters skel) (subscript index)
    else
      Print.print ppf "%sτ%d%s" c (skel - List.length letters) (subscript index)

let dirt_param index poly ppf =
  if !Config.ascii then
    let c = if poly then "_drt" else "drt" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))
  else
    let c = if poly then "_δ" else "δ" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))

let region_param index poly ppf =
  if !Config.ascii then
    let c = if poly then "_rgn" else "rgn" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))
  else
    let c = if poly then "_ρ" else "ρ" in
    Print.print ppf "%s%s" c (subscript (Some (index + 1)))
