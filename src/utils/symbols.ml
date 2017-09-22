let less () = if !Config.ascii then "<=" else "≤"
let handler_arrow () = if !Config.ascii then "=>" else "⟹ "
let arrow () = if !Config.ascii then "->" else "⟶ "
let short_arrow () = if !Config.ascii then "->" else "→"
let times () = if !Config.ascii then " * " else " × "
let top () = if !Config.ascii then "T" else "⊤"

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

let param ascii_symbol utf8_symbol index poly ppf =
  let prefix = if poly then "_" else ""
  and symbol = if !Config.ascii then ascii_symbol else utf8_symbol
  in
  Print.print ppf "%s%s%s" prefix symbol (subscript (Some (index + 1)))

let ty_param = param "ty" "τ"
let dirt_param = param "drt" "δ"
let region_param  = param "rgn" "ρ"
