open Typed

let rec optimize_comp c =
  match c.term with
  | Bind (c1, c2) ->
    begin match c1.term with
    | Value e -> let_in ~loc:c.location e c2
    | _ -> c
    end
  | _ -> c
