open Scheme
open Type


let filter_polymorphism drt =
  {drt with ops = List.filter (fun (op, _) -> op <> "///") drt.ops}

let show_dirt ~non_empty_dirts drt =
  let drt = filter_polymorphism drt in
  drt.ops <> [] || List.mem drt.rest non_empty_dirts


let print_operation ~non_poly r_ops =
  Print.sequence ", " (fun (op, r) ppf -> if op <> "///" then Print.print ppf "%s:%t" op (Params.print_region_param ~non_poly r)) r_ops

let print_dirt ~non_poly ~non_empty_dirts drt ppf =
  let drt = filter_polymorphism drt in
  match drt.ops with
  | [] ->
    if List.mem drt.rest non_empty_dirts then
      Print.print ppf "%t" (Params.print_dirt_param ~non_poly drt.rest)
  | _ ->
    if List.mem drt.rest non_empty_dirts then
      Print.print ppf "{%t|%t}" (print_operation ~non_poly drt.ops) (Params.print_dirt_param ~non_poly drt.rest)
    else
      Print.print ppf "{%t}" (print_operation ~non_poly drt.ops)


let print_ty ~non_poly ~non_empty_dirts ~skeletons t ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match t with
    | Arrow (t1, (t2, drt)) ->
      if !Config.effect_annotations && show_dirt ~non_empty_dirts drt then
        print ~at_level:5 "@[%t -%t%s@ %t@]"
          (ty ~max_level:4 t1)
          (print_dirt ~non_poly ~non_empty_dirts drt)
          (Symbols.short_arrow ())
          (ty ~max_level:5 t2)
      else
        print ~at_level:5 "@[%t@ %s@ %t@]" (ty ~max_level:4 t1) (Symbols.arrow ()) (ty ~max_level:5 t2)
    | Basic b -> print "%s" b
    | Apply (t, (lst, _, _)) ->
      begin match lst with
        | [] -> print "%s" t
        | [s] -> print ~at_level:1 "%t %s" (ty ~max_level:1 s) t
        | ts -> print ~at_level:1 "(%t) %s" (Print.sequence ", " ty ts) t
      end
    | Param p -> Params.print_ty_param ~non_poly p ppf
    | Tuple [] -> print "unit"
    | Tuple ts -> print ~at_level:2 "@[<hov>%t@]" (Print.sequence (Symbols.times ()) (ty ~max_level:1) ts)
    | Handler ((t1, drt1), (t2, drt2)) ->
      if !Config.effect_annotations then
        print ~at_level:6 "%t ! %t %s@ %t ! %t"
          (ty ~max_level:4 t1)
          (print_dirt ~non_poly ~non_empty_dirts drt1)
          (Symbols.handler_arrow ())
          (ty ~max_level:4 t2)
          (print_dirt ~non_poly ~non_empty_dirts drt2)
      else
        print ~at_level:6 "%t %s@ %t" (ty ~max_level:4 t1) (Symbols.handler_arrow ()) (ty ~max_level:4 t2)
  in ty t ppf


let print_ty_scheme ty_sch ppf =
  let ty_sch = Scheme.beautify_ty_scheme ty_sch in
  let skeletons, non_poly = Scheme.skeletons_non_poly_scheme ty_sch in
  let (ctx, ty, cnstrs) = ty_sch in
  let non_empty_dirts = Constraints.non_empty_dirts cnstrs in
  if !Config.effect_annotations then
    Print.print ppf "%t | %t"
      (print_ty ~non_poly ~non_empty_dirts ~skeletons ty)
      (Constraints.print cnstrs)
  else
    print_ty ~non_poly ~non_empty_dirts ~skeletons ty ppf

let print_dirty_scheme drty_sch ppf =
  let drty_sch = Scheme.beautify_dirty_scheme drty_sch in
  let skeletons, non_poly = Scheme.skeletons_non_poly_scheme drty_sch in
  let (ctx, (ty, drt), cnstrs) = drty_sch in
  let non_empty_dirts = Constraints.non_empty_dirts cnstrs in
  if !Config.effect_annotations then
    if show_dirt ~non_empty_dirts drt then
      Print.print ppf "%t ! %t | %t"
        (print_ty ~non_poly ~non_empty_dirts ~skeletons ty)
        (print_dirt ~non_poly ~non_empty_dirts drt)
        (Constraints.print cnstrs)
    else
      Print.print ppf "%t | %t"
        (print_ty ~non_poly ~non_empty_dirts ~skeletons ty)
        (Constraints.print cnstrs)
  else
    print_ty ~non_poly ~non_empty_dirts ~skeletons ty ppf
