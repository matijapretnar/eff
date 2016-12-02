open Scheme
open Type

let print_region_param ?(non_poly=Trio.empty) ((Region_Param k) as p) ppf =
  let (_, _, rs) = non_poly in
  Symbols.region_param k (List.mem p rs) ppf

let print_dirt_param ?(non_poly=Trio.empty) ((Dirt_Param k) as p) ppf =
  let (_, ds, _) = non_poly in
  Symbols.dirt_param k (List.mem p ds) ppf

let dirt_bound ?non_poly r_ops =
  Print.sequence ", " (fun (op, dt) ppf -> Print.print ppf "%s:%t" op (print_region_param dt)) r_ops

let print_dirt ?(non_poly=Trio.empty) ~show_dirt_param drt ppf =
  match drt.ops with
  | [] ->
    begin match show_dirt_param drt.rest with
    | Some f -> f ppf
    | None -> ()
    end
  | _ ->
    begin match show_dirt_param drt.rest with
    | Some f -> Print.print ppf "{%t|%t}" (dirt_bound ~non_poly drt.ops) f
    | None -> Print.print ppf "{%t}" (dirt_bound ~non_poly drt.ops)
    end


let print_ty_param ?(non_poly=Trio.empty) ((Ty_Param k) as p) ppf =
  let (ps, _, _) = non_poly in
  Symbols.ty_param k (List.mem p ps) ppf

let show_dirt show_dirt_param drt = drt.ops != [] || (show_dirt_param drt.rest != None)

let rec print ?(non_poly=Trio.empty) ?(show_dirt_param=fun d -> Some (print_dirt_param ~non_poly d)) skeletons t ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match t with
    | Arrow (t1, (t2, drt)) ->
        if !Config.effect_annotations && show_dirt show_dirt_param drt then
          print ~at_level:5 "@[%t -%t%s@ %t@]"
            (ty ~max_level:4 t1)
            (print_dirt ~non_poly ~show_dirt_param drt)
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
    | Param p -> print_ty_param ~non_poly p ppf
    | Tuple [] -> print "unit"
    | Tuple ts -> print ~at_level:2 "@[<hov>%t@]" (Print.sequence (Symbols.times ()) (ty ~max_level:1) ts)
    | Handler ((t1, drt1), (t2, drt2)) ->
        if !Config.effect_annotations then
          print ~at_level:6 "%t ! %t %s@ %t ! %t"
            (ty ~max_level:4 t1)
            (print_dirt ~non_poly ~show_dirt_param drt1)
            (Symbols.handler_arrow ())
            (ty ~max_level:4 t2)
            (print_dirt ~non_poly ~show_dirt_param drt2)
        else
          print ~at_level:6 "%t %s@ %t" (ty ~max_level:4 t1) (Symbols.handler_arrow ()) (ty ~max_level:4 t2)
  in ty t ppf

let show_dirt_param ~non_poly:(_, ds, _) =
  fun ((Type.Dirt_Param k) as p) -> Some (fun ppf -> (Symbols.dirt_param k (List.mem p ds) ppf))

let print_ty_scheme ty_sch ppf =
  let ty_sch = Scheme.beautify_ty_scheme ty_sch in
  let skeletons, non_poly = Scheme.skeletons_non_poly_scheme ty_sch in
  let show_dirt_param = show_dirt_param ~non_poly in
  let (ctx, ty, cnstrs) = ty_sch in
  if !Config.effect_annotations then
    Print.print ppf "%t | %t"
      (print ~show_dirt_param skeletons ty)
      (Constraints.print cnstrs)
  else
    print ~non_poly skeletons ty ppf

let print_dirty_scheme drty_sch ppf =
  let drty_sch = Scheme.beautify_dirty_scheme drty_sch in
  let skeletons, non_poly = Scheme.skeletons_non_poly_scheme drty_sch in
  let show_dirt_param = show_dirt_param ~non_poly in
  let (ctx, (ty, drt), cnstrs) = drty_sch in
  if !Config.effect_annotations then
    if show_dirt show_dirt_param drt then
      Print.print ppf "%t ! %t | %t"
        (print ~show_dirt_param skeletons ty)
        (print_dirt ~non_poly ~show_dirt_param drt)
        (Constraints.print cnstrs)
    else
      Print.print ppf "%t | %t"
        (print ~show_dirt_param skeletons ty)
        (Constraints.print cnstrs)
  else
    print ~non_poly skeletons ty ppf

