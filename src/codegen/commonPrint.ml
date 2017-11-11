(** TYPES *)

let rec print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Type.Apply ("empty", _) ->
    print "unit"
  | Type.Apply (ty_name, args) ->
    print ~at_level:1 "%t %s" (print_args args) ty_name
  | Type.TyVar p ->
    print "%t" (Params.print_type_param p)
  | Type.Prim t ->
    print "(%s)" (Type.prim_to_string t)
  | Type.Tuple tys ->
    print ~at_level:1 "(%t)" (Print.sequence "*" print_type tys)
  | Type.Arrow (ty, drty) ->
    print ~at_level:2 "(%t -> %t)" (print_type ~max_level:1 ty) (print_dirty_type drty)
  | Type.Handler (drty1, drty2) ->
    print ~at_level:2 "(%t -> %t)" (print_dirty_type drty1) (print_dirty_type drty2)

and print_dirty_type (ty, _) ppf =
  Format.fprintf ppf "%t computation" (print_type ~max_level:0 ty)

and print_args (tys, _) ppf =
  match tys with
  | [] -> ()
  | _ -> Format.fprintf ppf "(%t)" (Print.sequence "," print_type tys)


(** TYPE DEFINITIONS *)

let rec print_params params ppf =
  match Params.project_ty_params params with
  | [] -> ()
  | tys -> Format.fprintf ppf "(%t)" (Print.sequence "," Params.print_type_param tys)

let print_tydef_body ty_def ppf =
  match ty_def with
  | Tctx.Record flds ->
    let print_field (fld, ty) ppf = Format.fprintf ppf "%s: %t" fld (print_type ty) in
    Format.fprintf ppf "{@[<hov>%t@]}" (Print.sequence "; " print_field flds)
  | Tctx.Sum variants ->
    let print_variant (lbl, ty) ppf =
      match ty with
      | None -> Format.fprintf ppf "%s" lbl
      | Some ty -> Format.fprintf ppf "%s of %t" lbl (print_type ~max_level:0 ty)
    in
    Format.fprintf ppf "@[<hov>%t@]" (Print.sequence "|" print_variant variants)
  | Tctx.Inline ty -> print_type ty ppf

let print_tydef (name, (params, body)) ppf =
  Format.fprintf ppf "%t %s = %t" (print_params params) name (print_tydef_body body)

let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs)


(** SYNTAX *)

let print_variable = Typed.Variable.print ~safe:true


let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.Typed.term with
  | Typed.PVar x ->
    print "%t" (print_variable x)
  | Typed.PAs (p, x) ->
    print "%t as %t" (print_pattern p) (print_variable x)
  | Typed.PConst c ->
    Const.print c ppf
  | Typed.PTuple lst ->
    Print.tuple print_pattern lst ppf
  | Typed.PRecord lst ->
    Print.record print_pattern lst ppf
  | Typed.PVariant (lbl, None) when lbl = OldUtils.nil ->
    print "[]"
  | Typed.PVariant (lbl, None) ->
    print "%s" lbl
  | Typed.PVariant ("(::)", Some ({ Typed.term = Typed.PTuple [p1; p2] })) ->
    print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | Typed.PVariant (lbl, Some p) ->
    print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | Typed.PNonbinding ->
    print "_"


let compiled_filename fn = fn ^ ".ml"

let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs)
