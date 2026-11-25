open Language

(* A variable gets its number, so that two variables with the same name
   never capture each other, and no name is an OCaml keyword. *)
let print_variable var ppf =
  let printer desc n =
    match desc.[0] with
    | 'a' .. 'z' | '_' -> Format.fprintf ppf "_%s_%d" desc n
    | '$' -> (
        match desc with
        | "$c_thunk" -> Format.fprintf ppf "_comp_%d" n
        | "$id_par" -> Format.fprintf ppf "_id_%d" n
        | "$anon" -> Format.fprintf ppf "_anon_%d" n
        | "$bind" -> Format.fprintf ppf "_b_%d" n
        | _ -> Format.fprintf ppf "_x_%d" n)
    | _ -> Format.fprintf ppf "_op_%d (* %s *)" n desc
  in
  Term.Variable.fold printer var

(* The name of a top-level variable as other OCaml code refers to it, if it
   has one *)
let source_name var =
  Term.Variable.fold
    (fun desc _ ->
      match desc.[0] with 'a' .. 'z' | '_' -> Some desc | _ -> None)
    var

let print_effect eff ppf = Effect.print eff ppf
let print_label lbl ppf = Type.Label.print lbl ppf
let print_field fld ppf = Type.Field.print fld ppf

let print_tyname tyname ppf =
  let printer desc _n = Format.fprintf ppf "%s" desc in
  TyName.fold printer tyname

let print_typaram typaram ppf =
  let printer _desc n = Format.fprintf ppf "'ty_%d" n in
  Type.TyParam.fold printer typaram
