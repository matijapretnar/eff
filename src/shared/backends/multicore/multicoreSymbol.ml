let protected =
  [ "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done" ]
  @ [ "downto"; "else"; "end"; "exception"; "external"; "false"; "for"; "fun" ]
  @ [ "function"; "functor"; "if"; "in"; "include"; "inherit"; "initializer" ]
  @ [ "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match"; "method" ]
  @ [
      "mod"; "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or";
    ]
  @ [ "private"; "rec"; "sig"; "struct"; "then"; "to"; "true"; "try"; "type" ]
  @ [ "val"; "virtual"; "when"; "while"; "with"; "continue" ]

let print_variable var ppf =
  let printer desc n =
    (* [mod] has privileges because otherwise it's stupid *)
    if desc = "mod" then Format.fprintf ppf "_op_%d (* %s *)" n desc
    else (
      if List.mem desc protected then
        Print.warning
          "Warning: Protected keyword [%s]. Must be fixed by hand!@." desc;
      match desc.[0] with
      | 'a' .. 'z' | '_' -> Format.fprintf ppf "%s" desc
      | '$' -> (
          match desc with
          | "$c_thunk" -> Format.fprintf ppf "_comp_%d" n
          | "$id_par" -> Format.fprintf ppf "_id_%d" n
          | "$anon" -> Format.fprintf ppf "_anon_%d" n
          | "$bind" -> Format.fprintf ppf "_b_%d" n
          | _ -> Format.fprintf ppf "_x_%d" n)
      | _ -> Format.fprintf ppf "_op_%d (* %s *)" n desc)
  in
  CoreTypes.Variable.fold printer var

let print_effect eff ppf = CoreTypes.Effect.print eff ppf

let print_label lbl ppf = CoreTypes.Label.print lbl ppf

let print_field fld ppf = CoreTypes.Field.print fld ppf

let print_tyname tyname ppf =
  let printer desc _n =
    if desc = "empty" then
      Print.warning
        "Warning: [empty] type encountered. Must be fixed by hand!@.";
    Format.fprintf ppf "%s" desc
  in
  CoreTypes.TyName.fold printer tyname

let print_typaram typaram ppf =
  let printer _desc n = Format.fprintf ppf "'ty_%d" n in
  CoreTypes.TyParam.fold printer typaram
