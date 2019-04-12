let protected =
  [ "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done"
  ; "downto"; "else"; "end"; "exception"; "external"; "false"; "for"; "fun"
  ; "function"; "functor"; "if"; "in"; "include"; "inherit"; "initializer"
  ; "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match"; "method"
  ; "mod"; "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or"
  ; "private"; "rec"; "sig"; "struct"; "then"; "to"; "true"; "try"; "type"
  ; "val"; "virtual"; "when"; "while"; "with"; "continue" ]

let print_variable ?(warnings = None) var ppf =
  let printer desc n =
    (* [mod] has privileges because otherwise it's stupid *)
    if desc = "mod" then Format.fprintf ppf "_op_%d (* %s *)" n desc else
    let () =
      match warnings with
      | None -> ()
      | Some warning_ppf -> 
          if List.mem desc protected then
            Format.fprintf warning_ppf
             ("Warning: Protected keyword [%s]. Must be fixed by hand!@.")
             desc
          else ()
    in
    match desc.[0] with
    | 'a' .. 'z' | '_' -> Format.fprintf ppf "%s" desc
    | '$' -> (
        match desc with
        | "$c_thunk" -> Format.fprintf ppf "_comp_%d" n
        | "$id_par" -> Format.fprintf ppf "_id_%d" n
        | "$anon" -> Format.fprintf ppf "_anon_%d" n
        | "$bind" -> Format.fprintf ppf "_b_%d" n
        | _ -> Format.fprintf ppf "_x_%d" n )
    | _ -> Format.fprintf ppf "_op_%d (* %s *)" n desc
  in
  CoreTypes.Variable.fold printer var

let print_effect eff ppf = CoreTypes.Effect.print eff ppf

let print_label lbl ppf = CoreTypes.Label.print lbl ppf

let print_field fld ppf = CoreTypes.Field.print fld ppf

let print_tyname ?(warnings = None) tyname ppf = 
  let printer desc n =
    match warnings, desc with
      | Some warning_ppf, "empty" -> 
          Format.fprintf warning_ppf
           ("Warning: [empty] type encountered. Must be fixed by hand!@.") ;
          Format.fprintf ppf "%s" desc
      | _ -> Format.fprintf ppf "%s" desc
  in
  CoreTypes.TyName.fold printer tyname

let print_typaram typaram ppf = 
  let printer desc n = Format.fprintf ppf "'ty_%d" n in
  CoreTypes.TyParam.fold printer typaram
