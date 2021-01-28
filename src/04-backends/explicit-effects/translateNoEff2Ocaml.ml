open Utils
open SyntaxNoEff

let print = Format.fprintf

let rec pp_sequence sep pp xs ppf =
  match xs with
  | [] -> ()
  | [ x ] -> pp x ppf
  | x :: xs -> print ppf ("%t" ^^ sep ^^ "%t") (pp x) (pp_sequence sep pp xs)

let pp_tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp lst)

let pp_label label ppf = CoreTypes.Label.print label ppf

let pp_tyname ty_name ppf = CoreTypes.TyName.print ty_name ppf

let pp_typaram ty_param ppf =
  print ppf "'ty%t" (CoreTypes.TyParam.print ~safe:true ty_param)

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

let pp_variable var ppf =
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

let pp_field pp sep (field, value) ppf =
  print ppf "%t %s %t" (CoreTypes.Field.print field) sep (pp value)

let pp_record pp sep assoc ppf =
  let lst = Assoc.to_list assoc in
  print ppf "{@[<hov>%t@]}" (pp_sequence "; " (pp_field pp sep) lst)

let rec pp_type noeff_ty ppf =
  match noeff_ty with
  | NTyParam p -> print ppf "%t" (pp_typaram p)
  | NTyApply (tyName, []) -> print ppf "%t" (pp_tyname tyName)
  | NTyApply (tyName, tys) ->
      print ppf "(%t) %t" (Print.sequence ", " pp_type tys) (pp_tyname tyName)
  | NTyTuple [] -> print ppf "unit"
  | NTyTuple tys -> print ppf "@[<hov>(%t)@]" (Print.sequence " * " pp_type tys)
  | NTyBasic t -> print ppf "%t" (Const.print_ty t)
  | NTyArrow (ty1, ty2) ->
      print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
  | NTyHandler (ty1, ty2) ->
      print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
  | NTyQual (_tyc, ty) -> pp_type ty ppf
  | NTyComp ty -> print ppf "%t computation" (pp_type ty)

let rec pp_pattern pat ppf =
  match pat with
  | PNVar v -> print ppf "%t" (pp_variable v)
  | PNAs (p, v) -> print ppf "%t as %t" (pp_pattern p) (pp_variable v)
  | PNTuple pats -> print ppf "%t" (pp_tuple pp_pattern pats)
  | PNRecord rcd -> print ppf "%t" (pp_record pp_pattern "=" rcd)
  | PNVariant (l, None) -> print ppf "%t" (pp_label l)
  | PNVariant (l, Some p) ->
      print ppf "%t @[<hov>%t@]" (pp_label l) (pp_pattern p)
  | PNConst c -> print ppf "%t" (Const.print c)
  | PNNonbinding -> print ppf "_"

let pp_tuple pp tpl ppf =
  match tpl with
  | [] -> print ppf "()"
  | xs -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp xs)

let pp_effect (e, (_ty1, _ty2)) ppf = CoreTypes.Effect.print e ppf

let rec pp_coercion coer ppf =
  (* The cases not matched here should be handled in pp_term *)
  match coer with
  | NCoerVar v -> print ppf "%t" (Type.TyCoercionParam.print v)
  | NCoerRefl _ -> print ppf "coer_refl_ty"
  | NCoerArrow (w1, w2) ->
      print ppf "coer_arrow (%t) (%t)" (pp_coercion w1) (pp_coercion w2)
  | NCoerHandler (w1, w2) ->
      print ppf "coer_handler (%t) (%t)" (pp_coercion w1) (pp_coercion w2)
  | NCoerHandToFun (w1, w2) ->
      print ppf "coer_hand_to_fun (%t) (%t)" (pp_coercion w1) (pp_coercion w2)
  | NCoerFunToHand (w1, w2) ->
      print ppf "coer_fun_to_hand (%t) (%t)" (pp_coercion w1) (pp_coercion w2)
  | NCoerComp w -> print ppf "coer_computation (%t)" (pp_coercion w)
  | NCoerReturn w -> print ppf "coer_return (%t)" (pp_coercion w)
  | NCoerUnsafe w -> print ppf "coer_unsafe (%t)" (pp_coercion w)
  | NCoerTuple _cs -> print ppf "TupleCoercion"
  | NCoerApply (_t, _cs) -> print ppf "ApplyCoercion"
  | NCoerQual (_ct, _c) -> print ppf "ApplyCoercion"

let rec pp_term noEff_term ppf =
  match noEff_term with
  | NVar v -> print ppf "%t" (pp_variable v)
  | NConst c -> print ppf "%t" (Const.print c)
  | NTuple ts -> print ppf "%t" (pp_tuple pp_term ts)
  | NRecord rcd -> print ppf "%t" (pp_record pp_term "=" rcd)
  | NVariant (l, Some (NTuple [ hd; tl ])) when l = CoreTypes.cons ->
      print ppf "@[<hov>(%t::%t)@]" (pp_term hd) (pp_term tl)
  | NVariant (l, None) -> print ppf "(%t)" (pp_label l)
  | NVariant (l, Some t1) ->
      print ppf "(%t @[<hov>%t@])" (pp_label l) (pp_term t1)
  | NFun abs_ty -> print ppf "@[<hv 2>fun %t@]" (pp_abs_with_ty abs_ty)
  | NEffect (et, _) -> print ppf "(effect %t)" (CoreTypes.Effect.print et)
  | NApplyTerm (t1, t2) ->
      print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t1) (pp_term t2)
  | NCast (t, c) ->
      print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_coercion c) (pp_term t)
  | NReturn t -> print ppf "Value (%t)" (pp_term t)
  | NHandler { effect_clauses = eff_cls; return_clause = val_cl } ->
      print ppf
        "handler {@[<hov>value_clause = (fun %t);@] @[<hov>effect_clauses = \
         %t;@] }"
        (pp_abs_with_ty val_cl) (pp_effect_cls eff_cls)
  | NLet (t1, (pat, t2)) ->
      print ppf "@[<hv>@[<hv>let %t = %t in@] @,%t@]" (pp_pattern pat)
        (pp_term t1) (pp_term t2)
  | NLetRec (defs, t2) ->
      print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (pp_let_rec defs) (pp_term t2)
  | NMatch (t, []) ->
      print ppf "@[<hv>(match %t with@, _ -> assert false)@]" (pp_term t)
  | NMatch (t, cases) ->
      print ppf "@[<hv>(match %t with@, %t)@]" (pp_term t)
        (pp_sequence "@, | " pp_abs cases)
  | NCall (e, t, abs_ty) ->
      print ppf "@[<hov 2> call (%t) @,(%t) @,(fun %t)@]" (pp_effect e)
        (pp_term t) (pp_abs_with_ty abs_ty)
  | NOp (e, t) ->
      print ppf "@[<hov 2> call (%t) @,(%t) @,(%s)@]" (pp_effect e) (pp_term t)
        "(fun x -> x)"
  | NBind (t, abs) ->
      print ppf "@[<hov 2>((%t) >> (fun %t))@]" (pp_term t) (pp_abs abs)
  | NHandle (t1, t2) ->
      print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t2) (pp_term t1)
  | _ -> failwith __LOC__

and pp_abs (p, t) ppf = print ppf "@[<h> %t ->@ %t@]" (pp_pattern p) (pp_term t)

and pp_abs_with_ty (p, t) ppf =
  print ppf "@[<h>%t ->@ %t@]" (pp_pattern p) (pp_term t)

and pp_let_rec lst ppf =
  let pp_var_ty_abs (v, t) ppf =
    print ppf "@[<hv 2>and %t = @,%t@]" (pp_variable v) (pp_abs t)
  in
  match lst with
  | [] -> ()
  | (v, t) :: tl ->
      print ppf "@[<hv 2>let rec %t = @,%t@] @,%t" (pp_variable v) (pp_abs t)
        (pp_sequence " " pp_var_ty_abs tl)

and pp_effect_cls eff_cls ppf =
  let pp_effect_abs2 (eff, (pat1, pat2, t)) ppf =
    print ppf "@[<hv 2>| %t -> fun %t %t -> %t @]" (pp_effect eff)
      (pp_pattern pat1) (pp_pattern pat2) (pp_term t)
  in
  print ppf
    "@[<h>(fun (type a) (type b) (eff : (a, b) effect) : (a -> (b -> _) -> _) \
     -> \n\
    \  (match eff with\n\
    \    %t  \n\
    \    | eff' -> (fun arg k -> Call (eff', arg, k))\n\
    \      ))@]"
    (pp_sequence " " pp_effect_abs2 (Assoc.to_list eff_cls))

let pp_def_effect (eff, (ty1, ty2)) ppf =
  print ppf "@[type(_, _) effect += %t : (%t, %t) effect @]@.;;"
    (CoreTypes.Effect.print eff)
    (pp_type ty1) (pp_type ty2)

let pp_lets lst ppf =
  let pp_one_let (p, ty, t) ppf =
    print ppf "@[<hv 2>and (%t : %t) = @,%t@]" (pp_pattern p) (pp_type ty)
      (pp_term t)
  in
  match lst with
  | [] -> ()
  | (p, ty, t) :: tl ->
      print ppf "@[<hv 2>let rec (%t : %t) = @,%t@] @,%t" (pp_pattern p)
        (pp_type ty) (pp_term t)
        (pp_sequence " " pp_one_let tl)

let pp_external name symbol_name ppf =
  print ppf "let %t = ( %s )@." (pp_variable name) symbol_name

let pp_tydef (name, (params, tydef)) ppf =
  let pp_def tydef ppf =
    match tydef with
    | TyDefRecord assoc -> print ppf "%t" (pp_record pp_type ":" assoc)
    | TyDefSum assoc ->
        let lst = Assoc.to_list assoc in
        let print_cons ty_opt ppf =
          match ty_opt with
          | lbl, None -> print ppf "%t" (CoreTypes.Label.print lbl)
          | lbl, Some ty ->
              print ppf "%t of %t" (CoreTypes.Label.print lbl) (pp_type ty)
        in
        print ppf "@[<hov>%t@]" (pp_sequence "@, | " print_cons lst)
    | TyDefInline ty -> print ppf "%t" (pp_type ty)
  in
  match params with
  | [] ->
      print ppf "@[type %t = %t@]@."
        (CoreTypes.TyName.print name)
        (pp_def tydef)
  | _lst ->
      print ppf "@[type (%t) %t = %t@]@."
        (pp_sequence ", " CoreTypes.TyParam.print params)
        (CoreTypes.TyName.print name)
        (pp_def tydef)

let pp_cmd cmd ppf =
  match cmd with
  | Term t -> print ppf "%t@." (pp_term t) (* TODO check if ok *)
  | DefEffect e -> pp_def_effect e ppf
  | TopLet (x, t) -> print ppf "let %t = %t@." (pp_variable x) (pp_term t)
  | TopLetRec (x, (p, t)) ->
      print ppf "let rec %t %t = %t@." (pp_variable x) (pp_pattern p)
        (pp_term t)
  | External (x, _ty, f) -> pp_external x f ppf
  | TyDef defs -> print ppf "%t@." (pp_sequence "@, and " pp_tydef defs)
