let print_variable = Typed.Variable.print

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.Typed.term with
  | Typed.PVar x -> print "%t" (print_variable x)
  | Typed.PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | Typed.PConst c -> Const.print c ppf
  | Typed.PTuple lst -> Print.tuple print_pattern lst ppf
  | Typed.PRecord lst -> Print.record print_pattern lst ppf
  | Typed.PVariant (lbl, None) when lbl = Common.nil -> print "[]"
  | Typed.PVariant (lbl, None) -> print "%s" lbl
  | Typed.PVariant ("(::)", Some ({ Typed.term = Typed.PTuple [p1; p2] })) ->
      print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | Typed.PVariant (lbl, Some p) ->
      print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | Typed.PNonbinding -> print "_"

let print_type_param (Type.Ty_Param n) ppf =
   Format.fprintf ppf "'t%d" n

let rec print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Type.Apply ("empty", _) ->
      print "unit"
  | Type.Apply (ty_name, args) ->
      print ~at_level:1 "%t %s" (print_args args) ty_name
  | Type.Param p ->
      print "%t" (print_type_param p)
  | Type.Basic t ->
      print "%s" t
  | Type.Tuple tys ->
      print ~at_level:1 "%t" (Print.sequence "*" print_type tys)
  | Type.Arrow (ty1, (ty2, _)) ->
      print ~at_level:2 "(%t, %t) abstraction" (print_type ty1) (print_type ty2)
  | Type.Handler ((ty1, _), (ty2, _)) ->
      print ~at_level:2 "(%t, %t) handler" (print_type ty1) (print_type ty2)

and print_dirty_type (ty, _) ppf =
  Format.fprintf ppf "%t computation" (print_type ~max_level:0 ty)

and print_args (tys, _, _) ppf =
  match tys with
  | [] -> ()
  | _ -> Format.fprintf ppf "(%t)" (Print.sequence "," print_type tys)

and print_params (tys, _, _) ppf =
  match tys with
  | [] -> ()
  | _ -> Format.fprintf ppf "(%t)" (Print.sequence "," print_type_param tys)


let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Typed.term with
  | Typed.Var x ->
      print "%t" (print_variable x)
  | Typed.BuiltIn s ->
      print "%s" s
  | Typed.Const c ->
      print "%t" (Const.print c)
  | Typed.Tuple lst ->
      Print.tuple print_expression lst ppf
  | Typed.Record lst ->
      Print.record print_expression lst ppf
  | Typed.Variant (lbl, None) ->
      print "%s" lbl
  | Typed.Variant (lbl, Some e) ->
      print ~at_level:1 "%s %t" lbl (print_expression e)
  | Typed.Lambda a ->
      print ~at_level:2 "%t" (print_both_abstractions a)
  | Typed.Handler h ->
      print "{@[<hov>
        value_clause = %t;
        finally_clause = %t;
        pure_effect_clauses = ((
                  fun (type a) (type b) (x : (a, b) effect) -> (
                    (match x with %t)
                    :
                    a -> (b, _) abstraction -> _
                  )
                ));
        impure_effect_clauses = ((
                  fun (type a) (type b) (x : (a, b) effect) -> (
                    (match x with %t)
                    :
                    a -> (b, _) abstraction -> _ computation
                  )
                )) @]}"
      (print_both_abstractions h.Typed.value_clause)
      (print_both_abstractions h.Typed.finally_clause)
      (print_pure_effect_clauses h.Typed.effect_clauses)
      (print_effect_clauses h.Typed.effect_clauses)
  | Typed.Effect eff ->
      print ~at_level:2 "effect %t" (print_effect eff)
  | Typed.Pure c ->
      print ~at_level:1 "%t" (print_pure_computation ~max_level:0 c)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply ({Typed.term = Typed.Lambda a}, e2) ->
      print ~at_level:1 "(fun %t)@ %t" (print_abstraction a) (print_expression ~max_level:0 e2)
  | Typed.Apply (e1, e2) ->
      print ~at_level:1 "(%t).impure@ %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Typed.Value e ->
      print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Typed.Match (e, []) ->
      print ~at_level:2 "(match %t with _ -> assert false)" (print_expression e)
  | Typed.Match (e, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e) (Print.cases print_abstraction lst)
  | Typed.While (c1, c2) ->
      print ~at_level:2 "while %t do %t done" (print_computation c1) (print_computation c2)
  | Typed.For (i, e1, e2, c, up) ->
      let direction = if up then "to" else "downto" in
      print ~at_level:2 "for %t = %t %s %t do %t done"
      (print_variable i) (print_expression e1) direction (print_expression e2) (print_computation c)
  | Typed.Handle (e, c) ->
      print ~at_level:1 "handle %t %t" (print_expression ~max_level:0 e) (print_computation ~max_level:0 c)
  | Typed.Let (lst, c) ->
      print ~at_level:2 "%t" (print_multiple_bind (lst, c))
  | Typed.LetRec (lst, c) ->
      print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Typed.Check c' ->
      print ~at_level:1 "check %S %t" (Common.to_string Location.print c.Typed.location) (print_computation ~max_level:0 c')
  | Typed.Call (eff, e, a) ->
      print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Typed.Bind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]" (print_computation ~max_level:0 c1) (print_abstraction a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t" (print_pattern p) (print_expression e) (print_computation c)

and print_pure_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply ({Typed.term = Typed.Lambda a}, e2) ->
      print ~at_level:1 "(fun %t)@ %t" (print_pure_abstraction a) (print_expression ~max_level:0 e2)
  | Typed.Apply (e1, e2) ->
      print ~at_level:1 "(%t).pure@ %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Typed.Value e ->
      print ~at_level:1 "%t" (print_expression ~max_level:0 e)
  | Typed.Match (e, []) ->
      print ~at_level:2 "(match %t with _ -> assert false)" (print_expression e)
  | Typed.Match (e, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e) (Print.cases print_pure_abstraction lst)
(*   | Typed.While (c1, c2) ->
      print ~at_level:2 "while %t do %t done" (print_computation c1) (print_computation c2) *)
(*   | Typed.For (i, e1, e2, c, up) ->
      let direction = if up then "to" else "downto" in
      print ~at_level:2 "for %t = %t %s %t do %t done"
      (print_variable i) (print_expression e1) direction (print_expression e2) (print_computation c) *)
  | Typed.Handle (e, c) ->
      print ~at_level:1 "pure_handle %t %t" (print_expression ~max_level:0 e) (print_computation ~max_level:0 c)
  | Typed.Let (lst, c) ->
      print ~at_level:2 "%t" (print_pure_multiple_bind (lst, c))
  | Typed.LetRec (lst, c) ->
      print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_pure_computation c)
(*   | Typed.Check c' ->
      print ~at_level:1 "check %S %t" (Common.to_string Location.print c.Typed.location) (print_computation ~max_level:0 c') *)
  | Typed.Call _ ->
      print ~at_level:1 "assert false"
  | Typed.Bind (c1, {Typed.term = (p, c2)}) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t@]" (print_pattern p) (print_pure_computation c1) (print_pure_computation c2)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t" (print_pattern p) (print_expression e) (print_pure_computation c)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
      print "| eff' -> fun arg k -> Call (eff', arg, k.impure)"
  | (((_, (t1, t2)) as eff), {Typed.term = (p1, p2, c)}) :: cases ->
      print ~at_level:1 "| %t -> (fun (%t : %t) (%t : (%t, _) abstraction) -> %t) %t"
      (print_effect eff) (print_pattern p1) (print_type t1) (print_pattern p2) (print_type t2) (print_computation c) (print_effect_clauses cases)

and print_pure_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
      print "| eff' -> fun arg k -> assert false"
  | (((_, (t1, t2)) as eff), {Typed.term = (p1, p2, c)}) :: cases ->
      print ~at_level:1 "| %t -> (fun (%t : %t) (%t : (%t, _) abstraction) -> %t) %t"
      (print_effect eff) (print_pattern p1) (print_type t1) (print_pattern p2) (print_type t2) (print_pure_computation c) (print_pure_effect_clauses cases)

and print_abstraction {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

and print_pure_abstraction {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_pure_computation c)

and print_multiple_bind (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation c')
  | (p, c) :: lst ->
      Format.fprintf ppf "%t >> fun %t -> %t"
      (print_computation c) (print_pattern p) (print_multiple_bind (lst, c'))

and print_pure_multiple_bind (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_pure_computation c')
  | (p, c) :: lst ->
      Format.fprintf ppf "let %t = %t in %t"
      (print_pattern p) (print_pure_computation c) (print_pure_multiple_bind (lst, c'))

and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_top_let_abstraction (p, c) ppf =
  match c.Typed.term with
  | Typed.Value e -> 
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ -> 
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_both_abstractions a ppf =
  Format.fprintf ppf "{ pure = (fun %t); impure = (fun %t) }"
    (print_pure_abstraction a) (print_abstraction a)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = %t" (print_variable x) (print_both_abstractions a)

let compiled_filename fn = fn ^ ".ml"

let print_tydef_body ty_def ppf =
  match ty_def with
  | Tctx.Record flds ->
      let field (fld, ty) ppf = Format.fprintf ppf "%s: %t" fld (print_type ty) in
      Format.fprintf ppf "{@[<hov>%t@]}" (Print.sequence "; " field flds)
  | Tctx.Sum variants ->
      let variant (lbl, ty) ppf =
        match ty with
        | None -> Format.fprintf ppf "%s" lbl
        | Some ty -> Format.fprintf ppf "%s of %t" lbl (print_type ~max_level:0 ty)
      in
      Format.fprintf ppf "@[<hov>%t@]" (Print.sequence "|" variant variants)
  | Tctx.Inline ty -> print_type ty ppf

let print_tydef (name, (params, body)) ppf =
  Format.fprintf ppf "%t %s = %t" (print_params params) name (print_tydef_body body)

let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs)

let print_command (cmd, _) ppf =
  match cmd with
  | Typed.DefEffect (eff, (ty1, ty2)) ->
      Print.print ppf "type (_, _) effect += %t : (%t, %t) effect" (print_effect eff) (print_type ty1) (print_type ty2)
  | Typed.Computation c ->
      print_computation c ppf
  | Typed.TopLet (defs, _) ->
      Print.print ppf "let %t" (Print.sequence "\nand\n" print_top_let_abstraction defs)
  | Typed.TopLetRec (defs, _) ->
      Print.print ppf "let rec %t" (Print.sequence "\nand\n" print_let_rec_abstraction defs)
  | Typed.Use fn ->
      Print.print ppf "#use %S" (compiled_filename fn)
  | Typed.External (x, ty, f) ->
      Print.print ppf "let %t : %t = ( %s )" (print_variable x) (print_type ty) f
  | Typed.Tydef tydefs ->
      print_tydefs tydefs ppf
  | Typed.Reset ->
      Print.print ppf "(* #reset directive not supported by OCaml *)"
  | Typed.Quit ->
      Print.print ppf "(* #quit directive not supported by OCaml *)"
  | Typed.TypeOf _ ->
      Print.print ppf "(* #type directive not supported by OCaml *)"
  | Typed.Help ->
      Print.print ppf "(* #help directive not supported by OCaml *)"

let print_commands cmds ppf =
  Print.sequence "\n\n;;\n\n" print_command cmds ppf
