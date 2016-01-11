let print_variable = Typed.Variable.print

let print_effect eff ppf = Print.print ppf "effect_%s" eff

let print_pattern p ppf = Untyped.print_pattern (p.Typed.term) ppf

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Typed.term with
  | Typed.Var x ->
      (* We add extra parentheses in case the variable is a symbol *)
      (* We add extra spaces in case the symbol is * *)
      print "( %t )" (print_variable x)
  | Typed.Const c ->
      print "%t" (Const.print c)
  | Typed.Tuple lst ->
      Print.tuple print_expression lst ppf
  | Typed.Record lst ->
      Print.record print_expression lst ppf
  | Typed.Variant (lbl, None) ->
      print "%s" lbl
  | Typed.Variant (lbl, Some e) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Typed.Lambda a ->
      print ~at_level:2 "fun %t" (print_abstraction a)
  | Typed.Handler h ->
      print "{ value_clause = fun %t; finally_clause = fun %t; effect_clauses = %t }"
      (print_abstraction h.Typed.value_clause) (print_abstraction h.Typed.finally_clause)
      (print_effect_clauses h.Typed.effect_clauses)
  | Typed.Effect eff ->
      print ~at_level:2 "fun param -> call %t param (fun result -> value result)" (print_effect eff)
  | Typed.PureLambda pa ->
      print ~at_level:2 "(* pure *) fun %t" (print_pure_abstraction pa)
  | Typed.PureApply (e1, e2) ->
      print ~at_level:1 "(* pure *) %t %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Typed.PureLetIn (e1, pa) ->
      let (p, e2) = pa.Typed.term in
      print ~at_level:2 "(* pure *) let %t = %t in@ %t" (print_pattern p) (print_expression e1) (print_expression e2)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
      print ~at_level:1 "%t %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Typed.Value e ->
      print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Typed.Match (e, lst) ->
      print ~at_level:2 "match %t with (@[<hov>%t@])" (print_expression e) (Print.sequence " | " print_abstraction lst)
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
      print ~at_level:1 "call %t %t (fun %t)"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Typed.Bind (c1, a) ->
      print ~at_level:2 "%t >> fun %t" (print_computation ~max_level:0 c1) (print_abstraction a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
      print ~at_level:2 "let %t = %t in@ %t" (print_pattern p) (print_expression e) (print_computation c)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
      print "Nil"
  | (eff, {Typed.term = (p1, p2, c)}) :: cases ->
      print ~at_level:1 "Cons %t %t %t %t"
      (print_effect eff) (print_pattern p1) (print_pattern p2) (print_computation c)

and print_abstraction {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and print_pure_abstraction {Typed.term = (p, e)} ppf =
  Format.fprintf ppf "%t -> (* pure *) %t" (print_pattern p) (print_expression e)

and print_multiple_bind (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation c')
  | (p, c) :: lst ->
      Format.fprintf ppf "%t >> fun %t -> %t"
      (print_computation c) (print_pattern p) (print_multiple_bind (lst, c'))

and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_top_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a)

let rec print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Type.Apply (ty_name, args) ->
      print ~at_level:1 "%s %t" ty_name (print_args args)
  | Type.Param (Type.Ty_Param n) ->
      print "'t%d" n
  | Type.Basic t ->
      print "%s" t
  | Type.Tuple tys ->
      print "%t" (Print.tuple print_type tys)
  | Type.Arrow (ty, drty) ->
      print ~at_level:2 "%t -> %t" (print_type ~max_level:1 ty) (print_dirty_type drty)
  | Type.PureArrow(ty1,ty2) ->
      print ~at_level:2 "%t -> %t" (print_type ~max_level:1 ty1) (print_type ty2)
  | Type.Handler ((ty1, _), (ty2, _)) ->
      print ~at_level:2 "(%t, %t) handler" (print_type ty1) (print_type ty2)

and print_dirty_type (ty, _) ppf =
  print_type ty ppf

and print_args (tys, _, _) ppf =
  Print.sequence " " print_type tys ppf

let compiled_filename fn = fn ^ ".ml"

let print_command (cmd, _) ppf =
  match cmd with
  | Typed.DefEffect (eff, (ty1, ty2)) ->
      Print.print ppf "let %t : (%t, %t) effect = \"%t\"" (print_effect eff) (print_type ty1) (print_type ty2) (print_effect eff)
  | Typed.Computation c ->
      print_computation c ppf
  | Typed.TopLet (defs, _) ->
      Print.print ppf "let %t" (Print.sequence "\nand\n" print_top_let_abstraction defs)
  | Typed.TopLetRec (defs, _) ->
      Print.print ppf "let rec %t" (Print.sequence "\nand\n" print_let_rec_abstraction defs)
  | Typed.Use fn ->
      Print.print ppf "#use %S" (compiled_filename fn)
  | Typed.External _ ->
      Print.print ppf "(* external definition not yet implemented *)"
  | Typed.Tydef _ ->
      Print.print ppf "(* type definition not yet implemented *)"
  | Typed.Reset ->
      Print.print ppf "(* #reset directive not supported by OCaml *)"
  | Typed.Quit ->
      Print.print ppf "(* #quit directive not supported by OCaml *)"
  | Typed.TypeOf _ ->
      Print.print ppf "(* #type directive not supported by OCaml *)"
  | Typed.Help ->
      Print.print ppf "(* #help directive not supported by OCaml *)"

let print_commands cmds ppf =
  Print.sequence ";;" print_command cmds ppf
