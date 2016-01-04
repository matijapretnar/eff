let print_variable = Typed.Variable.print

let print_effect eff ppf = Print.print ppf "%s" eff

let print_pattern p ppf = Untyped.print_pattern (p.Typed.term) ppf

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Typed.term with
  | Typed.Var x ->
      print "%t" (print_variable x)
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
      print ~at_level:2 "fun param -> apply_effect %t param (fun result -> value result)" (print_effect eff)
  | Typed.PureLambda pa ->
      print ~at_level:2 "(* pure *) fun %t" (print_pure_abstraction pa)
  | Typed.PureApply (e1, e2) ->
      print ~at_level:1 "(* pure *) %t %t" (print_expression e1) (print_expression ~max_level:0 e2)
  | Typed.PureLetIn (e1, pa) ->
      let (p, e2) = pa.Typed.term in
      print ~at_level:2 "(* pure *) let %t = %t in@ %t" (print_pattern p) (print_expression e1) (print_expression e2)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
      print ~at_level:1 "%t %t" (print_expression e1) (print_expression ~max_level:0 e2)
  | Typed.Value e ->
      print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Typed.Match (e, lst) ->
      print "match %t with (@[<hov>%t@])" (print_expression e) (Print.sequence " | " print_abstraction lst)
  | Typed.While (c1, c2) ->
      print "while %t do %t done" (print_computation c1) (print_computation c2)
  | Typed.For (i, e1, e2, c, up) ->
      let direction = if up then "to" else "downto" in
      print "for %t = %t %s %t do %t done"
      (print_variable i) (print_expression e1) direction (print_expression e2) (print_computation c)
  | Typed.Handle (e, c) ->
      print "handle %t %t" (print_expression e) (print_computation c)
  | Typed.Let (lst, c) ->
      print "let @[<hov>%t@] in %t"
      (Print.sequence " | " print_let_abstraction lst) (print_computation c)
  | Typed.LetRec (lst, c) ->
      print "let rec ... in %t" (print_computation c)
  | Typed.Check c ->
      print "check %t" (print_computation c)
  | Typed.Call (eff, e, a) ->
      print "apply_effect %t %t (fun %t)"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Typed.Bind (c1, a) ->
      print ~at_level:2 "%t >> fun %t" (print_computation c1) (print_abstraction a)
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

and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)
