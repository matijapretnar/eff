let rec print_pattern ?max_level (p,_) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | Pattern.Var x -> print "(%t)" (Print.variable x)
  | Pattern.As (p, x) -> print ~at_level:2 "%t as %t" (print_pattern p) (Print.variable x)
  | Pattern.Const c -> Common.print_const c ppf
  | Pattern.Tuple lst -> Print.tuple print_pattern lst ppf
  | Pattern.Record lst -> Print.record print_pattern lst ppf
  | Pattern.Variant (lbl, None) when lbl = Common.nil -> print "[]"
  | Pattern.Variant (lbl, None) -> print "%s" lbl
  | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_pattern v1) (pattern_list v2)
  | Pattern.Variant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_pattern p)
  | Pattern.Nonbinding -> print "_"

and pattern_list ?(max_length=299) (p, pos) ppf =
  if max_length > 1 then
    match p with
    | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
        Format.fprintf ppf ",@ %t%t" (print_pattern v1) (pattern_list ~max_length:(max_length - 1) v2)
    | Pattern.Variant (lbl, None) when lbl = Common.nil -> ()
    | p -> Format.fprintf ppf "(??? %t ???)" (print_pattern (p, pos))
  else
    Format.fprintf ppf ",@ ..."

let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match fst c with
  | Syntax.Apply (e1, e2) -> print ~at_level:1 "%t %t" (print_expression e1) (print_expression ~max_level:0 e2)
  | Syntax.Value e -> print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Syntax.Match (e, lst) -> print "match %t with (@[<hov>%t@])" (print_expression e) (Print.sequence " | " case lst)
  | Syntax.While (c1, c2) -> Error.runtime "Compiling of while loops not implemented"
  | Syntax.For (i, e1, e2, c, d) -> Error.runtime "Compiling of for loops not implemented"
  | Syntax.New (eff, _) -> print "new_op %s" eff
  (* XXX Do compilation of resources *)
  | Syntax.Handle (e, c) -> print ~at_level:1 "handle (%t) (%t)" (print_expression e) (print_computation ~max_level:0 c)
  | Syntax.Let (lst, c) -> print "%t" (compile_let c lst)
  | Syntax.LetRec (lst, c) -> print "let rec @[<hov>%t@] in %t" (Print.sequence " and " let_rec_abstraction lst) (print_computation c)
  | Syntax.Check c -> print "()"

and compile_let c2 lst ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match lst with
  | [] -> print "%t" (print_computation c2)
  | (p, c1) :: lst -> print "((%t) >> (fun %t -> %t))" (print_computation c1) (print_pattern p) (compile_let c2 lst)

and print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match fst e with
  | Syntax.Var x -> print "%t" (Print.variable x)
  | Syntax.Const c -> print "%t" (Common.print_const c)
  | Syntax.Tuple lst -> Print.tuple print_expression lst ppf
  | Syntax.Record lst -> Print.record print_expression lst ppf
  | Syntax.Variant (lbl, None) -> print "%s" lbl
  | Syntax.Variant (lbl, Some e) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Syntax.Lambda a -> print "fun %t" (abstraction a)
  | Syntax.Handler h  -> print "%t" (handler h)
  | Syntax.Operation op -> print "%t" (operation op)

and operation (e, op) ppf =
  (* XXX Add instances! *)
  Print.print ppf "%s" op

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (Print.variable x) (abstraction a)

and case a ppf =
  Format.fprintf ppf "%t" (abstraction a)

and handler h ppf =
  Format.fprintf ppf "{ value = (%t); finally = (%t); operation_cases = (%t)}"
  (abstraction h.Syntax.value) (abstraction h.Syntax.finally) (operation_cases h.Syntax.operations)

and operation_cases cases ppf =
  match cases with
  | [] -> Format.fprintf ppf "Nil"
  | (op, (p, k, c)) :: cases ->
      Format.fprintf ppf
      "Cons (%t, (fun %t %t -> %t), %t)"
      (operation op) (print_pattern p) (print_pattern k) (print_computation c) (operation_cases cases)

let compile c =
  print_computation c Format.str_formatter;
  Format.flush_str_formatter ()
