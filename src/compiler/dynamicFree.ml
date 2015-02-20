type variable = string
type term = plain_term Common.pos
and plain_term =
  | Apply of term * term
  | Value of term
  | Match of term * abstraction list
  | New
  | Handle of term * term
  | Let of (variable Pattern.t * term) list * term
  | LetRec of (variable * abstraction) list * term
  | Var of variable
  | Const of Common.const
  | Tuple of term list
  | Record of (Common.field, term) Common.assoc
  | Variant of Common.label * term option
  | Lambda of abstraction
  | Operation of operation
  | Handler of handler
  | Check of term
and abstraction =
  variable Pattern.t * term
and abstraction2 =
  variable Pattern.t * variable Pattern.t * term
and operation =
  term * Common.opsym
and handler = {
  operations : (operation, abstraction2) Common.assoc;
  value : abstraction;
  finally : abstraction;
}

let _ = Header.run

let rec compile_expression (e, pos) =
  let e' = match e with
  | Syntax.Var x ->
      Var (compile_variable x)
  | Syntax.Const c ->
      Const c
  | Syntax.Tuple lst ->
      Tuple (List.map compile_expression lst)
  | Syntax.Record lst ->
      Record (Common.assoc_map compile_expression lst)
  | Syntax.Variant (lbl, e) ->
      Variant (lbl, Common.option_map compile_expression e)
  | Syntax.Lambda a ->
      Lambda (compile_abstraction a)
  | Syntax.Handler h  ->
      Handler (compile_handler h)
  | Syntax.Operation op ->
      Operation (compile_operation op)
  in (e', pos)
and compile_computation (c, pos) =
  let c' = match c with
  | Syntax.Apply (e1, e2) ->
      Apply (compile_expression e1, compile_expression e2)
  | Syntax.Value e ->
      Value (compile_expression e)
  | Syntax.Match (e, lst) ->
      Match (compile_expression e, List.map compile_abstraction lst)
  | Syntax.While _ ->
      Error.runtime "Compiling of while loops not implemented" 
  | Syntax.For _ ->
      Error.runtime "Compiling of for loops not implemented"
  | Syntax.New _ ->
      New
  | Syntax.Handle (e, c) ->
      Handle (compile_expression e, compile_computation c)
  | Syntax.Let (lst, c) ->
      Let (compile_let lst, compile_computation c)
  | Syntax.LetRec (lst, c) ->
      LetRec (compile_letrec lst, compile_computation c)
  | Syntax.Check c ->
      Check (compile_computation c)
  in (c', pos)
and compile_variable (n, x) = (x ^ string_of_int n)
and compile_pattern p = Pattern.map compile_variable p
and compile_abstraction (p, c) = (compile_pattern p, compile_computation c)
and compile_abstraction2 (p1, p2, c) =
  (compile_pattern p1, compile_pattern p2, compile_computation c)
and compile_operation (e, op) = (compile_expression e, op)
and compile_handler h = {
  operations =
    List.map (fun (op, a2) -> (compile_operation op, compile_abstraction2 a2)) h.operations;
  value = compile_abstraction h.value;
  finally = compile_abstraction h.finally;
}
and compile_let lst =
  List.map (fun (p, c) -> (compile_pattern p, compile_computation c)) lst
and compile_letrec lst =
  List.map (fun (x, a) -> (compile_variable x, compile_abstraction a)) lst


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
      print "(%t) :: (%t)" (print_pattern v1) (print_pattern v2)
  | Pattern.Variant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_pattern p)
  | Pattern.Nonbinding -> print "_"

let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match fst c with
  | Syntax.Apply (e1, e2) -> print ~at_level:1 "%t %t" (print_expression e1) (print_expression ~max_level:0 e2)
  | Syntax.Value e -> print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Syntax.Match (e, lst) -> print "match %t with @[<hov>%t@]" (print_expression e) (Print.sequence "\n" case lst)
  | Syntax.While (c1, c2) -> Error.runtime "Compiling of while loops not implemented"
  | Syntax.For (i, e1, e2, c, d) -> Error.runtime "Compiling of for loops not implemented"
  | Syntax.New (eff, _) -> print "value (new_instance ())"
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
  | Syntax.Var x -> print "(%t)" (Print.variable x)
  | Syntax.Const c -> print "%t" (Common.print_const c)
  | Syntax.Tuple lst -> Print.tuple print_expression lst ppf
  | Syntax.Record lst -> Print.record print_expression lst ppf
  | Syntax.Variant (lbl, None) -> print "%s" lbl
  | Syntax.Variant (lbl, Some e) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Syntax.Lambda a -> print ~at_level:3 "fun %t" (abstraction a)
  | Syntax.Handler h  -> print "%t" (handler h)
  | Syntax.Operation op -> print "apply_operation %t" (operation op)

and operation (e, op) ppf =
  Print.print ppf "(\"%s\", %t)" op (print_expression e)

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (Print.variable x) (abstraction a)

and case a ppf =
  Format.fprintf ppf "| %t" (abstraction a)

and handler h ppf =
  Format.fprintf ppf "{ value = (fun %t); finally = (fun %t); operation_cases = (%t)}"
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

let compile_with_header c =
  let ic = open_in "src/compiler/header.ml" in
  let n = in_channel_length ic in
  let header = Bytes.create n in
  really_input ic header 0 n;
  close_in ic;
  header ^ "\n\n\nlet _ = (" ^ compile c ^ ")"

let builtin = [
  ("=", (-1, "="));
  ("+", (-2, "+"));
  ("&&", (-3, "&&"));
  ("<>", (-4, "<>"));
  ("-", (-5, "-"));
  ("abs", (-6, "abs"));
  ("raise", (-7, "raise"));
  ("<", (-8, "<"));
]
