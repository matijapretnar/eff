type variable = string
type term = plain_term Common.pos
and plain_term =
  | Apply of term * term
  | Value of term
  | Match of term * abstraction list
  | New
  | Handle of term * term
  | Let of variable Pattern.t * term * term
  | Bind of variable Pattern.t * term * term
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


let rec optimize ((t, pos) : term) : term =
  let t' = match t with
  | Apply (e1, e2) -> Apply (optimize e1, optimize e2)
  | Value e -> Value (optimize e)
  | Match (e, lst) -> Match (optimize e, List.map optimize_abstraction lst)
  | New -> New
  | Handle (e, c) -> Handle (optimize e, optimize c)
  | Let (p, c1, c2) -> Let (p, optimize c1, optimize c2)
  | Bind (p, c1, c2) -> Bind (p, optimize c1, optimize c2)
  | LetRec (lst, c) -> LetRec (optimize_let_rec lst, optimize c)
  | Check c -> Check (optimize c)
  | Var x -> Var x
  | Const c -> Const c
  | Tuple lst -> Tuple (List.map optimize lst)
  | Record lst -> Record (Common.assoc_map optimize lst)
  | Variant (lbl, e) -> Variant (lbl, Common.option_map optimize e)
  | Lambda a -> Lambda (optimize_abstraction a)
  | Handler h -> Handler (optimize_handler h)
  | Operation op -> Operation op
  in
  (t', pos)
and optimize_abstraction (p, c) = (p, optimize c)
and optimize_abstraction2 (p1, p2, c) = (p1, p2, optimize c)
and optimize_let_rec lst = Common.assoc_map optimize_abstraction lst
and optimize_handler h = {
  value = optimize_abstraction h.value;
  finally = optimize_abstraction h.finally;
  operations = Common.assoc_map optimize_abstraction2 h.operations;
}

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
      compile_let c lst
  | Syntax.LetRec (lst, c) ->
      LetRec (compile_letrec lst, compile_computation c)
  | Syntax.Check c ->
      Check (compile_computation c)
  in (c', pos)
and compile_variable (n, x) = x
and compile_pattern p = Pattern.map compile_variable p
and compile_abstraction (p, c) = (compile_pattern p, compile_computation c)
and compile_abstraction2 (p1, p2, c) =
  (compile_pattern p1, compile_pattern p2, compile_computation c)
and compile_operation (e, op) = (compile_expression e, op)
and compile_handler h = {
  operations =
    List.map (fun (op, a2) -> (compile_operation op, compile_abstraction2 a2)) h.Syntax.operations;
  value = compile_abstraction h.Syntax.value;
  finally = compile_abstraction h.Syntax.finally;
}
and compile_let c = function
  | [] -> fst (compile_computation c)
  | (p, c') :: lst ->
      Bind (compile_pattern p, compile_computation c', (compile_let c lst, snd c))
and compile_letrec lst =
  List.map (fun (x, a) -> (compile_variable x, compile_abstraction a)) lst


let rec print_pattern ?max_level (p,_) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | Pattern.Var x -> print "(%s)" x
  | Pattern.As (p, x) -> print ~at_level:2 "%t as %s" (print_pattern p) x
  | Pattern.Const c -> Common.print_const c ppf
  | Pattern.Tuple lst -> Print.tuple print_pattern lst ppf
  | Pattern.Record lst -> Print.record print_pattern lst ppf
  (* | Pattern.Variant (lbl, None) when lbl = Common.nil -> print "[]" *)
  | Pattern.Variant (lbl, None) -> print "%s" lbl
(*   | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
      print "(%t) :: (%t)" (print_pattern v1) (print_pattern v2)
 *)
  | Pattern.Variant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_pattern p)
  | Pattern.Nonbinding -> print "_"

let rec print_term ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match fst c with
  | Apply (e1, e2) -> print ~at_level:1 "%t %t" (print_term e1) (print_term ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value %t" (print_term ~max_level:0 e)
  | Match (e, lst) -> print "match %t with @[<hov>%t@]" (print_term e) (Print.sequence "\n" case lst)
  | New -> print "value (new_instance ())"
  | Handle (e, c) -> print ~at_level:1 "handle (%t) (%t)" (print_term e) (print_term ~max_level:0 c)
  | Let (p, c1, c2) -> print "let %t = %t in (%t)" (print_term c1) (print_pattern p) (print_term c2)
  | Bind (p, c1, c2) -> print "(%t) >> (fun %t -> %t)" (print_term c1) (print_pattern p) (print_term c2)
  | LetRec (lst, c) -> print "let rec @[<hov>%t@] in %t" (Print.sequence " and " let_rec_abstraction lst) (print_term c)
  | Check c -> print "()"
  | Var x -> print "(%s)" x
  | Const c -> print "%t" (Common.print_const c)
  | Tuple lst -> Print.tuple print_term lst ppf
  | Record lst -> Print.record print_term lst ppf
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some e) -> print ~at_level:1 "%s @[<hov>%t@]" lbl (print_term e)
  | Lambda a -> print ~at_level:3 "fun %t" (abstraction a)
  | Handler h -> print "%t" (handler h)
  | Operation op -> print "apply_operation %t" (operation op)

and print_let c2 lst ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match lst with
  | [] -> print "%t" (print_term c2)
  | (p, c1) :: lst -> print "((%t) >> (fun %t -> %t))" (print_term c1) (print_pattern p) (print_let c2 lst)

and operation (e, op) ppf =
  Print.print ppf "(\"%s\", %t)" op (print_term e)

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_term c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_term c)

and let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%s = fun %t" x (abstraction a)

and case a ppf =
  Format.fprintf ppf "| %t" (abstraction a)

and handler h ppf =
  Format.fprintf ppf "{ value = (fun %t); finally = (fun %t); operation_cases = (%t)}"
  (abstraction h.value) (abstraction h.finally) (operation_cases h.operations)

and operation_cases cases ppf =
  match cases with
  | [] -> Format.fprintf ppf "Nil"
  | (op, (p, k, c)) :: cases ->
      Format.fprintf ppf
      "Cons (%t, (fun %t %t -> %t), %t)"
      (operation op) (print_pattern p) (print_pattern k) (print_term c) (operation_cases cases)

let compile c =
  let c' = compile_computation c in
  print_term c' Format.str_formatter;
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
