open CommonPrint

let is_pure_function e =
  Scheme.is_pure_function_type ~loc:e.Typed.location e.Typed.scheme

let is_pure_abstraction {Typed.term = (_, c)} =
  Scheme.is_pure c.Typed.scheme

let is_pure_handler e =
  false

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Typed.term with
  | Typed.Var x ->
    print "%t" (print_variable x)
  | Typed.BuiltIn (s, _) ->
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
    print ~at_level:1 "(%s %t)" lbl (print_expression e)
  | Typed.Lambda a ->
    let pure = is_pure_function e in
    print ~at_level:2 "fun %t" (print_abstraction ~pure a)
  | Typed.Handler h ->
    let pure = is_pure_handler e in
    print "%t" (print_handler ~pure h)
  | Typed.Effect eff ->
    print ~at_level:2 "effect %t" (print_effect eff)
  | Typed.Pure c ->
    print_computation ?max_level ~pure:true c ppf

and print_function_argument ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  if is_pure_function e then
    print "(fun x -> value (%t x))" (print_expression ~max_level:1 e)
  else
    print_expression ~max_level:0 e ppf

and print_computation ?max_level ~pure c ppf =
  let is_pure_computation = Scheme.is_pure ~loc:c.Typed.location c.Typed.scheme in
  let expect_pure_computation = pure in
  match expect_pure_computation, is_pure_computation with
  | true, true ->
    print_computation' ?max_level ~pure:true c ppf
  | true, false ->
    Print.print ?max_level ppf "run %t" (print_computation' ~max_level:0 ~pure:false c)
  | false, true ->
    Print.print ?max_level ppf "value %t" (print_computation' ~max_level:0 ~pure:true c)
  | false, false ->
    print_computation' ?max_level ~pure:false c ppf
and print_computation' ?max_level ~pure c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
    print ~at_level:1 "%t@ %t"
      (print_expression ~max_level:1 e1)
      (print_function_argument ~max_level:0 e2)
  | Typed.Value e ->
    (* assert pure; *)
    print ~at_level:1 "%t" (print_expression ~max_level:0 e)
  | Typed.Match (e, []) ->
    print ~at_level:2 "(match %t with _ -> assert false)"
      (print_expression e)
  | Typed.Match (e, lst) ->
    print ~at_level:2 "(match %t with @[<v>| %t@])"
      (print_expression e)
      (Print.cases (print_abstraction ~pure) lst)
  | Typed.Handle (e, c) ->
    print ~at_level:1 "handle %t %t"
      (print_expression ~max_level:0 e)
      (print_computation ~max_level:0 ~pure:false c)
  | Typed.Let (lst, c) ->
    print ~at_level:2 "%t" (print_multiple_bind ~pure (lst, c))
  | Typed.LetRec (lst, c) ->
    print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation ~pure c)
  | Typed.Call (eff, e, a) ->
    assert (not pure);
    print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction ~pure a)
  | Typed.Bind (c1, {Typed.term = (p, c2)}) when pure ->
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_computation ~max_level:0 ~pure c1)
      (print_computation ~pure c2)
  | Typed.Bind (c1, a) ->
    print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
      (print_computation ~max_level:0 ~pure c1)
      (print_abstraction ~pure a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_expression e)
      (print_computation ~pure c)

and print_handler ~pure h ppf =
  Print.print ppf
    "{@[<hov>
      value_clause = (@[fun %t@]);@ 
      finally_clause = (@[fun %t@]);@ 
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with %t) : a -> (b -> _ computation) -> _ computation))
    @]}"
    (print_abstraction ~pure h.Typed.value_clause)
    (print_abstraction ~pure h.Typed.finally_clause)
    (print_effect_clauses ~pure h.Typed.effect_clauses)

and print_effect_clauses ~pure eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
    print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), {Typed.term = (p1, p2, c)}) :: cases ->
    print ~at_level:1
      "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
      (print_effect eff)
      (print_pattern p1) (print_type t1)
      (print_pattern p2) (print_type t2)
      (print_computation ~pure c)
      (print_effect_clauses ~pure cases)

and print_abstraction ~pure {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation ~pure c)

and print_multiple_bind ~pure (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation ~pure c')
  | (p, c) :: lst ->
    if pure then
      Format.fprintf ppf "let %t = %t in %t"
        (print_pattern p) (print_computation ~pure c) (print_multiple_bind ~pure (lst, c'))
    else
      Format.fprintf ppf "%t >> fun %t -> %t"
        (print_computation ~pure c) (print_pattern p) (print_multiple_bind ~pure (lst, c'))

(* and print_let_abstraction (p, c) ppf =
   Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c) *)

and print_top_let_abstraction (p, c) ppf =
  match c.Typed.term with
  | Typed.Value e -> 
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ -> 
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 ~pure:false c)

and print_let_rec_abstraction (x, a) ppf =
  let pure = is_pure_abstraction a in
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction ~pure a)

(** COMMANDS *)

let print_command (cmd, _) ppf =
  match cmd with
  | Typed.DefEffect (eff, (ty1, ty2)) ->
    Print.print ppf "type (_, _) effect += %t : (%t, %t) effect" (print_effect eff) (print_type ty1) (print_type ty2)
  | Typed.Computation c ->
    print_computation ~pure:false c ppf
  | Typed.TopLet (defs, _) ->
    Print.print ppf "let %t" (Print.sequence "\nand\n" print_top_let_abstraction defs)
  | Typed.TopLetRec (defs, _) ->
    Print.print ppf "let rec %t" (Print.sequence "\nand\n" print_let_rec_abstraction defs)
  | Typed.Use fn ->
    Print.print ppf "#use %S" (compiled_filename fn)
  | Typed.External (x, ty, f) ->
    Print.print ppf "let %t = ( %s )" (print_variable x) f
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
