open CommonPrint

type conversion =
  | Identity
  | Tuple of conversion list
  | Value
  | Compose of conversion * conversion
  | PrePostCompose of conversion * conversion

let rec ty_scheme_conversion (ctx, ty, constraints) (ctx', ty', constraints') =
  match ty, ty' with
  | Type.Basic _, Type.Basic _ -> Identity
  | Type.Tuple tys, Type.Tuple tys' ->
      Tuple (List.map2 (fun ty ty' ->
        ty_scheme_conversion (ctx, ty, constraints) (ctx', ty', constraints')
      ) tys tys')
  | Type.Arrow (ty, drty), Type.Arrow (ty', drty') ->
      PrePostCompose (
        ty_scheme_conversion (ctx', ty', constraints') (ctx, ty, constraints),
        dirty_scheme_conversion (ctx, drty, constraints) (ctx', drty', constraints')
      )
  | _, _ -> Identity

and dirty_scheme_conversion (ctx, (ty, drt), constraints) (ctx', (ty', drt'), constraints') =
  let ty_conversion = ty_scheme_conversion (ctx, ty, constraints) (ctx', ty', constraints')
  and dirt_conversion =
    let pure = Scheme.is_pure (ctx, (ty, drt), constraints)
    and pure' = Scheme.is_pure (ctx', (ty', drt'), constraints') in
    match pure, pure' with
    | true, false -> Value
    | false, true -> assert false
    | _, _ -> Identity
  in
  Compose (ty_conversion, dirt_conversion)

let rec print_conversion ?max_level conv ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match conv with
  | Identity ->
      print ~at_level:1 "fun x -> x"
  | Value ->
      print ~at_level:0 "value"
  | Compose (conv1, conv2) ->
      print ~at_level:1 "fun x -> %t (%t x)"
        (print_conversion ~max_level:0 conv1)
        (print_conversion ~max_level:0 conv2)
  | PrePostCompose (conv1, conv2) ->
      print ~at_level:1 "fun f -> fun x -> %t (f (%t x))"
        (print_conversion ~max_level:0 conv1)
        (print_conversion ~max_level:0 conv2)

let optional_conversion f = function
  | None -> Identity
  | Some x -> f x

let rec print_expression ?max_level ?expected_scheme e ppf =
  match optional_conversion (ty_scheme_conversion e.Typed.scheme) expected_scheme with
  | Identity ->
    print_expression' ?max_level e ppf
  | conv ->
    Print.print ?max_level ~at_level:1 ppf "%t %t"
      (print_conversion conv) (print_expression' ~max_level:0 e)

and print_expression' ?max_level e ppf =
  let (ctx, ty, constraints) = e.Typed.scheme in
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
    print ~at_level:2 "fun %t" (print_abstraction a)
  | Typed.Handler h ->
    print "%t" (print_handler h)
  | Typed.Effect eff ->
    print ~at_level:2 "effect %t" (print_effect eff)
  | Typed.Pure c ->
    print_computation ?max_level c ppf

and print_computation ?max_level ?expected_scheme c ppf =
  match optional_conversion (dirty_scheme_conversion c.Typed.scheme) expected_scheme with
  | Identity ->
    print_computation' ?max_level c ppf
  | conv ->
    Print.print ?max_level ~at_level:1 ppf "%t %t"
      (print_conversion conv) (print_computation' ~max_level:0 c)

and print_computation' ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
    print ~at_level:1 "%t@ %t"
      (print_expression ~max_level:1 e1)
      (print_expression ~max_level:0 e2)
  | Typed.Value e ->
    let (ctx, (ty, _), constraints) = c.Typed.scheme in
    let expected_scheme = (ctx, ty, constraints) in
    print ~at_level:1 "%t" (print_expression ~max_level:0 ~expected_scheme e)
  | Typed.Match (e, []) ->
    print ~at_level:2 "(match %t with _ -> assert false)"
      (print_expression e)
  | Typed.Match (e, lst) ->
    let expected_scheme = c.Typed.scheme in
    print ~at_level:2 "(match %t with @[<v>| %t@])"
      (print_expression e)
      (Print.cases (print_abstraction ~expected_scheme) lst)
  | Typed.Handle (e, c) ->
    print ~at_level:1 "handle %t %t"
      (print_expression ~max_level:0 e)
      (print_computation ~max_level:0 c)
  | Typed.Let (lst, c) ->
    print ~at_level:2 "%t" (print_multiple_bind (lst, c))
  | Typed.LetRec (lst, c) ->
    print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Typed.Call (eff, e, a) ->
    print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Typed.Bind (c1, {Typed.term = (p, c2)}) when Scheme.is_pure c1.Typed.scheme ->
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_computation ~max_level:0 c1)
      (print_computation c2)
  | Typed.Bind (c1, a) ->
    print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
      (print_computation ~max_level:0 c1)
      (print_abstraction a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_expression e)
      (print_computation c)

and print_handler h ppf =
  Print.print ppf
    "{@[<hov>
      value_clause = (@[fun %t@]);@ 
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with %t) : a -> (b -> _ computation) -> _ computation))
    @]}"
    (print_abstraction h.Typed.value_clause)
    (print_effect_clauses h.Typed.effect_clauses)

and print_effect_clauses eff_clauses ppf =
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
      (print_computation c)
      (print_effect_clauses cases)

and print_abstraction ?expected_scheme {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

and print_multiple_bind (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation c')
  | (p, c) :: lst when Scheme.is_pure c.Typed.scheme ->
      Format.fprintf ppf "let %t = %t in %t"
        (print_pattern p) (print_computation c) (print_multiple_bind (lst, c'))
  | (p, c) :: lst ->
      Format.fprintf ppf "%t >> fun %t -> %t"
        (print_computation c) (print_pattern p) (print_multiple_bind (lst, c'))

and print_top_let_abstraction (p, c) ppf =
  match c.Typed.term with
  | Typed.Value e -> 
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ -> 
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a)

(** COMMANDS *)

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
