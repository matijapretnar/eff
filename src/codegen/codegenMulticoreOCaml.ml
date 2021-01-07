let print_variable = Erasure.Variable.print ~safe:true

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | Erasure.PEVar x -> print "%t" (print_variable x)
  | Erasure.PEAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | Erasure.PEConst c -> Const.print c ppf
  | Erasure.PETuple lst -> Print.tuple print_pattern lst ppf
  | Erasure.PERecord lst -> Print.record print_pattern lst ppf
  | Erasure.PEVariant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | Erasure.PEVariant (lbl, None) -> print "%s" lbl
  | Erasure.PEVariant ("(::)", Some (Erasure.PETuple [ p1; p2 ])) ->
      print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | Erasure.PEVariant (lbl, Some p) ->
      print ~at_level:1 "(%s %t)" lbl (print_pattern p)
  | Erasure.PENonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Erasure.EVar x -> print "%t" (print_variable x)
  | Erasure.EBuiltIn (s, n) ->
      if n = 1 then print ~at_level:1 "lift_unary %s" s
      else if n = 2 then print ~at_level:1 "lift_binary %s" s
      else assert false
  | Erasure.EConst c -> print "%t" (Const.print c)
  | Erasure.ETuple lst -> Print.tuple print_expression lst ppf
  | Erasure.ERecord lst -> Print.record print_expression lst ppf
  | Erasure.EVariant (lbl, None) -> print "%s" lbl
  | Erasure.EVariant (lbl, Some e) ->
      print ~at_level:1 "(%s %t)" lbl (print_expression e)
  | Erasure.ELambda (x, _, c) ->
      print "fun (%t) -> %t" (print_pattern x) (print_computation c)
  | Erasure.EEffect eff -> print ~at_level:2 "effect %t" (print_effect eff)
  | Erasure.EHandler h ->
      print ~at_level:2
        "fun c -> handler { value_clause = (fun %t); effect_clauses = (fun \
         (type a) (type b) (x : (a, b) effect) ->\n\
        \             ((match x with %t) : a -> (b -> _ computation) -> _ \
         computation)) } c"
        (print_abstraction_with_ty h.Erasure.value_clause)
        (print_effect_clauses (Assoc.to_list h.Erasure.effect_clauses))
  | EBigLambdaSkel (_, e) -> print "%t" (print_expression e)
  | EApplySkelExp (e, _) -> print "%t" (print_expression e)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | Erasure.EValue e -> print ~at_level:1 "%t" (print_expression ~max_level:0 e)
  | Erasure.ELetVal (p, e, c) ->
      print ~at_level:2 "let %t = %t in %t" (print_pattern p)
        (print_expression e) (print_computation c)
  | Erasure.EApply (e1, e2) ->
      print ~at_level:1 "%t %t"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | Erasure.EHandle (e, c) ->
      print ~at_level:1 "%t %t"
        (print_expression ~max_level:0 e)
        (print_computation ~max_level:0 c)
  | Erasure.ECall (eff, e, a) ->
      print ~at_level:1 "call %t %t (fun %t)" (print_effect eff)
        (print_expression ~max_level:0 e)
        (print_abstraction_with_ty a)
  | Erasure.EBind (c1, (p, c2)) ->
      print ~at_level:2 "let %t = %t in %t" (print_pattern p)
        (print_computation c1) (print_computation c2)
  | Erasure.EMatch (e, alist) ->
      print ~at_level:1 "match %t with %t"
        (print_expression ~max_level:0 e)
        (print_cases alist)
  | Erasure.ELetRec ([ (var, _, e) ], c) ->
      print ~at_level:2 "let rec %t = %t in %t" (print_variable var)
        (print_expression e) (print_computation c)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((eff_name, (t1, t2)) as eff), (p1, p2, c)) :: cases ->
      print ~at_level:1
        "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
        (print_effect eff) (print_pattern p1) (Types.print_target_ty t1)
        (print_pattern p2) (Types.print_target_ty t2) (print_computation c)
        (print_effect_clauses cases)

and print_cases cases ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match cases with
  | [] -> ()
  | (p, c) :: cases ->
      print ~at_level:1 "| %t -> %t %t" (print_pattern p) (print_computation c)
        (print_cases cases)

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and print_abstraction_with_ty (p, _, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)
