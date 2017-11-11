
(**********************)
(* PRINTING FUNCTIONS *)
(**********************)

module Variable = Symbol.Make(Symbol.String)

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let print_variable = Variable.print ~safe:true

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.Typed.term with
  | Typed.PVar x -> print "%t" (print_variable x)
  | Typed.PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | Typed.PConst c -> Const.print c ppf
  | Typed.PTuple lst -> Print.tuple print_pattern lst ppf
  | Typed.PRecord lst -> Print.record print_pattern lst ppf
  | Typed.PVariant (lbl, None) when lbl = OldUtils.nil -> print "[]"
  | Typed.PVariant (lbl, None) -> print "%s" lbl
  | Typed.PVariant ("(::)", Some ({ term = PTuple [p1; p2] })) ->
    print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | Typed.PVariant (lbl, Some p) ->
    print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | Typed.PNonbinding -> print "_"

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
    print ~at_level:1 "%s %t" lbl (print_expression e)
  | Typed.Lambda (_,_,_) ->
    assert false (*Still needs to be done*)
  | Typed.Handler h ->
    print "{@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]}"
      (print_abstraction h.value_clause)
      (print_effect_clauses h.effect_clauses)
  | Typed.Effect eff ->
    print ~at_level:2 "effect %t" (print_effect eff)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
    print ~at_level:1 "%t@ %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Typed.Value e ->
    print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Typed.Match (e, []) ->
    print ~at_level:2 "(match %t with _ -> assert false)" (print_expression e)
  | Typed.Match (e, lst) ->
    print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e) (Print.cases print_abstraction lst)
  | Typed.Handle (e, c) ->
    print ~at_level:1 "handle %t %t" (print_expression ~max_level:0 e) (print_computation ~max_level:0 c)
  | Typed.LetRec (lst, c) ->
    print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Typed.Call (eff, e, a) ->
    print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Typed.Bind (c1, a) ->
    print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]" (print_computation ~max_level:0 c1) (print_abstraction a)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
    print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), {term = (p1, p2, c)}) :: cases ->
    print ~at_level:1 "| %t -> (fun %t %t -> %t) %t"
      (print_effect eff) (print_pattern p1) (print_pattern p2) (print_computation c) (print_effect_clauses cases)

and print_abstraction {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

and print_pure_abstraction {Typed.term = (p, e)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_expression e)

and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_top_let_abstraction (p, c) ppf =
  match c.Typed.term with
  | Typed.Value e ->
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ ->
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a)
