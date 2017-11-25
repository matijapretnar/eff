module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.Untyped.term with
  | Untyped.PVar x -> print "%t" (Variable.print ~safe:true x)
  | Untyped.PAs (p, x) -> print "%t as %t" (print_pattern p) (Variable.print ~safe:true x)
  | Untyped.PConst c -> Const.print c ppf
  | Untyped.PTuple lst -> Print.tuple print_pattern lst ppf
  | Untyped.PRecord lst -> Print.record print_pattern lst ppf
  | Untyped.PVariant (lbl, None) when lbl = OldUtils.nil -> print "[]"
  | Untyped.PVariant (lbl, None) -> print "%s" lbl
  | Untyped.PVariant (lbl, Some ({ term = PTuple [p1; p2] })) when lbl = OldUtils.cons ->
    print ~at_level:1 "[@[<hov>@[%t@]%t@]]" (print_pattern p1) (pattern_list p2)
  | Untyped.PVariant (lbl, Some p) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (print_pattern p)
  | Untyped.PNonbinding -> print "_"

and pattern_list ?(max_length=299) p ppf =
  if max_length > 1 then
    match p.Untyped.term with
    | Untyped.PVariant (lbl, Some ({ term = PTuple [v1; v2] })) when lbl = OldUtils.cons ->
      Format.fprintf ppf ",@ %t%t" (print_pattern v1) (pattern_list ~max_length:(max_length - 1) v2)
    | Untyped.PVariant (lbl, None) when lbl = OldUtils.nil -> ()
    | _ -> Format.fprintf ppf "(??? %t ???)" (print_pattern p)
  else
    Format.fprintf ppf ",@ ..."

let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Untyped.term with
  | Untyped.Apply (e1, e2) -> print ~at_level:1 "%t %t" (print_expression e1) (print_expression ~max_level:0 e2)
  | Untyped.Value e -> print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Untyped.Match (e, lst) -> print "match %t with (@[<hov>%t@])" (print_expression e) (Print.sequence " | " case lst)
  | Untyped.Handle (e, c) -> print "handle %t with %t" (print_expression e) (print_computation c)
  | Untyped.Let (lst, c) -> print "let @[<hov>%t@] in %t" (Print.sequence " | " let_abstraction lst) (print_computation c)
  | Untyped.LetRec (lst, c) -> print "let rec ... in %t" (print_computation c)

and print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Untyped.term with
  | Untyped.Var x -> print "%t" (Variable.print ~safe:true x)
  | Untyped.Const c -> print "%t" (Const.print c)
  | Untyped.Tuple lst -> Print.tuple print_expression lst ppf
  | Untyped.Record lst -> Print.record print_expression lst ppf
  | Untyped.Variant (lbl, None) -> print "%s" lbl
  | Untyped.Variant (lbl, Some e) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Untyped.Lambda a -> print "fun %t" (abstraction a)
  | Untyped.Handler _  -> print "<handler>"
  | Untyped.Effect eff -> print "%s" eff

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf =
  Format.fprintf ppf "%t" (abstraction a)
