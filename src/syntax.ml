(** Syntax of the core language. *)

type variable = int * Common.variable
type pattern = variable Pattern.t

(** Pure expressions *)
type expression = plain_expression Common.pos
and plain_expression =
  | Var of variable
  | Const of Common.const
  | Tuple of expression list
  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option
  | Lambda of abstraction
  | Operation of operation
  | Handler of handler

(** Impure computations *)
and computation = plain_computation Common.pos
and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | While of computation * computation
  | For of variable * expression * expression * computation * bool
  | Apply of expression * expression
  | New of Common.tyname * resource option
  | Handle of expression * computation
  | Check of computation

(** Handler definitions *)
and handler = {
  operations : (operation, abstraction2) Common.assoc;
  value : abstraction;
  finally : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = pattern * computation

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * computation

(** An operation is an expression that represents an instance together with
    an operation symbol. *)
and operation = expression * Common.opsym

(** A resource consists of an expression for initial state and of a definition
    of operations, which take an argument and a state, and return a result and
    the new state. *)
and resource = expression * (Common.opsym, abstraction2) Common.assoc

let rec print_pattern ?max_level (p,_) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | Pattern.Var x -> print "%t" (Print.variable x)
  | Pattern.As (p, x) -> print "%t as %t" (print_pattern p) (Print.variable x)
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
  | Apply (e1, e2) -> print ~at_level:1 "%t %t" (print_expression e1) (print_expression ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Match (e, lst) -> print "match %t with (@[<hov>%t@])" (print_expression e) (Print.sequence " | " case lst)
  | While (c1, c2) -> print "while %t do %t done" (print_computation c1) (print_computation c2)
  | For (i, e1, e2, c, d) -> print "for %t = ... " (Print.variable i)
  | New (eff, None) -> print "new %s" eff
  | New (eff, Some (e, lst)) -> print "new %s @ %t with ... end" eff (print_expression e)
  | Handle (e, c) -> print "handle %t with %t" (print_expression e) (print_computation c)
  | Let (lst, c) -> print "let @[<hov>%t@] in %t" (Print.sequence " | " let_abstraction lst) (print_computation c)
  | LetRec (lst, c) -> print "let rec ... in %t" (print_computation c)
  | Check c -> print "check %t" (print_computation c)


and print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match fst e with
  | Var x -> print "%t" (Print.variable x)
  | Const c -> print "%t" (Common.print_const c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record print_expression lst ppf
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some e) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Lambda a -> print "fun %t" (abstraction a)
  | Handler _  -> print "<handler>"
  | Operation (e, op) -> print "%t#%s" (print_expression e) op

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf =
  Format.fprintf ppf "%t" (abstraction a)
