(** Syntax of the core language. *)

module Variable = Symbol.Make (Symbol.String)
module EffectMap = Map.Make (String)

type variable = Variable.t

type effect = OldUtils.effect

let add_loc t loc = {CoreUtils.it= t; CoreUtils.at= loc}

let loc_of loc_t = loc_t.CoreUtils.at

let term_of loc_t = loc_t.CoreUtils.it

(* Changing the datatype [plain_pattern] will break [specialize_vector] in [exhaust.ml] because
   of wildcard matches there. *)

type pattern = plain_pattern CoreUtils.located

and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (OldUtils.field, pattern) Assoc.t
  | PVariant of OldUtils.label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure expressions *)
type expression = plain_expression CoreUtils.located

and plain_expression =
  | Var of variable
  | Const of Const.t
  | Tuple of expression list
  | Record of (OldUtils.field, expression) Assoc.t
  | Variant of OldUtils.label * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler

(** Impure computations *)
and computation = plain_computation CoreUtils.located

and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Handle of expression * computation
  | Check of computation

(** Handler definitions *)
and handler =
  { effect_clauses: (effect, abstraction2) Assoc.t
  ; value_clause: abstraction
  ; finally_clause: abstraction }

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation)

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation)

let rec contains_variable_expression var {term= e} =
  contains_variable_plain_expression var e


and contains_variable_plain_expression var = function
  | Var var' -> var = var'
  | Const _ -> false
  | Tuple es -> List.exists (contains_variable_expression var) es
  | Record lab_e_assoc ->
      List.exists
        (fun (lab, e) -> contains_variable_expression var e)
        lab_e_assoc
  | Variant (lab, e_option) ->
      OldUtils.map_default (contains_variable_expression var) false e_option
  | Lambda abs -> contains_variable_abs var abs
  | Effect _ -> false
  | Handler h -> contains_variable_handler var h


and contains_variable_abs var (pat, c) = contains_variable_comp var c

and contains_variable_comp var {term= c} = contains_variable_plain_comp var c

and contains_variable_plain_comp var = function
  | Value e -> contains_variable_expression var e
  | Let (defs, c) ->
      List.exists (fun (_, c) -> contains_variable_comp var c) defs
      || contains_variable_comp var c
  | LetRec (defs, c) ->
      List.exists (fun (_, abs) -> contains_variable_abs var abs) defs
      || contains_variable_comp var c
  | Match (e, abs_list) ->
      contains_variable_expression var e
      || List.exists (contains_variable_abs var) abs_list
  | Apply (e1, e2) ->
      contains_variable_expression var e1
      || contains_variable_expression var e2
  | Handle (e, c) ->
      contains_variable_expression var e || contains_variable_comp var c
  | Check c -> contains_variable_comp var c


and contains_variable_handler var
    {effect_clauses= eff_abs2_assoc; value_clause= abs1; finally_clause= abs2} =
  List.exists
    (fun (eff, abs2) -> contains_variable_abs2 var abs2)
    eff_abs2_assoc
  || contains_variable_abs var abs1 || contains_variable_abs var abs2


and contains_variable_abs2 var (pat1, pat2, c) = contains_variable_comp var c

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match term_of p with
  | PVar x -> print "%t" (Variable.print x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (Variable.print x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record print_pattern lst ppf
  | PVariant (lbl, None) when lbl = OldUtils.nil -> print "[]"
  | PVariant (lbl, None) -> print "%s" lbl
  | PVariant (lbl, Some {CoreUtils.it= PTuple [v1; v2]})
    when lbl = OldUtils.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_pattern v1) (pattern_list v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_pattern p)
  | PNonbinding -> print "_"


and pattern_list ?(max_length= 299) p ppf =
  if max_length > 1 then
    match term_of p with
    | PVariant (lbl, Some {CoreUtils.it= PTuple [v1; v2]})
      when lbl = OldUtils.cons ->
        Format.fprintf ppf ",@ %t%t" (print_pattern v1)
          (pattern_list ~max_length:(max_length - 1) v2)
    | PVariant (lbl, None) when lbl = OldUtils.nil -> ()
    | _ -> Format.fprintf ppf "(??? %t ???)" (print_pattern p)
  else Format.fprintf ppf ",@ ..."


let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match term_of c with
  | Apply (e1, e2) ->
      print ~at_level:1 "%t %t" (print_expression e1)
        (print_expression ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Match (e, lst) ->
      print "match %t with (@[<hov>%t@])" (print_expression e)
        (Print.sequence " | " case lst)
  | Handle (e, c) ->
      print "handle %t with %t" (print_expression e) (print_computation c)
  | Let (lst, c) ->
      print "let @[<hov>%t@] in %t"
        (Print.sequence " | " let_abstraction lst)
        (print_computation c)
  | LetRec (lst, c) -> print "let rec ... in %t" (print_computation c)
  | Check c -> print "check %t" (print_computation c)

and print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match term_of e with
  | Var x -> print "%t" (Variable.print x)
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record print_expression lst ppf
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Lambda a -> print "fun %t" (abstraction a)
  | Handler h ->
      print "{effect_clauses = %t; value_clause = (%t)}"
        (Print.sequence " | " effect_clause (Assoc.to_list h.effect_clauses))
        (abstraction h.value_clause)
  | Effect eff -> print "%s" eff

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf = Format.fprintf ppf "%t" (abstraction a)

and effect_clause (eff, a2) ppf =
  Format.fprintf ppf "| %s -> %t" eff (abstraction2 a2)

and abstraction2 (p1, p2, c) ppf =
  Format.fprintf ppf "%t %t -> %t" (print_pattern p1) (print_pattern p2)
    (print_computation c)
