(** Syntax of the core language. *)

module Variable = Symbol.Make (Symbol.String)
module EffectMap = Map.Make (String)

type variable = Variable.t

type effect = OldUtils.effect

type 'term annotation = {term: 'term; location: Location.t}

let add_loc t loc = {term= t; location= loc}

type pattern = plain_pattern annotation

and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (OldUtils.field, pattern) OldUtils.assoc
  | PVariant of OldUtils.label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure expressions *)
type expression = plain_expression annotation

and plain_expression =
  | Var of variable
  | Const of Const.t
  | Tuple of expression list
  | Record of (OldUtils.field, expression) OldUtils.assoc
  | Variant of OldUtils.label * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler

(** Impure computations *)
and computation = plain_computation annotation

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
  { effect_clauses: (effect, abstraction2) OldUtils.assoc
  ; value_clause: abstraction
  ; finally_clause: abstraction }

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation)

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation)

(* Toplevel commands (the first four do not need to be separated by [;;]) *)
type command = plain_command annotation

and plain_command =
  | Tydef of (OldUtils.tyname, Type.ty_param list * Tctx.tydef) OldUtils.assoc
      (** [type t = tydef] *)
  | TopLet of (pattern * computation) list
      (** [let p1 = t1 and ... and pn = tn] *)
  | TopLetRec of (variable * abstraction) list
      (** [let rec f1 p1 = t1 and ... and fn pn = tn] *)
  | External of variable * Type.ty * string
      (** [external x : t = "ext_val_name"] *)
  | DefEffect of effect * (Type.ty * Type.ty)  (** [effect Eff : ty1 -> t2] *)
  | Computation of computation
  | Use of string  (** [#use "filename.eff"] *)
  | Reset  (** [#reset] *)
  | Help  (** [#help] *)
  | Quit  (** [#quit] *)
  | TypeOf of computation  (** [#type t] *)

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PVar x -> print "%t" (Variable.print x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (Variable.print x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record print_pattern lst ppf
  | PVariant (lbl, None) when lbl = OldUtils.nil -> print "[]"
  | PVariant (lbl, None) -> print "%s" lbl
  | PVariant (lbl, Some {term= PTuple [v1; v2]}) when lbl = OldUtils.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_pattern v1) (pattern_list v2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_pattern p)
  | PNonbinding -> print "_"


and pattern_list ?(max_length= 299) p ppf =
  if max_length > 1 then
    match p.term with
    | PVariant (lbl, Some {term= PTuple [v1; v2]}) when lbl = OldUtils.cons ->
        Format.fprintf ppf ",@ %t%t" (print_pattern v1)
          (pattern_list ~max_length:(max_length - 1) v2)
    | PVariant (lbl, None) when lbl = OldUtils.nil -> ()
    | _ -> Format.fprintf ppf "(??? %t ???)" (print_pattern p)
  else Format.fprintf ppf ",@ ..."


let rec print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
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
  match e.term with
  | Var x -> print "%t" (Variable.print x)
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record print_expression lst ppf
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_expression e)
  | Lambda a -> print "fun %t" (abstraction a)
  | Handler _ -> print "<handler>"
  | Effect eff -> print "%s" eff

and abstraction (p, c) ppf =
  Format.fprintf ppf "%t -> %t" (print_pattern p) (print_computation c)

and let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and case a ppf = Format.fprintf ppf "%t" (abstraction a)
