(** Syntax of the core language. *)
open CoreUtils

module CoreSyntax = UntypedSyntax

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

(** Types used by Ocaml. *)
type ty =
  | TyApply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | TyBasic of string
  | TyTuple of ty list
  | TyArrow of ty * ty

type tydef =
  | TyDefRecord of (field, ty) Assoc.t
  | TyDefSum of (CoreTypes.Label.t, ty option) Assoc.t
  | TyDefInline of ty

(** Patterns *)
type pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (field, pattern) Assoc.t
  | PVariant of label * pattern option
  | PConst of Const.t
  | PReturn of pattern
  | PNonbinding

type term =
  | Var of variable
  | Const of Const.t
  | Annotated of term * ty
  | Tuple of term list
  | Record of (field, term) Assoc.t
  | Variant of label * term option
  | Lambda of abstraction
  | Function of match_case list
  | Effect of effect * ty * ty
  | Let of (pattern * term) * term
  | LetRec of (variable * abstraction) list * term
  | Match of term * match_case list
  | Apply of term * term
  | Check of term
  | Return of term
  | Call of effect * term * abstraction
  | Handler of abstraction_with_type * effect_clause list
  | Bind of term * abstraction

and match_case =
  | ValueClause of abstraction
  | EffectClause of effect * abstraction2

(** Abstractions that take one argument. *)
and abstraction = pattern * term

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * term

and abstraction_with_type = pattern * ty * term

and effect_clause = (effect * ty * ty) * abstraction2

(*************************** PRINTING ***************************)

let print_variable = CoreTypes.Variable.print ~safe:true

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | PVar x -> print "%t" (print_variable x)
  | PAs (p, x) ->
      print "%t as %t" (print_pattern p) (print_variable x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record CoreTypes.Field.print print_pattern lst ppf
  | PVariant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | PVariant (lbl, None) -> CoreTypes.Label.print lbl ppf
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "(%t @[<hov>%t@])" (CoreTypes.Label.print lbl) (print_pattern p)
  | PReturn p ->
      print ~at_level:1 "(return %t)" (print_pattern p)
  | PAnnotated (pat, _) -> print "%t" (print_pattern pat)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (print_variable x)
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record (CoreTypes.Field.print) print_expression lst ppf
  | Variant (lbl, None) -> print "%t" (CoreTypes.Field.print lbl)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "(%t %t)" (CoreTypes.Field.print lbl) (print_expression e)
  | Lambda (x, c) ->
      print "fun (%t) -> %t" (print_pattern x) (print_term c)
  | Effect (eff, _, _) -> print ~at_level:2 "effect %t" (CoreTypes.Effect.print eff)
  | Handler (value_clause, effect_clauses) ->
      print ~at_level:2
        "fun c -> handler {@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->\n             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]} c"
        (print_abstraction_with_ty value_clause)
        (print_effect_clauses effect_clauses)

and print_term ?max_level t ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match t with
  | Let ((p, t1), t2) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t" (print_pattern p)
        (print_expression t1) (print_term t2)
  | Apply (e1, e2) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | Call (eff, e, a) ->
      print ~at_level:1 "call %t %t (@[fun %t@])" (CoreTypes.Effect.print eff)
        (print_expression ~max_level:0 e)
        (print_abstraction a)
  | Bind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_term ~max_level:0 c1)
        (print_abstraction a)
  | Match (e, alist) ->
      print ~at_level:1 "match %t with %t"
        (print_expression ~max_level:0 e)
        (print_cases alist)
  | LetRec ([(var, abs)], c) ->
      print ~at_level:2 "let rec @[<hov>%t =@ %t@ in@]@ %t"
        (print_variable var) (print_abstraction abs) (print_term c)

and print_type t ppf = failwith "TODO"

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | ( (eff, t1, t2), (p1, p2, c)) :: cases ->
      print ~at_level:1
        "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
        (CoreTypes.Effect.print eff) (print_pattern p1) (print_type t1)
        (print_pattern p2) (print_type t2) (print_term c)
        (print_effect_clauses cases)

and print_cases cases ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match cases with
  | [] -> ()
  | case :: cases ->
      ( match case with
      | ValueClause (p, c) ->
        print ~at_level:1 "| %t -> %t %t" (print_pattern p) (print_term c)
          (print_cases cases)
      | EffectClause (eff, (p1, p2, c)) ->
        print ~at_level:1 "| Eff_%t %t %t -> %t %t" (CoreTypes.Effect.print eff)
          (print_pattern p1) (print_pattern p2) (print_term c)
          (print_cases cases) )

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_term c)

and print_abstraction_with_ty (p, _, c) ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_term c)
