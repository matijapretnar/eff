(** Syntax of the core language. *)

module CoreSyntax = UntypedSyntax

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

(** Types used by Ocaml. *)
type ty =
  | TyApply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | TyBasic of Const.ty
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
  | LambdaList of term list
  | Effect of effect * ty * ty
  | Let of (pattern * term) * term
  | LetRec of (variable * abstraction) list * term
  | Match of term * match_case list
  | Apply of term * term
  | Return of term
  | Call of effect * term * abstraction
  | Handler of abstraction_with_type * effect_clause list
  | Bind of term * abstraction

and cmd =
  | Term of term
  | DefEffect of effect * ty * ty
  | External of (variable * ty * string)
  | TyDef of (CoreTypes.TyName.t * (CoreTypes.TyParam.t list * tydef)) list

and match_case =
  | ValueClause of abstraction
  | EffectClause of effect * abstraction2

and abstraction = pattern * term
(** Abstractions that take one argument. *)

and abstraction2 = pattern * pattern * term
(** Abstractions that take two arguments. *)

and abstraction_with_type = pattern * ty * term

and effect_clause = (effect * ty * ty) * abstraction2

(*************************** PRINTING ***************************)

let print_variable = CoreTypes.Variable.print ~safe:true

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | PVar x -> print "%t" (print_variable x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record CoreTypes.Field.print print_pattern lst ppf
  | PVariant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | PVariant (lbl, None) -> CoreTypes.Label.print lbl ppf
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "(%t @[<hov>%t@])"
        (CoreTypes.Label.print lbl)
        (print_pattern p)
  | PReturn p -> print ~at_level:1 "Value (%t)" (print_pattern p)
  | PAnnotated (pat, _) -> print "%t" (print_pattern pat)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (print_variable x)
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record CoreTypes.Field.print print_expression lst ppf
  | Variant (lbl, None) -> print "%t" (CoreTypes.Field.print lbl)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "(%t %t)"
        (CoreTypes.Field.print lbl)
        (print_expression e)
  | Lambda (x, c) ->
      print "fun (%t) -> (%t)" (print_pattern x) (print_expression c)
  | LambdaList ls ->
      print "fun lst -> (map ( (x,y) -> (x y) ) (zip [%t] lst))"
        (print_lambda_list ls)
  | Effect (eff, _, _) ->
      print ~at_level:2 "effect %t" (CoreTypes.Effect.print eff)
  | Handler (value_clause, effect_clauses) ->
      print ~at_level:2
        "(handler {value_clause = (fun %t); effect_clauses = (fun (type a) \
         (type b) (x : (a, b) effect) -> ((match x with %t) : a -> (b -> _ \
         computation) -> _ computation)) })"
        (print_value_clause value_clause)
        (print_effect_clauses effect_clauses)
  | Let ((p, t1), t2) ->
      print "let %t = (%t) in (%t)" (print_pattern p) (print_expression t1)
        (print_expression t2)
  | Apply (t1, t2) ->
      print "(%t) (%t)" (print_expression t1) (print_expression t2)
  | Annotated (t, ty) -> print "%t: %t" (print_expression t) (print_type ty)
  | LetRec (ls, t) ->
      print "%t (%t)" (print_letrec_cases ls) (print_expression t)
  | Match (t, ls) ->
      print "(match (%t) with %t)" (print_expression t) (print_match_cases ls)
  | Return t -> print "Value (%t)" (print_expression t)
  | Bind (t, (p, c)) ->
      print "%t >> (fun (%t) -> (%t))" (print_expression t) (print_pattern p)
        (print_expression c)
  | Call (eff, t, (p, c)) ->
      print "call %t (%t) (fun (%t) -> (%t))"
        (CoreTypes.Effect.print eff)
        (print_expression t) (print_pattern p) (print_expression c)

and print_lambda_list ?max_level ls ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ls with
  | [] -> print ""
  | l :: rest -> print "(%t);" (print_expression l)

and print_letrec_cases ?max_level ls ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ls with
  | [] -> print ""
  | (v, (p, c)) :: rest ->
      print "let rec %t = %t in %t" (print_variable v) (print_expression c)
        (print_letrec_cases rest)

and print_match_cases ?max_level ls ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ls with
  | [] -> print ""
  | m :: rest -> (
      match m with
      | ValueClause (p, c) ->
          print "| %t -> (%t) %t" (print_pattern p) (print_expression c)
            (print_match_cases rest)
      | EffectClause (eff, (p1, p2, c)) ->
          print "| %t (%t, %t) -> ((%t) (%t))"
            (CoreTypes.Effect.print eff)
            (print_pattern p1) (print_pattern p2) (print_expression c)
            (print_match_cases rest))

and print_command ?max_level cmd ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match cmd with
  | Term t -> print ~at_level:2 "%t" (print_expression t)
  | DefEffect (eff, ty1, ty2) ->
      print ~at_level:2 "type (_, _) effect += %t : (%t, %t) effect;;\n\n"
        (CoreTypes.Effect.print eff)
        (print_type ty1) (print_type ty2)
  | External (v, t, s) ->
      print ~at_level:2 "%t: (%t) = %s" (print_variable v) (print_type t) s
  | TyDef defs -> print_tydefs defs ppf

and print_tydefs ?max_level defs ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match defs with
  | [] -> print " "
  | def :: rest -> print "%t; %t" (print_tydef def) (print_tydefs rest)

and print_tydef ?max_level (name, (params, tydef)) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match tydef with
  | TyDefRecord assoc ->
      print "%t" (Print.record CoreTypes.Field.print print_type assoc)
  | TyDefSum assoc -> print_sums (Assoc.to_list assoc) ppf
  | TyDefInline ty -> print "%t" (print_type ty)

and print_sums ?max_level sums ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match sums with
  | [] -> print ""
  | (lbl, ty_opt) :: rest -> (
      match ty_opt with
      | None -> print "\n| %t %t" (CoreTypes.Label.print lbl) (print_sums rest)
      | Some ty ->
          print "\n| %t of %t %t"
            (CoreTypes.Label.print lbl)
            (print_type ty) (print_sums rest))

and print_type ?max_level t ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match t with
  | TyApply (name, tys) ->
      print ~at_level:1 "(%t) (%t)"
        (Print.sequence ", " print_type tys)
        (CoreTypes.TyName.print name)
  | TyParam p -> CoreTypes.TyParam.print p ppf
  | TyBasic s -> print "%t" (Const.print_ty s)
  | TyTuple [] -> print "unit"
  | TyTuple tys ->
      print ~at_level:2 "@[<hov>%t@]"
        (Print.sequence (Symbols.times ()) (print_type ~max_level:1) tys)
  | TyArrow (ty1, ty2) -> print "(%t) -> (%t)" (print_type ty1) (print_type ty2)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> (fun arg k -> Call (eff', arg, k))"
  | ((eff, t1, t2), (p1, p2, c)) :: cases ->
      print ~at_level:1
        "| %t -> (fun (%t : a) (%t : b -> _ computation) -> (%t)) %t"
        (CoreTypes.Effect.print eff)
        (print_pattern p1) (print_pattern p2) (print_expression c)
        (print_effect_clauses cases)

and print_cases cases ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match cases with
  | [] -> ()
  | case :: cases -> (
      match case with
      | ValueClause (p, c) ->
          print ~at_level:1 "| %t -> (%t) %t \n" (print_pattern p)
            (print_expression c) (print_cases cases)
      | EffectClause (eff, (p1, p2, c)) ->
          print ~at_level:1 "| Eff_%t %t %t -> %t %t \n"
            (CoreTypes.Effect.print eff)
            (print_pattern p1) (print_pattern p2) (print_expression c)
            (print_cases cases))

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_expression c)

and print_abstraction_with_ty (p, _, c) ppf =
  Format.fprintf ppf "(%t) -> (%t)" (print_pattern p) (print_expression c)

and print_value_clause (p, _, c) ppf =
  Format.fprintf ppf "(%t) -> (Value (%t))" (print_pattern p)
    (print_expression c)
