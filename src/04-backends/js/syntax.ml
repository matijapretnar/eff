open Language
module Assoc = Utils.Assoc
module Print = Utils.Print

(** Syntax of the core language. *)

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

(** Patterns *)
type pattern_shape =
  | PArbitrary
  | PTuple of pattern_shape list
  | PRecord of (field, pattern_shape) Assoc.t
  | PVariant of label * pattern_shape option
  | PConst of Const.t

type projection = Int of int | Field of field | VariantProj

type js_term =
  | Var of variable
  | Const of Const.t
  (* a LIST of terms - equivalent to list in JS, also handles tuples *)
  | List of js_term list
  (* RECORD representation - multiple fields, each with it's own name (string) and the actual term *)
  | Record of (field * js_term) list
  (* VARIANTs as are known in Eff - a label with an optional term *)
  | Variant of label * js_term option
  (* LAMBDA is very similar to Eff's lambda - takes a variable and a computation *)
  | Lambda of abstraction
  (* EFFECT is an effect identifier - a symbol *)
  | Effect of effect
  (* HANDLER handles performed effects - can handle multiple effects and also have a finally and value clause *)
  | Handler of handler
  (* APPLY is function application.. it is very similar in JS to the one in Eff *)
  | Apply of js_term * js_term
  (* LET is uniform across JS and it does not differentiate between 'let' and 'let rec' *)
  | Let of variable * js_term
  (* MATCH holds a list of triples shape, a variable and a computation - the value of the variable must be compatible with the shape to execute the computation *)
  | Match of (pattern_shape * abstraction) list
  (* A PROJECTION for a variable - projections denote the correct field path to take in the 'match' object *)
  | Projection of variable * projection list
  (* BIND is used to construct continuations - new in JS *)
  | Bind of js_term * abstraction
  (* HANDLE evaluates the computation (2nd term) with the given handler (1st term) *)
  | Handle of js_term * js_term
  (* SEQUENCE denotes a sequence of terms *)
  | Sequence of js_term list
  (* COMMENTs are used for translating the terms which do not translate well to JS e.g. type checking *)
  | Comment of string

and handler = {
  effect_clauses : (effect * abstraction2) list;
  value_clause : abstraction;
  finally_clause : abstraction;
}

and abstraction = variable * js_term

and abstraction2 = variable * variable * js_term

type cmd =
  | Term of js_term
  | TopLet of (variable * js_term * js_term) list
  | TopLetRec of js_term
  | External of (variable * string)

let print = Format.fprintf

let symbol_print desc n ppf =
  let replaced = String.map (fun c -> if c == '\'' then '_' else c) desc in
  match replaced.[0] with
  | 'a' .. 'z' | '_' -> print ppf "%s_%d" replaced n
  | 'A' .. 'Z' -> print ppf "%s" replaced
  | _ -> print ppf "_var_%d /* %s */" n desc

let rec indented_sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [ v ] -> pp v ppf
  | v :: vs ->
      print ppf "@[<v 2>%t@]%s@,@[<v 2>%t@]" (pp v) sep
        (indented_sequence sep pp vs)

let rec print_term return term ppf =
  let prepend_return f =
    if return then print ppf "@[<v 2>return %t@];" f else f ppf
  in
  match term with
  | Var v -> prepend_return @@ print_variable v
  | Const c -> prepend_return @@ print_constant c
  | Projection (m, ps) -> prepend_return @@ print_projection_list m ps
  | List l -> prepend_return @@ print_list l
  | Record r -> prepend_return @@ print_record r
  | Variant (lbl, t) -> prepend_return @@ print_variant lbl t
  | Lambda a -> prepend_return @@ print_abstraction a
  | Effect e -> prepend_return @@ print_effect_call e
  | Handler h -> prepend_return @@ print_handler h
  | Let (v, t) -> print_let v t ppf
  | Bind (t, a) -> prepend_return @@ print_bind t a
  | Match ms -> print_match return ms ppf
  | Apply (t1, t2) -> prepend_return @@ print_apply t1 t2
  | Handle (t1, t2) -> prepend_return @@ print_handle t1 t2
  | Sequence s -> print_sequence return s ppf
  | Comment c -> print_comment c ppf

and print_constant c = Const.print c

and print_variable v = CoreTypes.Variable.fold symbol_print v

and print_field f = CoreTypes.Field.fold symbol_print f

and print_label lbl = CoreTypes.Label.fold symbol_print lbl

and print_effect_label e = CoreTypes.Effect.fold symbol_print e

and print_effect_call e ppf =
  print ppf "new Call('%t').perform" @@ print_effect_label e

and print_let v t ppf =
  print ppf "@[<v 2>const %t = %t@]" (print_variable v) (print_term false t)

and print_list l ppf =
  match l with
  | [] -> print ppf "[]"
  | _ ->
      print ppf "[@,%t@;<0 -2>]" @@ indented_sequence "," (print_term false) l

and print_record r ppf =
  print ppf "({@,%t@;<0 -2>})" @@ indented_sequence "," print_record_term r

and print_record_term (f, t) ppf =
  print ppf "%t: %t" (print_field f) (print_term false t)

and print_variant lbl t_opt ppf =
  match t_opt with
  | None -> print ppf "({ 'name': '%t' })" (print_label lbl)
  | Some t ->
      print ppf "({@,'name': '%t',@,@[<v 2>'arg': %t@]@;<0 -2>})"
        (print_label lbl) (print_term false t)

and print_bind t a ppf =
  print ppf "bind(@,@[<v 2>%t@],@,@[<v 2>%t@]@;<0 -2>)" (print_term false t)
    (print_abstraction a)

and print_abstraction (v, t) ppf =
  print ppf "%t => %t" (print_variable v) (print_function_body t)

and print_abstraction2 (v1, v2, t) ppf =
  print ppf "(%t, %t) => %t" (print_variable v1) (print_variable v2)
    (print_function_body t)

and print_function_body t ppf =
  match t with
  | Sequence _ -> print ppf "{@,@[<v 2>%t@]@;<0 -2>}" @@ print_term true t
  | _ -> print_term false t ppf

and print_apply t1 t2 ppf =
  print ppf "%t(%t)" (print_term false t1) (print_term false t2)

and print_handle t1 t2 ppf =
  print ppf "eval(@,@[<v 2>%t@],@,@[<v 2>%t@]@;<0 -2>)" (print_term false t1)
    (print_term false t2)

and print_handler { effect_clauses; value_clause; finally_clause } ppf =
  print ppf "new Handler(@,@[<v 2>%t@],@,@[<v 2>%t@],@,@[<v 2>%t@]@;<0 -2>)"
    (print_handler_clauses effect_clauses)
    (print_abstraction value_clause)
    (print_abstraction finally_clause)

and print_handler_clauses hcs ppf =
  let print_handler_clause (effect, abs2) ppf =
    print ppf "@[<v 2>new HandlerClause(@,'%t',@,@[<v 2>%t@]@;<0 -2>)@]"
      (print_effect_label effect)
      (print_abstraction2 abs2)
  in
  print ppf "[@,%t@;<0 -2>]" @@ Print.sequence "," print_handler_clause hcs

and print_match return ms = Print.sequence "" (print_match_clause return) ms

and print_match_clause return (ps, (x, t)) ppf =
  print ppf "@[<v 2>if (%t.satisfies(%t)) {@,@[<v 2>%t@]@;<0 -2>}@]"
    (print_pattern_shape ps) (print_variable x) (print_term return t)

and print_pattern_shape p ppf =
  match p with
  | PArbitrary -> print ppf "new ArbitraryPattern()"
  | PConst c -> print ppf "new ConstantPattern(%t)" (print_constant c)
  | PTuple ps ->
      print ppf "new TuplePattern([@,%t@;<0 -2>])"
        (indented_sequence "," print_pattern_shape ps)
  | PRecord pa ->
      print ppf "new RecordPattern({@,%t@;<0 -2>})"
        (indented_sequence "," print_record_pattern_shape @@ Assoc.to_list pa)
  | PVariant (lbl, ps) -> (
      match ps with
      | Some shp ->
          print ppf "new VariantPattern('%t', [@,@[<v 2>%t@]@;<0 -2>])"
            (print_label lbl) (print_pattern_shape shp)
      | None -> print ppf "new VariantPattern('%t')" (print_label lbl))

and print_record_pattern_shape (f, ps) ppf =
  print ppf "%t: %t" (print_field f) (print_pattern_shape ps)

and print_projection_list m ps ppf =
  print ppf "@[<h>%t%t@]" (print_variable m)
    (Print.sequence "" print_projection ps)

and print_projection b ppf =
  match b with
  | Int i -> print ppf "[%d]" i
  | Field f -> print ppf ".%t" @@ print_field f
  | VariantProj -> print ppf ".arg"

and print_sequence return s ppf =
  match s with
  | [] -> ()
  | [ t ] -> print_term return t ppf
  | _ ->
      let n = List.length s in
      let returns_s = List.mapi (fun i t -> (i = n - 1, t)) s in
      if return then
        print ppf "@[<v>%t@]"
        @@ Print.sequence ";" (fun (return, t) -> print_term return t)
        @@ returns_s
      else
        print ppf "(() => {@,@[<v>%t@]@;<0 -2>})()"
        @@ Print.sequence ";" (fun (return, t) -> print_term return t)
        @@ returns_s

and print_comment c ppf = print ppf "/* %s */" c

let rec print_cmd cmd ppf =
  match cmd with
  | Term t -> print_cmd_term t ppf
  | TopLet ts -> print_cmd_top_let ts ppf
  | TopLetRec t -> print_cmd_top_let_rec t ppf
  | External (x, f) -> print_cmd_external x f ppf

and print_cmd_term t ppf =
  print ppf
    "@[<v 2>print(@,@[<v 2>top_eval(@,@[<v 2>%t@]@;<0 -2>)@]@]@;<0 -2>);@."
  @@ print_term false t

and print_cmd_top_let ts ppf =
  print ppf "%t@." (Print.sequence "" print_cmd_top_let_clause ts)

and print_cmd_top_let_clause (v, t, ts) ppf =
  print ppf "@[<v 2>const %t = top_eval(@,@[<v 2>%t@]@;<0 -2>);@;<0 -2>%t;@]@."
    (print_variable v) (print_term false t) (print_term true ts)

and print_cmd_top_let_rec ts ppf = print ppf "%t;@.@." @@ print_term true ts

and print_cmd_external x f ppf =
  match Assoc.lookup f External.values with
  | None -> Utils.Error.runtime "Unknown external symbol %s." f
  | Some known -> print ppf "const %t = %s;@." (print_variable x) known
