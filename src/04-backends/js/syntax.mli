open Utils
open Language

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

val print_cmd : cmd -> Format.formatter -> unit
