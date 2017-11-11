(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type effect = OldUtils.effect * (Type.ty * Type.ty)

type ('term, 'scheme) annotation = {
  term: 'term;
  scheme: 'scheme;
  location: Location.t;
}

type pattern = (plain_pattern, Scheme.ty_scheme) annotation
and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (OldUtils.field, pattern) OldUtils.assoc
  | PVariant of OldUtils.label * pattern option
  | PConst of Const.t
  | PNonbinding

let rec pattern_vars p =
  match p.term with
  | PVar x -> [x]
  | PAs (p,x) -> x :: pattern_vars p
  | PTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
  | PRecord lst -> List.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
  | PVariant (_, None) -> []
  | PVariant (_, Some p) -> pattern_vars p
  | PConst _ -> []
  | PNonbinding -> []

let annotate t sch loc = {
  term = t;
  scheme = sch;
  location = loc;
}

(** Pure expressions *)
type expression = (plain_expression, Scheme.ty_scheme) annotation
and plain_expression =
  | Var of variable
  | BuiltIn of string * int
  | Const of Const.t
  | Tuple of expression list
  | Record of (OldUtils.field, expression) OldUtils.assoc
  | Variant of OldUtils.label * expression option
  | Effect of effect
  | Handler of handler
  | Lambda of abstractionLambda
  | BigLambdaTy of abstractionType
  | ApplyTy of expression * Type.ty

(** Impure computations *)
and computation = (plain_computation, Scheme.dirty_scheme) annotation
and plain_computation =
  | Value of expression
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  (* | TyApple of expression * target_ty *)
  | Handle of expression * computation
  | Call of effect * expression * abstraction
  | Bind of computation * abstraction

(** Handler definitions *)
and handler = {
  effect_clauses : (effect, abstraction2) OldUtils.assoc;
  value_clause : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation, Scheme.abstraction_scheme) annotation

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation, Scheme.abstraction2_scheme) annotation

(** Abstractions that take one argument but is typed. *)
and abstractionLambda = (pattern * Type.ty * computation)

(** Abstraction that take one *type* argument. **)
and abstractionType = (Params.ty_param * expression)

type toplevel = plain_toplevel * Location.t
and plain_toplevel =
  | Tydef of (OldUtils.tyname, Params.t * Tctx.tydef) OldUtils.assoc
  | TopLet of (pattern * computation) list * (variable * Scheme.ty_scheme) list
  | TopLetRec of (variable * abstraction) list * (variable * Scheme.ty_scheme) list
  | External of variable * Type.ty * string
  | DefEffect of effect * (Type.ty * Type.ty)
  | Computation of computation
  | Use of string
  | Reset
  | Help
  | Quit
  | TypeOf of computation
