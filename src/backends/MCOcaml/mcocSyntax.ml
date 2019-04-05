(** Syntax of the core language. *)
open CoreUtils
module CoreSyntax = UntypedSyntax

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

type pattern =
  | PVar of variable
  | PAnnotated of pattern * Type.ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (field, pattern) Assoc.t
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure expressions *)
type term = 
  | Var of variable
  | Const of Const.t
  | Annotated of term * Type.ty
  | Tuple of term list
  | Record of (field, term) Assoc.t
  | Variant of label * term option
  | Lambda of abstraction
  | Effect of effect
  | Let of (pattern * term) list * term
  | LetRec of (variable * abstraction) list * term
  | Match of term * match_case list
  | Apply of term * term

and match_case =
  | ValueCase of variable * abstraction
  | EffectCase of effect * abstraction2

(** Abstractions that take one argument. *)
and abstraction = pattern * term

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * term

(** Types used by MCOcaml. *)
type ty =
  | Apply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * ty

type tydef =
  | Record of (CoreTypes.Field.t, ty) Assoc.t
  | Sum of (CoreTypes.Label.t, ty option) Assoc.t
  | Inline of ty

let of_computation c = failwith "TODO"

let of_pattern p = failwith "TODO"

let of_type ty = failwith "TODO"

let of_tydef tydef = failwith "TODO"