
type ty =
  | TyVar of CoreTypes.TyParam.t
  | TyApply of CoreTypes.TyName.t * ty list
  | TyTuple of ty list
  | TyBasic of Const.ty
  | TyArrow of ty * ty
  | TyHandler of ty * ty
  | TyForAll of CoreTypes.TyParam.t * ty
  | TyQualification of ty_coercion * ty
  | TyComputation of ty

and ty_coercion = 
  | TyCoercion of ty * ty

type effect = CoreTypes.Effect.t * (ty * ty)

type variable = CoreTypes.Variable.t

type pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (CoreTypes.Field.t, pattern) Assoc.t
  | PVariant of CoreTypes.Label.t * pattern
  | PConst of Const.t
  | PNonbinding

type term = 
  | Var of variable
  | BuiltIn of string * int
  | Const of Const.t
  | Tuple of term list
  | Record of (CoreTypes.Field.t, term) Assoc.t
  | Variant of CoreTypes.Label.t * term
  | Lambda of abstraction_with_ty
  | Effect of effect
  | Apply of term * term
  | BigLambdaTy of CoreTypes.TyParam.t * term
  | ApplyTy of term * ty
  | BigLambdaCoerVar of CoreTypes.TyCoercionParam.t * ty_coercion * term
  | ApplyCoercion of term * coercion
  | Cast of term * coercion
  | Return of term
  | Handler of handler
  | Let of variable * term * term
  | Call of effect * term * abstraction_with_ty
  | Op of effect * term
  | Do of variable * term * term
  | Handle of term * term

and handler = 
  { effect_clauses: (effect, abstraction2) Assoc.t
  ; value_clause: abstraction_with_ty }

and abstraction_with_ty = pattern * ty * term

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * term)

and coercion = 
  | CoerVar of CoreTypes.TyCoercionParam.t
  | ReflTy of ty
  | ReflVar of CoreTypes.TyParam.t
  | CoerArrow of coercion * coercion
  | CoerHandler of coercion * coercion
  | HandToFun of coercion * coercion
  | FunToHand of coercion * coercion
  | Forall of CoreTypes.TyParam.t * coercion
  | CoerQualification of ty_coercion * coercion
  | CoerComputation of coercion
  | CoerReturn of coercion
  | Unsafe of coercion
