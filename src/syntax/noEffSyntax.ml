(** Syntax of the NoEff language **)

module Variable = Symbol.Make (Symbol.String)

type variable = Variable.t

type n_effect = CoreTypes.Effect.t

type n_term =
  | NVar of variable
  | NTuple of n_term list
  | NFun of n_abstraction_with_type 
  | NApplyTerm of n_term * n_term
  | NBigLambdaTy of CoreTypes.TyParam.t * n_term
  | NTyAppl of n_term * n_type
  | NBigLambdaCoer of CoreTypes.TyCoercionParam.t * n_coerty * n_term
  | NApplyCoer of n_term * n_coercion
  | NCast of n_term * n_coercion
  | NReturn of n_term
  | NHandler of n_handler
  | NLet of n_term * n_term * n_term
  | NCall of n_effect * n_term * n_abstraction_with_type
  | NBind of n_term * (n_abstraction)
  | NHandle of n_term * n_term

and n_handler = 
  { effect_clauses: (n_effect, n_abstraction_2_args) Assoc.t
  ; return_clause: n_abstraction_with_type }

and n_type = 
  | NTyParam of CoreTypes.TyParam.t
  | NTyTuple of n_type list
  | NTyArrow of n_type * n_type
  | NTyHandler of n_type * n_type
  | NTyQual of n_coerty * n_type
  | NTyComp of n_type
  | NTyForall of CoreTypes.TyParam.t * n_type

and n_abstraction = (n_term * n_term)
and n_abstraction_with_type = (n_term * n_type * n_term)
and n_abstraction_2_args = (n_term * n_term * n_term)

and n_coerty = n_type * n_type

and n_coercion =
  | NCoerVar of CoreTypes.TyCoercionParam.t
  | NCoerRefl of n_type
  | NCoerArrow of n_coercion * n_coercion
  | NCoerHandler of n_coercion * n_coercion
  | NCoerHandToFun of n_coercion * n_coercion
  | NCoerFunToHand of n_coercion * n_coercion
  | NCoerForall of CoreTypes.TyParam.t * n_coercion
  | NCoerQual of n_coerty * n_coercion
  | NCoerComp of n_coercion
  | NCoerReturn of n_coercion
  | NCoerUnsafe of n_coercion
  | NCoerApp of n_coercion * n_coercion
  | NCoerInst of n_coercion * n_type
  | NCoerTrans of n_coercion * n_coercion
  (* STIEN: Might have to add more left-cases here later *)
  | NCoerLeftArrow of n_coercion
  | NCoerLeftHandler of n_coercion
  | NCoerPure of n_coercion
