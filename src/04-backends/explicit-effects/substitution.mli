(**
Substitutions

Holds substitutions
*)

module CoreTypes = Language.CoreTypes

type t

val empty : t
(** Empty substitutions *)

(* Adding and merging *)

val add_type_coercion :
  Type.TyCoercionParam.t -> Constraint.ty_coercion -> t -> t
(** [add_type_coercion parameter t_coercion sub] Add type [parameter] [t_coercion] to [sub]. *)

val add_type_coercion_e : Type.TyCoercionParam.t -> Constraint.ty_coercion -> t
(** [add_type_coercion_e parameter t_coercion] Add type [parameter] [t_coercion] to empty substitution. *)

val add_type_substitution : CoreTypes.TyParam.t -> Type.ty -> t -> t
(** [add_type_substitution parameter ty sub] Add type [parameter] to [ty] substitution to [sub] *)

val add_type_substitution_e : CoreTypes.TyParam.t -> Type.ty -> t
(** [add_type_substitution_e parameter ty] Add type [parameter] to [ty] substitution to empty substitution *)

val add_dirt_var_coercion :
  Type.DirtCoercionParam.t -> Constraint.dirt_coercion -> t -> t
(** [add_dirt_var_coercion dirt_var dc sub] Add [dirt_var] to target dirt coercion ([dc]) to [sub] *)

val add_dirt_var_coercion_e :
  Type.DirtCoercionParam.t -> Constraint.dirt_coercion -> t
(** [add_dirt_var_coercion dirt_var dc] Add [dirt_var] to target dirt coercion ([dc]) to empty substitution *)

val add_dirt_substitution : Type.DirtParam.t -> Type.dirt -> t -> t
(** [add_dirt_substitution var dirt sub] Add dirt variable ([dirt_var]) to [dirt] substitution to [sub] *)

val add_dirt_substitution_e : Type.DirtParam.t -> Type.dirt -> t
(** [add_dirt_substitution var dirt] Add dirt variable ([dirt_var]) to [dirt] substitution to empty substitution *)

val add_skel_param_substitution : Type.SkelParam.t -> Type.skeleton -> t -> t
(** [add_type_substitution parameter skel sub] Add skeleton [parameter] to [skel] substitution to [sub] *)

val add_skel_param_substitution_e : Type.SkelParam.t -> Type.skeleton -> t
(** [add_type_substitution parameter skel sub] Add skeleton [parameter] to [skel] substitution to empty substitution *)

val merge : t -> t -> t
(** [merge subs1 subs2] Combines substitutions from [subs1] and [subs2]. In case of substitution conflicts, the results are unspecified *)

(* Substitution application *)

val apply_substitutions_to_constraints :
  t -> Constraint.omega_ct list -> Constraint.omega_ct list
(** [apply_substitutions_to_constraints subs constraints] Applies all substitutions from [subs] to [constraints] *)

val apply_substitutions_to_computation :
  t -> Term.computation -> Term.computation
(** [apply_substitutions_to_computation subs computation] Applies all substitutions from [subs] to [computation] *)

val apply_substitutions_to_expression : t -> Term.expression -> Term.expression
(** [apply_substitutions_to_expression subs expression] Applies all substitutions from [subs] to [expression] *)

val apply_substitutions_to_abstraction :
  t -> Term.abstraction -> Term.abstraction
(** [apply_substitutions_to_expression subs expression] Applies all substitutions from [subs] to [expression] *)

val apply_substitutions_to_type : t -> Type.ty -> Type.ty
(** [apply_substitutions_to_type subs ty] Applies all substitutions from [subs] to [ty]pe *)

val apply_substitutions_to_dirt : t -> Type.dirt -> Type.dirt
(** [apply_substitutions_to_dirt subs dirt] Applies all substitutions from [subs] to [dirt] *)

val apply_substitutions_to_skeleton : t -> Type.skeleton -> Type.skeleton
(** [apply_substitutions_to_skeleton subs skeleton] Applies all substitutions from [subs] to [skeleton] *)

val apply_sub_tycoer : t -> Constraint.ty_coercion -> Constraint.ty_coercion
(** [apply_sub_tycoer subs co] Applies all substitutions from [subs] to [co] *)

val apply_sub_dirtcoer :
  t -> Constraint.dirt_coercion -> Constraint.dirt_coercion
(** [apply_sub_dirtcoer subs co] Applies all substitutions from [subs] to [co] *)

val apply_sub_dirtycoer :
  t -> Constraint.dirty_coercion -> Constraint.dirty_coercion
(** [apply_sub_dirtycoer subs co] Applies all substitutions from [subs] to [co] *)

(* Other type information *)

(* Printing and other debug helpers *)

val print_substitutions : t -> Format.formatter -> unit
(** [print_substitutions subs] Prints [subs] *)

val apply_sub_definitions : t -> Term.rec_definitions -> Term.rec_definitions
