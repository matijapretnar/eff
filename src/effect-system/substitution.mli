(** 
Substitutions 

Holds substitutions
*)

type t

val empty : t
(** Empty substitutions *)

(* Adding and merging *)

val add_type_coercion :
  CoreTypes.TyCoercionParam.t -> Typed.ty_coercion -> t -> t
(** [add_type_coercion parameter t_coercion sub] Add type [parameter] [t_coercion] to [sub]. *)

val add_type_coercion_e : CoreTypes.TyCoercionParam.t -> Typed.ty_coercion -> t
(** [add_type_coercion_e parameter t_coercion] Add type [parameter] [t_coercion] to empty substitution. *)

val add_type_substitution : CoreTypes.TyParam.t -> Types.target_ty -> t -> t
(** [add_type_substitution parameter target_type sub] Add type [parameter] to [target_type] substitution to [sub] *)

val add_type_substitution_e : CoreTypes.TyParam.t -> Types.target_ty -> t
(** [add_type_substitution_e parameter target_type] Add type [parameter] to [target_type] substitution to empty substitution *)

val add_dirt_var_coercion :
  CoreTypes.DirtCoercionParam.t -> Typed.dirt_coercion -> t -> t
(** [add_dirt_var_coercion dirt_var target_dc sub] Add [dirt_var] to target dirt coercion ([target_dc]) to [sub] *)

val add_dirt_var_coercion_e :
  CoreTypes.DirtCoercionParam.t -> Typed.dirt_coercion -> t
(** [add_dirt_var_coercion dirt_var target_dc] Add [dirt_var] to target dirt coercion ([target_dc]) to empty substitution *)

val add_dirt_substitution : CoreTypes.DirtParam.t -> Types.dirt -> t -> t
(** [add_dirt_substitution var target_dirt sub] Add dirt variable ([dirt_var]) to [target_dirt] substitution to [sub] *)

val add_dirt_substitution_e : CoreTypes.DirtParam.t -> Types.dirt -> t
(** [add_dirt_substitution var target_dirt] Add dirt variable ([dirt_var]) to [target_dirt] substitution to empty substitution *)

val add_skel_param_substitution :
  CoreTypes.SkelParam.t -> Types.skeleton -> t -> t
(** [add_type_substitution parameter target_skel sub] Add skeleton [parameter] to [target_skel] substitution to [sub] *)

val add_skel_param_substitution_e : CoreTypes.SkelParam.t -> Types.skeleton -> t
(** [add_type_substitution parameter target_skel sub] Add skeleton [parameter] to [target_skel] substitution to empty substitution *)

val merge : t -> t -> t
(** [merge subs1 subs2] Combines substitutions from [subs1] and [subs2]. In case of substitution conflicts, the results are unspecified *)

(* Substitution application *)

val apply_substitutions_to_constraints :
  t -> Typed.omega_ct list -> Typed.omega_ct list
(** [apply_substitutions_to_constraints subs constraints] Applies all substitutions from [subs] to [constraints] *)

val apply_substitutions_to_computation :
  t -> Typed.computation -> Typed.computation
(** [apply_substitutions_to_computation subs computation] Applies all substitutions from [subs] to [computation] *)

val apply_substitutions_to_expression :
  t -> Typed.expression -> Typed.expression
(** [apply_substitutions_to_expression subs expression] Applies all substitutions from [subs] to [expression] *)

val apply_substitutions_to_type : t -> Types.target_ty -> Types.target_ty
(** [apply_substitutions_to_type subs ty] Applies all substitutions from [subs] to [ty]pe *)

val apply_substitutions_to_dirt : t -> Types.dirt -> Types.dirt
(** [apply_substitutions_to_dirt subs dirt] Applies all substitutions from [subs] to [dirt] *)

val apply_substitutions_to_skeleton : t -> Types.skeleton -> Types.skeleton
(** [apply_substitutions_to_skeleton subs skeleton] Applies all substitutions from [subs] to [skeleton] *)

val apply_substitutions_to_tycoer : t -> Typed.ty_coercion -> Typed.ty_coercion
(** [apply_substitutions_to_tycoer sub ty_coer] Applies all substitutions from [subs] to [ty_coer] *)

(* Other type information *)

(* Printing and other debug helpers *)

val print_substitutions : t -> unit
(** [print_substitutions subs] Prints [subs] *)
