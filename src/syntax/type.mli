val fresh_ty_param : unit -> CoreTypes.TyParam.t

type ty =
  | Apply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | Basic of Const.ty
  | Tuple of ty list
  | Arrow of ty * ty
  | Handler of handler_ty

and handler_ty = { value : ty; finally : ty }

val int_ty : ty

val string_ty : ty

val bool_ty : ty

val float_ty : ty

val unit_ty : ty

val empty_ty : ty

type substitution = (CoreTypes.TyParam.t, ty) Assoc.t

val subst_ty : substitution -> ty -> ty
(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)

val identity_subst : substitution
(** [identity_subst] is a substitution that makes no changes. *)

val compose_subst : substitution -> substitution -> substitution
(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)

(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)

val free_params : ty -> CoreTypes.TyParam.t list

val occurs_in_ty : CoreTypes.TyParam.t -> ty -> bool
(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)

val fresh_ty : unit -> ty
(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)

val refreshing_subst :
  CoreTypes.TyParam.t list -> CoreTypes.TyParam.t list * substitution

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)

val refresh : CoreTypes.TyParam.t list -> ty -> CoreTypes.TyParam.t list * ty

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)

val beautify : CoreTypes.TyParam.t list * ty -> CoreTypes.TyParam.t list * ty

val beautify2 :
  ty -> ty -> (CoreTypes.TyParam.t list * ty) * (CoreTypes.TyParam.t list * ty)

val print : CoreTypes.TyParam.t list * ty -> Format.formatter -> unit

val print_beautiful : CoreTypes.TyParam.t list * ty -> Format.formatter -> unit
