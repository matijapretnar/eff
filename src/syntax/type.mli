
val fresh_ty_param : unit -> Params.Ty.t

type ty =
  | Apply of CoreTypes.TyName.t * ty list
  | TyParam of Params.Ty.t
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * ty
  | Handler of handler_ty

and handler_ty = {value: ty; finally: ty}

val universal_ty : ty

val int_ty : ty

val string_ty : ty

val bool_ty : ty

val float_ty : ty

val unit_ty : ty

val empty_ty : ty

type substitution = (Params.Ty.t, ty) Assoc.t

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
val subst_ty : substitution -> ty -> ty

(** [identity_subst] is a substitution that makes no changes. *)
val identity_subst : substitution

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
val compose_subst : substitution -> substitution -> substitution


(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)

val free_params : ty -> Params.Ty.t list

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
val occurs_in_ty : Params.Ty.t -> ty -> bool

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
val fresh_ty : unit -> ty

val refreshing_subst : Params.Ty.t list -> Params.Ty.t list * substitution

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)

val refresh : Params.Ty.t list -> ty -> Params.Ty.t list * ty


(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)

val beautify : Params.Ty.t list * ty -> Params.Ty.t list * ty

val beautify2 : ty -> ty -> (Params.Ty.t list * ty) * (Params.Ty.t list * ty)

val print :  Params.Ty.t list * ty -> Format.formatter -> unit

val print_beautiful : Params.Ty.t list * ty -> Format.formatter -> unit
