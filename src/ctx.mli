(** Type contexts

    Type contexts assign type schemes to variables, and are used for type
    inference. A type scheme consists of a type and a list of universally
    quantified type parameters.
*)

(** The types of contexts and type schemes. *)
type ty_scheme = Type.params * Type.ty * Type.constraints list

type t

(** [empty] is the empty context. *)
val empty : t

(** [lookup ctx x] returns a fresh instance of the type scheme assigned
    to the variable [x] in the context [ctx]. *)
val lookup : t -> Common.variable -> ty_scheme option

(** [extend x ty_scheme ctx] returns the context [ctx] extended with
    a variable [x] bound to the type scheme [ty_scheme]. *)
val extend : t -> Common.variable -> ty_scheme -> t

(** [extend_ty x ty ctx] returns the context [ctx] extended with a variable [x]
    bound to the type [ty]. The type is promoted to a type scheme with no
    generalized type parameters. *)
val extend_ty : t -> Common.variable -> Type.ty -> t

(** [subst_ctx sbst ctx] returns a substitution of [ctx] under [sbst]. *)
val subst_ctx : t -> Type.substitution -> t

(** [generalize ctx poly ty] generalizes the type [ty] in context [ctx] to a
    type scheme. If [poly] is [true], all free type parameters in [ty] that do
    not appear in [ctx] are universally quantified. *)
val generalize : t -> bool -> Type.ty -> Type.constraints list -> ty_scheme
