(** Type contexts

    Type contexts assign type schemes to variables, and are used for type
    inference. A type scheme consists of a type and a list of universally
    quantified type parameters.
*)

open Utils

type t = (Language.CoreTypes.Variable.t, Language.Type.ty_scheme) Assoc.t
(** The type of contexts. *)

val empty : t
(** [empty] is the empty context. *)

val lookup :
  t ->
  Language.CoreTypes.Variable.t ->
  Language.Term.expression * Language.Constraint.omega_ct list
(** [lookup ctx x] returns a fresh instance of the type scheme assigned
    to the variable [x] in the context [ctx]. *)

val update : t -> Language.CoreTypes.Variable.t -> Language.Type.ty_scheme -> t
(** [extend x ty_scheme ctx] returns the context [ctx] extended with
    a variable [x] bound to the type scheme [ty_scheme]. *)
