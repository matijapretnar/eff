(** Type contexts

    Type contexts assign type schemes to variables, and are used for type
    inference. A type scheme consists of a type and a list of universally
    quantified type parameters.
*)

(** The type of contexts. *)
type t = (Typed.variable, Types.target_ty) Assoc.t

val empty : t
(** [empty] is the empty context. *)

val lookup : t -> Typed.variable -> Types.target_ty option
(** [lookup ctx x] returns a fresh instance of the type scheme assigned
    to the variable [x] in the context [ctx]. *)

val update : t -> Typed.variable -> Types.target_ty -> t
(** [extend x ty_scheme ctx] returns the context [ctx] extended with
    a variable [x] bound to the type scheme [ty_scheme]. *)

val return_context : t -> (Typed.variable * Types.target_ty) list

val apply_sub : t -> Substitution.t -> t
