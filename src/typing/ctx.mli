(** Type contexts

    Type contexts assign type schemes to variables, and are used for type
    inference. A type scheme consists of a type and a list of universally
    quantified type parameters.
*)

(** The type of contexts. *)
type t

(** [empty] is the empty context. *)
val empty : t

(** [lookup ctx x] returns a fresh instance of the type scheme assigned
    to the variable [x] in the context [ctx]. *)
val lookup : t -> Syntax.variable -> Scheme.ty_scheme option

(** [extend x ty_scheme ctx] returns the context [ctx] extended with
    a variable [x] bound to the type scheme [ty_scheme]. *)
val extend : t -> Syntax.variable -> Scheme.ty_scheme -> t
