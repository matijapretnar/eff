(* Represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) Common.assoc

(* Represents a generic scheme *)
type 'a t = context * 'a * Unification.t

(* Type scheme for expressions *)
type ty_scheme = Type.ty t
(* Type scheme for computations *)
type dirty_scheme = Type.dirty t
(* Type scheme for letrec, call, match, bind *)
type abstraction_scheme = (Type.ty * Type.dirty) t
(* Type scheme for effect clauses *)
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t

(* Refresh a type scheme *)
val refresh : ty_scheme -> ty_scheme

(* Make a simple (empty) type scheme *)
val simple : 'a -> 'a t

(* Add a variable to the type scheme context *)
val add_to_context : Untyped.variable -> Type.ty -> ty_scheme -> ty_scheme

(* Get the type from a type scheme *)
val get_type : ty_scheme -> Type.ty

(* Make a type scheme for an abstraction *)
val abstract : loc:Location.t -> ty_scheme -> dirty_scheme -> abstraction_scheme
