(********************)
(* TYPE DEFINITIONS *)
(********************)

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

(*************************)
(* INTERFACE DEFINITIONS *)
(*************************)

(* Make a simple (empty) type scheme *)
val simple : 'a -> 'a t

(* Add a variable to the type scheme context *)
val add_to_context : Untyped.variable -> Type.ty -> ty_scheme -> ty_scheme

(* Get the type from a type scheme *)
val get_type : ty_scheme -> Type.ty

(* Makes a scheme dirty *)
val make_dirty : ty_scheme -> dirty_scheme

(* Refresh a type scheme *)
val refresh : ty_scheme -> ty_scheme

(* Make a type scheme for an abstraction *)
val abstract : loc:Location.t -> ty_scheme -> dirty_scheme -> abstraction_scheme

(**********************)
(* SMART CONSTRUCTORS *)
(**********************)

(* Create a scheme for a variable expression *)
val var : Untyped.variable -> Type.ty -> ty_scheme

(* Create a scheme for a Lambda expression *)
val lambda : loc:Location.t -> ty_scheme -> dirty_scheme -> ty_scheme
