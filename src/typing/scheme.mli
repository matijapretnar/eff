(********************)
(* TYPE DEFINITIONS *)
(********************)

(* represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) OldUtils.assoc

(* represents a generic scheme *)
type 'a t = context * 'a * Unification.t

(* type scheme for expressions *)
type ty_scheme = Type.ty t

(* type scheme for computations *)
type dirty_scheme = Type.dirty t

(* type scheme for letrec, call, match, bind *)
type abstraction_scheme = (Type.ty * Type.dirty) t

(* type scheme for effect clauses *)
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t


val just : Unification.t -> ty_scheme -> ty_scheme

val ty_cnstr : loc:Location.t -> Type.ty -> Type.ty -> ty_scheme -> ty_scheme

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

(******************)
(* SCHEME SOLVERS *)
(******************)

(* solve the type scheme *)
val solve_ty : ty_scheme -> ty_scheme

(* solve the dirty scheme *)
val solve_dirty : dirty_scheme -> dirty_scheme

(****************************)
(* ABSTRACTION CONSTRUCTORS *)
(****************************)

(* Make a type scheme for an abstraction *)
val abstract : loc:Location.t -> ty_scheme -> dirty_scheme -> abstraction_scheme

(* Make a type scheme for an abstraction *)
val abstract2 : loc:Location.t -> ty_scheme -> ty_scheme -> dirty_scheme -> abstraction2_scheme

(***************************)
(* EXPRESSION CONSTRUCTORS *)
(***************************)

(* Create a scheme for a variable expression *)
val var : loc:Location.t -> Untyped.variable -> Type.ty -> ty_scheme

(* create a scheme for a const *)
val const : loc:Location.t -> Const.t -> ty_scheme

(* Create a scheme for a Lambda expression *)
val lambda : loc:Location.t -> ty_scheme -> dirty_scheme -> ty_scheme

(* smart constructor for the Tuple term : expression *)
val tuple : loc:Location.t -> ty_scheme list -> ty_scheme

(* Create a scheme for an Effect *)
val effect : loc:Location.t -> Type.ty -> Type.ty -> Untyped.EffectMap.key -> ty_scheme

(* smart constructor for the handler term : expression *)
val handler : loc:Location.t -> ((OldUtils.effect * (Type.ty * Type.ty)) * abstraction2_scheme) list -> abstraction_scheme -> ty_scheme

(***************************)
(* COMPUTATION CONSTRUCTORS*)
(***************************)

val value : loc:Location.t -> ty_scheme -> dirty_scheme

val apply : loc:Location.t -> ty_scheme -> ty_scheme -> dirty_scheme

val patmatch : loc:Location.t -> ty_scheme -> abstraction_scheme list -> dirty_scheme

val handle : loc:Location.t -> ty_scheme -> dirty_scheme -> dirty_scheme

(************************)
(* PATTERN CONSTRUCTORS *)
(************************)

val pvar : loc:Location.t -> Untyped.variable -> ty_scheme

val pnonbinding : loc:Location.t -> unit -> ty_scheme

val pconst : loc:Location.t -> Const.t -> ty_scheme

val pas : loc:Location.t -> ty_scheme -> Untyped.variable -> ty_scheme

val ptuple : loc:Location.t -> ty_scheme list -> ty_scheme

val precord : loc:Location.t -> context -> Type.ty -> (ty_scheme -> ty_scheme) list -> ty_scheme

(**********************)
(* PRINTING UTILITIES *)
(**********************)

val print_ty_scheme : ty_scheme -> Format.formatter -> unit

val print_dirty_scheme : dirty_scheme -> Format.formatter -> unit
