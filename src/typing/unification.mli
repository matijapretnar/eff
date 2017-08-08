(* Constraints
    There are two types of constraints, ty_constraints and dirt_constraints

    dirt_constraints are based on row polymorphism

    ty_constraints are based on parametric polymorphism
    They are used to find the principal solution
    A constraint set is a set of equations {S = T}
      This describes which types are equal
    A unification algorithm is used to determine the solution
*)

(********************)
(* TYPE DEFINITIONS *)
(********************)

(* Typing constraint *)
type ty_cnstr
(* Dirt constraint *)
type dirt_cnstr

(* A constraint set *)
type t

(*************************)
(* CONSTRAINT OPERATIONS *)
(*************************)

(* The empty graph. *)
val empty : t

(* Add a typing constraint: T = S *)
val add_ty_constraint : Type.ty -> Type.ty -> t -> t

(* Add a dirt constraint: ... *)
(* val add_dirt_constraint : *)

(* Add a dirty constraint: ... *)
(* val add_dirty_constraint : *)

(* Combine two constraint sets to a single set *)
val union : t -> t -> t

(* Combine mutliple constraint sets to a single set *)
val union_list : t list -> t

(* Unify the constraints to find a solution *)
val unify : t -> t

(* Perform a substitution *)
val subst : Params.substitution -> t -> t

(***********************)
(* PRINTING OPERATIONS *)
(***********************)

(* Print constraints *)
val print : t -> Format.formatter -> unit
