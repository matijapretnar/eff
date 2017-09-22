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

(* typing constraint *)
type ty_cnstr

(* dirt constraint *)
type dirt_cnstr

(* a constraint set *)
type t

(*************************)
(* CONSTRAINT OPERATIONS *)
(*************************)

(* the empty graph. *)
val empty : t

(* add a typing constraint: T = S *)
val add_ty_constraint : Type.ty -> Type.ty -> t -> t

(* add a dirt constraint: ... *)
val add_dirt_constraint : Type.dirt -> Type.dirt -> t -> t

(* add a dirty constraint: ... *)
val add_dirty_constraint : Type.dirty -> Type.dirty -> t -> t

(* combine two constraint sets to a single set *)
val union : t -> t -> t

(* combine mutliple constraint sets to a single set *)
val union_list : t list -> t

(* unify the constraints to find a solution *)
val unify : t -> t

(* perform a substitution *)
val subst : Params.substitution -> t -> t

val list_union : t list -> t

(***********************)
(* PRINTING OPERATIONS *)
(***********************)

(* print constraints *)
val print : t -> Format.formatter -> unit
