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

(* Combine two constraint sets to a single set *)
val union : t -> t -> t

(* Print constraints *)
val print : t -> Format.formatter -> unit
