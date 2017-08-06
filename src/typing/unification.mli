(* Constraints
    There are two types of constraints, ty_constraints and dirt_constraints

    dirt_constraints are based on row polymorphism

    ty_constraints are based on parametric polymorphism
    They are used to find the principal solution
    A constraint set is a set of equations {S = T}
      This describes which types are equal
    A unification algorithm is used to determine the solution
*)

type t

(** The empty graph. *)
val empty : t

(* Combine two constraint sets to a single set *)
val union : t -> t -> t
