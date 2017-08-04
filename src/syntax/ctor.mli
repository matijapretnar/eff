(* This file contains all smartconstructors for the typed terms *)

(* Expressions *)
(* smart constructor for the Const term : expression *)
val const : ?loc:Location.t -> Const.t -> Typed.expression


(* Computations *)
val value : ?loc:Location.t -> Typed.expression -> Typed.computation

(* Toplevel computations *)

(* Patterns *)
