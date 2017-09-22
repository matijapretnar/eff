(* This file contains all smartconstructors for the typed terms *)

val abstraction : ?loc:Location.t -> Typed.pattern -> Typed.computation -> Typed.abstraction

(**************************)
(* EXPRESSION CONSTRUCTORS*)
(**************************)

(* smart constructor for the Var term : expression *)
val var : ?loc:Location.t -> Typed.variable -> Scheme.ty_scheme -> Typed.expression

(* smart constructor for the Const term : expression *)
val const : ?loc:Location.t -> Const.t -> Typed.expression

(* smart constructor for the Lambda term : expression *)
val lambda : ?loc:Location.t -> Typed.pattern -> Typed.computation -> Typed.expression

(* smart constructor for the Tuple term : expression *)
val tuple : ?loc:Location.t -> Typed.expression list -> Typed.expression

(* val handler : ?loc:Location.t ->  *)

(* val effect : ?loc:Location.t ->  *)

(***************************)
(* COMPUTATION CONSTRUCTORS*)
(***************************)

(* value computation *)
val value : ?loc:Location.t -> Typed.expression -> Typed.computation

(* application computation *)
val apply : ?loc:Location.t -> Typed.expression -> Typed.expression -> Typed.computation

(* match computation *)
val patmatch : ?loc:Location.t -> Typed.expression -> Typed.abstraction list -> Typed.computation

(************************************)
(* TOPLEVEL COMPUTATION CONSTRUCTORS*)
(************************************)

(***********************)
(* PATTERN CONSTRUCTORS*)
(***********************)

(* Pattern variable *)
val pvar : ?loc:Location.t -> Typed.variable -> Typed.pattern

val pas : ?loc:Location.t -> Typed.pattern -> Typed.variable -> Typed.pattern

val pconst : ?loc:Location.t -> Const.t -> Typed.pattern

val ptuple : ?loc:Location.t -> Typed.pattern list -> Typed.pattern

val pnonbinding : ?loc:Location.t -> Typed.pattern
