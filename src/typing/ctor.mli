(* This file contains all smartconstructors for the typed terms *)

(****************************)
(* ABSTRACTION CONSTRUCTORS *)
(****************************)

val abstraction : ?loc:Location.t -> Typed.pattern -> Typed.computation -> Typed.abstraction

val abstraction2 : ?loc:Location.t -> Typed.pattern -> Typed.pattern -> Typed.computation -> Typed.abstraction2

(***************************)
(* EXPRESSION CONSTRUCTORS *)
(***************************)

(* smart constructor for the Var term : expression *)
val lambdavar : ?loc:Location.t -> Typed.variable -> Type.ty -> Typed.expression

(* smart constructor for the Const term : expression *)
val const : ?loc:Location.t -> Const.t -> Typed.expression

(* smart constructor for the Record term : expression *)
val record : ?loc:Location.t -> (OldUtils.field * Typed.expression) list -> Typed.expression

(* smart constructor for the Variant term : expression *)
val variant : ?loc:Location.t -> (OldUtils.label * Typed.expression option) -> Typed.expression

(* smart constructor for the Lambda term : expression *)
val lambda : ?loc:Location.t -> Typed.pattern -> Typed.computation -> Typed.expression

(* smart constructor for the Tuple term : expression *)
val tuple : ?loc:Location.t -> Typed.expression list -> Typed.expression

(* smart constructor for the effect term : expression *)
val effect : ?loc:Location.t ->  Typed.effect -> Typed.expression

(* smart constructor for the handler term : expression *)
val handler : ?loc:Location.t ->  (Typed.effect, Typed.abstraction2) OldUtils.assoc -> Typed.abstraction -> Typed.expression

(***************************)
(* COMPUTATION CONSTRUCTORS*)
(***************************)

(* value computation *)
val value : ?loc:Location.t -> Typed.expression -> Typed.computation

(* application computation *)
val apply : ?loc:Location.t -> Typed.expression -> Typed.expression -> Typed.computation

(* match computation *)
val patmatch : ?loc:Location.t -> Typed.expression -> Typed.abstraction list -> Typed.computation

val handle : ?loc:Location.t -> Typed.expression -> Typed.computation -> Typed.computation

(* val letbinding : ?loc:Location.t -> (Typed.pattern * Typed.computation) -> Typed.computation -> Typed.computation *)

(* val letrecbinding : ?loc:Location.t -> (Typed.variable * Typed.abstraction) -> Typed.computation -> Typed.computation *)

(*************************************)
(* TOPLEVEL COMPUTATION CONSTRUCTORS *)
(*************************************)

(************************)
(* PATTERN CONSTRUCTORS *)
(************************)

(* Pattern variable *)
val pvar : ?loc:Location.t -> Typed.variable -> Typed.pattern

val pnonbinding : ?loc:Location.t -> Typed.pattern

val pconst : ?loc:Location.t -> Const.t -> Typed.pattern

val pas : ?loc:Location.t -> Typed.pattern -> Typed.variable -> Typed.pattern

val ptuple : ?loc:Location.t -> Typed.pattern list -> Typed.pattern

val precord : ?loc:Location.t -> OldUtils.field -> (OldUtils.field * Typed.pattern) list -> Typed.pattern

val pvariant_none : ?loc:Location.t -> OldUtils.label -> Type.ty -> Typed.pattern

val pvariant_some : ?loc:Location.t -> OldUtils.label -> Type.ty -> Type.ty -> Typed.pattern -> Typed.pattern
