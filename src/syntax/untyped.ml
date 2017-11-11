(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type effect = OldUtils.effect

type 'term annotation = {
  term: 'term;
  location: Location.t;
}

let annotate t loc = {
  term = t;
  location = loc;
}

type pattern = plain_pattern annotation
and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (OldUtils.field, pattern) OldUtils.assoc
  | PVariant of OldUtils.label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure expressions *)
type expression = plain_expression annotation
and plain_expression =
  | Var of variable
  | Const of Const.t
  | Tuple of expression list
  | Record of (OldUtils.field, expression) OldUtils.assoc
  | Variant of OldUtils.label * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler

(** Impure computations *)
and computation = plain_computation annotation
and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Handle of expression * computation

(** Handler definitions *)
and handler = {
  effect_clauses : (effect, abstraction2) OldUtils.assoc;
  value_clause : abstraction option;
  finally_clause : abstraction option;
}

(** Abstractions that take one argument. *)
and abstraction = pattern * computation

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * computation


let annotate t loc = {
  term = t;
  location = loc;
}

let return_term t = 
    t.term

(* Toplevel commands (the first four do not need to be separated by [;;]) *)
type toplevel = plain_toplevel annotation
and plain_toplevel =
  | Tydef of (OldUtils.tyname, Params.t * Tctx.tydef) OldUtils.assoc
  (** [type t = tydef] *)
  | TopLet of (pattern * computation) list
  (** [let p1 = t1 and ... and pn = tn] *)
  | TopLetRec of (variable * abstraction) list
  (** [let rec f1 p1 = t1 and ... and fn pn = tn] *)
  | External of variable * Type.ty * string
  (** [external x : t = "ext_val_name"] *)
  | DefEffect of effect * (Type.ty * Type.ty)
  (** [effect Eff : ty1 -> t2] *)
  | Computation of computation
  | Use of string
  (** [#use "filename.eff"] *)
  | Reset
  (** [#reset] *)
  | Help
  (** [#help] *)
  | Quit
  (** [#quit] *)
  | TypeOf of computation
  (** [#type t] *)
