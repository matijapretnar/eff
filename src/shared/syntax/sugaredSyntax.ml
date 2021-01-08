open Utils
open Language
open CoreUtils

(** Abstract syntax of eff terms, types, and toplevel commands. *)

type variable = string
(** Terms *)

type effect = string

type label = string

type field = string

type tyname = string

type typaram = string

type dirtparam = int

type ty = plain_ty located

and plain_ty =
  | TyApply of tyname * ty list  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of typaram  (** ['a] *)
  | TyArrow of ty * ty  (** [ty1 -> ty2] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)
  | TyHandler of ty * ty  (** [ty1 => ty2] *)

type tydef =
  | TyRecord of (field, ty) Assoc.t
      (** [{ field1 : ty1; field2 : ty2; ...; fieldn : tyn }] *)
  | TySum of (label, ty option) Assoc.t
      (** [Label1 of ty1 | Label2 of ty2 | ... | Labeln of tyn | Label' | Label''] *)
  | TyInline of ty  (** [ty] *)

type pattern = plain_pattern located

and plain_pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (field, pattern) Assoc.t
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(* Changing the datatype [plain_pattern] will break [specialize_vector] in [exhaust.ml] because
   of wildcard matches there. *)

type term = plain_term located

and plain_term =
  | Var of variable  (** variables *)
  | Const of Const.t  (** integers, strings, booleans, and floats *)
  | Annotated of term * ty
  | Tuple of term list  (** [(t1, t2, ..., tn)] *)
  | Record of (field, term) Assoc.t
      (** [{field1 = t1; field2 = t2; ...; fieldn = tn}] *)
  | Variant of label * term option  (** [Label] or [Label t] *)
  | Lambda of abstraction  (** [fun p1 p2 ... pn -> t] *)
  | Function of abstraction list  (** [function p1 -> t1 | ... | pn -> tn] *)
  | Effect of effect * term  (** [eff], where [eff] is an effect symbol. *)
  | Handler of handler
      (** [handler clauses], where [clauses] are described below. *)
  | Let of (pattern * term) list * term
      (** [let p1 = t1 and ... and pn = tn in t] *)
  | LetRec of (variable * term) list * term
      (** [let rec f1 p1 = t1 and ... and fn pn = tn in t] *)
  | Match of term * match_case list
      (** [match t with p1 -> t1 | ... | pn -> tn] *)
  | Conditional of term * term * term  (** [if t then t1 else t2] *)
  | Apply of term * term  (** [t1 t2] *)
  | Handle of term * term  (** [with t1 handle t2] *)
  | Check of term  (** [check t] *)

and handler = {
  effect_clauses : (effect, abstraction2) Assoc.t;
      (** [t1#op1 p1 k1 -> t1' | ... | tn#opn pn kn -> tn'] *)
  value_clause : abstraction list;  (** [val p -> t] *)
  finally_clause : abstraction list;  (** [finally p -> t] *)
}

and match_case =
  | Val_match of abstraction
  | Eff_match of (effect * abstraction2)

and abstraction = pattern * term

and abstraction2 = pattern * pattern * term

type dirt = DirtParam of dirtparam
