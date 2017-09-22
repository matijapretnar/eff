(** Abstract syntax of eff terms, types, and toplevel commands. *)

(** Terms *)
type variable = string
type effect = Common.effect

type term = plain_term * Location.t
and plain_term =
  | Var of variable
  (** variables *)
  | Const of Const.t
  (** integers, strings, booleans, and floats *)
  | Tuple of term list
  (** [(t1, t2, ..., tn)] *)
  | Record of (Common.field, term) Common.assoc
  (** [{field1 = t1; field2 = t2; ...; fieldn = tn}] *)
  | Variant of Common.label * term option
  (** [Label] or [Label t] *)
  | Lambda of abstraction
  (** [fun p1 p2 ... pn -> t] *)
  | Function of abstraction list
  (** [function p1 -> t1 | ... | pn -> tn] *)
  | Effect of effect
  (** [eff], where [eff] is an effect symbol. *)
  | Handler of handler
  (** [handler clauses], where [clauses] are described below. *)

  | Let of (variable Pattern.t * term) list * term
  (** [let p1 = t1 and ... and pn = tn in t] *)
  | LetRec of (variable * term) list * term
  (** [let rec f1 p1 = t1 and ... and fn pn = tn in t] *)
  | Match of term * abstraction list
  (** [match t with p1 -> t1 | ... | pn -> tn] *)
  | Conditional of term * term * term
  (** [if t then t1 else t2] *)
  | Apply of term * term
  (** [t1 t2] *)
  | Handle of term * term
  (** [with t1 handle t2] *)

and handler = {
  effect_clauses : (effect, abstraction2) Common.assoc;
  (** [t1#op1 p1 k1 -> t1' | ... | tn#opn pn kn -> tn'] *)
  value_clause : abstraction option;
  (** [val p -> t] *)
  finally_clause : abstraction option;
  (** [finally p -> t] *)
}

and abstraction = variable Pattern.t * term

and abstraction2 = variable Pattern.t * variable Pattern.t * term

type dirt =
  | DirtParam of Common.dirtparam

type ty = plain_ty * Location.t
and plain_ty =
  | TyApply of Common.tyname * ty list * (dirt list) option
  (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of Common.typaram
  (** ['a] *)
  | TyArrow of ty * ty * dirt option
  (** [ty1 -> ty2] *)
  | TyTuple of ty list
  (** [ty1 * ty2 * ... * tyn] *)
  | TyHandler of ty * dirt option * ty * dirt option
  (** [ty1 => ty2] *)

type tydef =
  | TyRecord of (Common.field, ty) Common.assoc
  (** [{ field1 : ty1; field2 : ty2; ...; fieldn : tyn }] *)
  | TySum of (Common.label, ty option) Common.assoc
  (** [Label1 of ty1 | Label2 of ty2 | ... | Labeln of tyn | Label' | Label''] *)
  | TyInline of ty
  (** [ty] *)

(* Toplevel commands (the first four do not need to be separated by [;;]) *)
type toplevel = plain_toplevel * Location.t
and plain_toplevel =
  | Tydef of (Common.tyname, (Common.typaram list * tydef)) Common.assoc
  (** [type t = tydef] *)
  | TopLet of (variable Pattern.t * term) list
  (** [let p1 = t1 and ... and pn = tn] *)
  | TopLetRec of (variable * term) list
  (** [let rec f1 p1 = t1 and ... and fn pn = tn] *)
  | External of variable * ty * variable
  (** [external x : t = "ext_val_name"] *)
  | DefEffect of effect * (ty * ty)
  (** [effect Eff : ty1 -> t2] *)
  | Term of term
  | Use of string
  (** [#use "filename.eff"] *)
  | Reset
  (** [#reset] *)
  | Help
  (** [#help] *)
  | Quit
  (** [#quit] *)
  | TypeOf of term
  (** [#type t] *)
