(** Abstract syntax of eff terms, types, and toplevel commands. *)

(** Terms *)
type variable = string

type effect = OldUtils.effect

type 'var pattern = ('var plain_pattern * Location.t)

and 'var plain_pattern =
  | PVar of 'var
  | PAs of 'var pattern * 'var
  | PTuple of 'var pattern list
  | PRecord of (OldUtils.field * 'var pattern) list
  | PVariant of OldUtils.label * 'var pattern option
  | PConst of Const.t
  | PNonbinding

(* Changing the datatype [plain_pattern] will break [specialize_vector] in [exhaust.ml] because
   of wildcard matches there. *)

type term = (plain_term * Location.t)

and plain_term =
  | Var of variable  (** variables *)
  | Const of Const.t  (** integers, strings, booleans, and floats *)
  | Tuple of term list  (** [(t1, t2, ..., tn)] *)
  | Record of (OldUtils.field, term) OldUtils.assoc
      (** [{field1 = t1; field2 = t2; ...; fieldn = tn}] *)
  | Variant of OldUtils.label * term option  (** [Label] or [Label t] *)
  | Lambda of abstraction  (** [fun p1 p2 ... pn -> t] *)
  | Function of abstraction list  (** [function p1 -> t1 | ... | pn -> tn] *)
  | Effect of effect  (** [eff], where [eff] is an effect symbol. *)
  | Handler of handler
      (** [handler clauses], where [clauses] are described below. *)
  | Let of (variable pattern * term) list * term
      (** [let p1 = t1 and ... and pn = tn in t] *)
  | LetRec of (variable * term) list * term
      (** [let rec f1 p1 = t1 and ... and fn pn = tn in t] *)
  | Match of term * abstraction list
      (** [match t with p1 -> t1 | ... | pn -> tn] *)
  | Conditional of term * term * term  (** [if t then t1 else t2] *)
  | Apply of term * term  (** [t1 t2] *)
  | Handle of term * term  (** [with t1 handle t2] *)
  | Check of term  (** [check t] *)

and handler =
  { effect_clauses: (effect, abstraction2) OldUtils.assoc
        (** [t1#op1 p1 k1 -> t1' | ... | tn#opn pn kn -> tn'] *)
  ; value_clause: abstraction option  (** [val p -> t] *)
  ; finally_clause: abstraction option  (** [finally p -> t] *) }

and abstraction = (variable pattern * term)

and abstraction2 = (variable pattern * variable pattern * term)

type dirt = DirtParam of OldUtils.dirtparam

type region = RegionParam of OldUtils.regionparam

type ty = (plain_ty * Location.t)

and plain_ty =
  | TyApply of OldUtils.tyname * ty list
      (** [(ty1, ty2, ..., tyn) type_name] *)
  | TyParam of OldUtils.typaram  (** ['a] *)
  | TyArrow of ty * ty  (** [ty1 -> ty2] *)
  | TyTuple of ty list  (** [ty1 * ty2 * ... * tyn] *)
  | TyHandler of ty * ty  (** [ty1 => ty2] *)

type tydef =
  | TyRecord of (OldUtils.field, ty) OldUtils.assoc
      (** [{ field1 : ty1; field2 : ty2; ...; fieldn : tyn }] *)
  | TySum of (OldUtils.label, ty option) OldUtils.assoc
      (** [Label1 of ty1 | Label2 of ty2 | ... | Labeln of tyn | Label' | Label''] *)
  | TyInline of ty  (** [ty] *)

(* Toplevel commands (the first four do not need to be separated by [;;]) *)
type command = (plain_command * Location.t)

and plain_command =
  | Tydef of (OldUtils.tyname, OldUtils.typaram list * tydef) OldUtils.assoc
      (** [type t = tydef] *)
  | TopLet of (variable pattern * term) list
      (** [let p1 = t1 and ... and pn = tn] *)
  | TopLetRec of (variable * term) list
      (** [let rec f1 p1 = t1 and ... and fn pn = tn] *)
  | External of variable * ty * variable
      (** [external x : t = "ext_val_name"] *)
  | DefEffect of effect * (ty * ty)  (** [effect Eff : ty1 -> t2] *)
  | Term of term
  | Use of string  (** [#use "filename.eff"] *)
  | Reset  (** [#reset] *)
  | Help  (** [#help] *)
  | Quit  (** [#quit] *)
  | TypeOf of term  (** [#type t] *)
