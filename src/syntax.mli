(** Abstract syntax of eff terms, types, and toplevel commands. *)

(** Terms *)
type term = plain_term Common.pos
and plain_term =
  | Var of Common.variable
  (** variables *)
  | Const of Common.const
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
  | Operation of operation
  (** [t#op], where [op] is an operation symbol. *)
  | Handler of handler
  (** [handler clauses], where [clauses] are described below. *)

  | Let of (Common.variable Pattern.t * term) list * term
  (** [let p1 = t1 and ... and pn = tn in t] *)
  | LetRec of (Common.variable * term) list * term
  (** [let rec f1 p1 = t1 and ... and fn pn = tn in t] *)
  | Match of term * abstraction list
  (** [match t with p1 -> t1 | ... | pn -> tn] *)
  | Conditional of term * term * term
  (** [if t then t1 else t2] *)
  | While of term * term
  (** [while t1 do t2 done] *)
  | For of Common.variable * term * term * term * bool
  (** [for x = t1 to t2 do t done] or [for x = t1 downto t2 do t done] *)
  | Apply of term * term
  (** [t1 t2] *)
  | New of Common.tyname * resource option
  (** [new effect] or
      [new effect @ t with operation op1 x1 @ s1 -> t1 ... end] *)
  | Handle of term * term
  (** [with t1 handle t2] *)
  | Check of term
  (** [check t] *)

and handler = {
  operations : (operation, abstraction2) Common.assoc;
  (** [t1#op1 p1 k1 -> t1' | ... | tn#opn pn kn -> tn'] *)
  value : abstraction option;
  (** [val p -> t] *)
  finally : abstraction option;
  (** [finally p -> t] *)
}

and abstraction = Common.variable Pattern.t * term

and abstraction2 = Common.variable Pattern.t * Common.variable Pattern.t * term

and operation = term * Common.opsym

and resource = term * (Common.opsym, Common.variable Pattern.t * Common.variable Pattern.t * term) Common.assoc

type dirt =
  | DirtParam of Common.dirtparam

type region =
  | RegionParam of Common.regionparam

type ty = plain_ty Common.pos
and plain_ty =
  | TyApply of Common.tyname * ty list * (dirt list * region list) option * region option
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
  | TyEffect of (Common.opsym, ty * ty) Common.assoc
  (** [effect operation1 : ty1 -> ty1' ... operationn : tyn -> tyn' end] *)
  | TyInline of ty
  (** [ty] *)

(* Toplevel commands (the first four do not need to be separated by [;;]) *)
type toplevel = plain_toplevel Common.pos
and plain_toplevel =
  | Tydef of (Common.tyname, (Common.typaram list * tydef)) Common.assoc
  (** [type t = tydef] *)
  | TopLet of (Common.variable Pattern.t * term) list
  (** [let p1 = t1 and ... and pn = tn] *)
  | TopLetRec of (Common.variable * term) list
  (** [let rec f1 p1 = t1 and ... and fn pn = tn] *)
  | External of Common.variable * ty * Common.variable
  (** [external x : t = "ext_val_name"] *)
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

