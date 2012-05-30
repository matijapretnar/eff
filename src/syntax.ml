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
  (** [Label] or [Label (t1, ..., tn)] *)
  | Lambda of abstraction
  (** [fun p1 p2 ... pn -> t] *)
  | Function of abstraction list
  (** [function p1 -> t1 | ... | pn -> tn] *)
  | Operation of operation
  (** [t#op], where [t] is an instance and [op] is an operation symbol. *)
  | Handler of handler
  (** [handler t1#op1 p1 k1 -> t1' | ... | val pv -> tv | finally pf -> tf] *)

  | Let of (Pattern.t * term) list * term
  (** [let p1 = t1 and ... and pn = tn in t] *)
  | LetRec of (Common.variable * term) list * term
  (** [let rec f1 p1 = t1 and ... and fn pn = tn in t] *)
  | Match of term * abstraction list
  (** [match t with p1 -> t1 | ... pn -> tn] *)
  | Conditional of term * term * term
  (** [if t then t1 else t2] *)
  | While of term * term
  (** [while t1 do t2 done] *)
  | For of Common.variable * term * term * term * bool
  (** [for x = t1 to t2 do t done] or [for x = t1 downto t2 do t done] *)
  | Apply of term * term
  (** [t1 t2] *)
  | New of Common.tyname * resource option
  (** [new effect] or [new effect @ t with op1 x1 @ s1 -> t1 | ... | end] *)
  | Handle of term * term
  (** [with t1 handle t2] *)
  | Check of term
  (** [check t] *)

and handler = {
  operations : (operation, abstraction2) Common.assoc;
  value : abstraction option;
  finally : abstraction option;
}

and abstraction = Pattern.t * term

and abstraction2 = Pattern.t * Pattern.t * term

and operation = term * Common.opsym

and resource = term * (Common.opsym, Pattern.t * Pattern.t * term) Common.assoc


type ty =
  | TyApply of Common.tyname * ty list
  (** [(ty1, ty2, ..., tyn) Type] *)
  | TyParam of Common.typaram
  (** ['a] *)
  | TyArrow of ty * ty
  (** [ty1 -> ty2] *)
  | TyTuple of ty list
  (** [ty1 * ty2 * ... * tyn] *)
  | TyHandler of ty * ty
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

(* Toplevel definitions which need not be separated by;; *)
type topdef = plain_topdef Common.pos
and plain_topdef =
  | Tydef of (Common.tyname * (Common.typaram list * tydef)) list
  (* [type t = tydef] *)
  | TopLet of (Pattern.t * term) list
  (* [let p1 = t1 and ... and pn = tn] *)
  | TopLetRec of (Common.variable * term) list
  (* [let rec f1 p1 = t1 and ... and fn pn = tn] *)
  | External of Common.variable * ty * Common.variable
  (* [external x : t = "ext_val_name"] *)

(* Toplevel entries which need to be separated by;; *)
type toplevel =
  | Topdef of topdef
  | Term of term
  | Use of string
  | Reset
  | Help
  | Quit
  | TypeOf of term

