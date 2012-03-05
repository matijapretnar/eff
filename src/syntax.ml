(** Abstract syntax of eff terms, computations, and toplevel commands. *)
module C = Common

type tydef =
  | TyRecord of (C.field, ty) C.assoc
  | TySum of (C.label, ty option) C.assoc
  | TyEffect of (C.opname, ty * ty) C.assoc
  | TyInline of ty

and ty =
  | TyApply of C.tyname * ty list
  | TyParam of C.param
  | TyArrow of ty * ty
  | TyTuple of ty list
  | TyHandler of ty * ty

type term =
  plain_term C.pos
and plain_term =
  | Var of C.variable (* x *)
  | Const of C.const  (* c *)
  | Tuple of term list (* e1, ..., en *)
  | Record of (C.field, term) C.assoc (* {l1=e1; ...; ln=en} *)
  | Variant of C.label * term option (* L e *)
  | Lambda of abstraction (* fun p -> e *)
  | Handler of handler
  | Apply of term * term
  | Match of term * abstraction list
  | Function of abstraction list
  | New of C.tyname * resource option
  | Handle of term * term
  | Check of term
  | Conditional of term * term * term
  | While of term * term
  | For of C.variable * term * term * term * bool
  | Operation of operation
  | Let of (Pattern.t * term) list * term
  | LetRec of (C.variable * term) list * term

and handler = {
  operations : (operation, Pattern.t * abstraction) C.assoc ;
  value : abstraction option;
  finally : abstraction option;
}

and resource = term * (C.opname, Pattern.t * Pattern.t * term) C.assoc

and abstraction = Pattern.t * term

and operation = term * C.opname

(* Toplevel definitions which need not be separated by ;; *)
type topdef = plain_topdef C.pos
and plain_topdef =
  | Tydef of (C.tyname * (C.param list * tydef)) list
  | TopLet of (Pattern.t * term) list
  | TopLetRec of (C.variable * term) list
  | External of C.variable * ty * C.variable

(* Toplevel entries which need to be separated by ;; *)
and toplevel =
  | Topdef of topdef
  | Expr of term
  | Use of string
  | Reset
  | Help
  | Quit
  | TypeOf of term

let unit_term = Tuple []

(** [ty_fv t] returns the list of free parameters occuring in type [t]. *)
let rec ty_fv = function
  | TyApply (_, lst) -> List.flatten (List.map ty_fv lst)
  | TyParam s -> [s]
  | TyArrow (t1, t2) -> ty_fv t1 @ ty_fv t2
  | TyTuple lst -> List.flatten (List.map ty_fv lst)
  | TyHandler (t1, t2) -> ty_fv t1 @ ty_fv t2
