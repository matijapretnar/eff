type param = int

type ty =
  | Apply of Common.tyname * ty list
  | Param of param (* a type variable *)
  | Basic of string
  | Tuple of ty list
  | Record of (Common.field, ty) Common.assoc
  | Sum of (Common.label, ty option) Common.assoc
  | Arrow of ty * ty
  | Effect of (Common.opsym, ty * ty) Common.assoc
  | Handler of handler_ty

and handler_ty = {
  value: ty; (* the type of the _argument_ of value *)
  finally: ty; (* the return type of finally *)
}

(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"

let int_ty = Basic "int"
let string_ty = Basic "string"
let bool_ty = Basic "bool"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Sum []

let ty_of_const = function
  | Common.Integer _ -> int_ty
  | Common.String _ -> string_ty
  | Common.Boolean _ -> bool_ty
  | Common.Float _ -> float_ty

type substitution = (param * ty) list

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let subst_ty sbst ty =
  let rec subst = function
  | Apply (ty_name, tys) -> Apply (ty_name, List.map subst tys)
  | Param p as ty -> (try List.assoc p sbst with Not_found -> ty)
  | Basic _ as ty -> ty
  | Tuple tys -> Tuple (List.map subst tys)
  | Record tys -> Record (Common.assoc_map subst tys)
  | Sum tys -> Sum (Common.assoc_map (Common.option_map subst) tys)
  | Arrow (ty1, ty2) -> Arrow (subst ty1, subst ty2)
  | Effect op_sig ->
      Effect (Common.assoc_map (fun (ty1, ty2) -> (subst ty1, subst ty2)) op_sig)
  | Handler {value = ty1; finally = ty2} ->
      Handler {value = subst ty1; finally = subst ty2}
  in
  subst ty

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = []

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  sbst1 @ Common.assoc_map (subst_ty sbst1) sbst2

(** [free_params ty] returns a list of all type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty =
  let rec free = function
  | Apply (_, tys) -> Common.flatten_map free tys
  | Param p -> [p]
  | Basic _ -> []
  | Tuple tys -> Common.flatten_map free tys
  | Record tys -> Common.flatten_map (fun (_, ty) -> free ty) tys
  | Sum tys ->
      Common.flatten_map (function (_, None) -> [] | (_, Some ty) -> free ty) tys
  | Arrow (ty1, ty2) -> free ty1 @ free ty2
  | Effect op_sig ->
      Common.flatten_map (function (_, (ty1, ty2)) -> free ty1 @ free ty2) op_sig
  | Handler {value = ty1; finally = ty2} -> free ty1 @ free ty2
  in
  Common.uniq (free ty)

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = List.mem p (free_params ty)

(** [next_param ()] gives a new type parameter on each call. *)
let next_param = Common.fresh "type parameter" 

(** [fresh_param ()] gives a type [Param p] where [p] is a new type parameter on
    each call. *)
let fresh_param () = Param (next_param ())

(** [refresh ps ty] replaces the polymorphic parameters [ps] in [ty] with new
    values. *)
let refresh ps ty =
  let sbst = List.map (fun p -> (p, fresh_param ())) ps in
  subst_ty sbst ty

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify ty =
  let next_param = Common.fresh "beautify" in
  List.map (fun p -> (p, next_param ())) (free_params ty)

(** [beautify2 ty1 ty2] returns a sequential replacement of type parameters in
    [ty1] and [ty2] that can be used for their simultaneous pretty printing. *)
let beautify2 ty1 ty2 = beautify (Tuple [ty1; ty2])
