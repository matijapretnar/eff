open CoreUtils

let fresh_ty_param = CoreTypes.TyParam.fresh

type ty =
  | Apply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | Basic of Const.ty
  | Tuple of ty list
  | Arrow of ty * ty
  | Handler of handler_ty

and handler_ty = {
  value : ty;
  (* the type of the _argument_ of value *)
  finally : ty; (* the return type of finally *)
}

let int_ty = Basic Const.IntegerTy

let string_ty = Basic Const.StringTy

let bool_ty = Basic Const.BooleanTy

let float_ty = Basic Const.FloatTy

let unit_ty = Tuple []

let empty_ty = Apply (CoreTypes.empty_tyname, [])

type substitution = (CoreTypes.TyParam.t, ty) Assoc.t

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst ty =
  let rec subst = function
    | Apply (ty_name, tys) -> Apply (ty_name, List.map subst tys)
    | TyParam p as ty -> (
        match Assoc.lookup p sbst with Some ty -> ty | None -> ty)
    | Basic _ as ty -> ty
    | Tuple tys -> Tuple (List.map subst tys)
    | Arrow (ty1, ty2) -> Arrow (subst ty1, subst_ty sbst ty2)
    | Handler { value = ty1; finally = ty2 } ->
        Handler { value = subst ty1; finally = subst ty2 }
  in
  subst ty

(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = Assoc.empty

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  Assoc.concat sbst1 (Assoc.map (subst_ty sbst1) sbst2)

(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty =
  let rec free_ty = function
    | Apply (_, tys) -> concat_map free_ty tys
    | TyParam p -> [ p ]
    | Basic _ -> []
    | Tuple tys -> concat_map free_ty tys
    | Arrow (ty1, ty2) -> free_ty ty1 @ free_ty ty2
    | Handler { value = ty1; finally = ty2 } -> free_ty ty1 @ free_ty ty2
  in
  unique_elements (free_ty ty)

(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = List.mem p (free_params ty)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())

let refreshing_subst ps =
  let ps' = Assoc.map_of_list (fun p -> (p, fresh_ty_param ())) ps in
  let sbst = Assoc.map (fun p' -> TyParam p') ps' in
  (Assoc.values_of ps', sbst)

(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh params ty =
  let params', sbst = refreshing_subst params in
  (params', subst_ty sbst ty)

(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify (ps, ty) =
  let next_ty_param = CoreTypes.TyParam.new_fresh () in
  let xs = free_params ty in
  let xs_assoc = Assoc.map_of_list (fun p -> (p, next_ty_param ())) xs in
  let sub p = match Assoc.lookup p xs_assoc with None -> p | Some p' -> p' in
  let ty_sbst = Assoc.map (fun p' -> TyParam p') xs_assoc in
  (List.map sub ps, subst_ty ty_sbst ty)

let beautify2 ty1 ty2 =
  match beautify ([], Tuple [ ty1; ty2 ]) with
  | ps, Tuple [ ty1; ty2 ] -> ((ps, ty1), (ps, ty2))
  | _ -> assert false

let print (ps, t) ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match t with
    | Arrow (t1, t2) ->
        print ~at_level:5 "@[<h>%t ->@ %t@]" (ty ~max_level:4 t1) (ty t2)
    | Basic b -> print "%t" (Const.print_ty b)
    | Apply (t, []) -> print "%t" (CoreTypes.TyName.print t)
    | Apply (t, [ s ]) ->
        print ~at_level:1 "%t %t" (ty ~max_level:1 s) (CoreTypes.TyName.print t)
    | Apply (t, ts) ->
        print ~at_level:1 "(%t) %t"
          (Print.sequence ", " ty ts)
          (CoreTypes.TyName.print t)
    | TyParam p -> print "%t" (CoreTypes.TyParam.print_old ~poly:ps p)
    | Tuple [] -> print "unit"
    | Tuple ts ->
        print ~at_level:2 "@[<hov>%t@]"
          (Print.sequence " * " (ty ~max_level:1) ts)
    | Handler { value = t1; finally = t2 } ->
        print ~at_level:4 "%t =>@ %t" (ty ~max_level:2 t1) (ty t2)
  in
  ty t ppf

let print_beautiful sch = print (beautify sch)
