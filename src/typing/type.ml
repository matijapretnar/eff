(* We need three sorts of parameters, for types, dirt, and regions.
   In order not to confuse them, we define separate types for them.
 *)

type ty_param = Ty_Param of int

let fresh_ty_param = OldUtils.fresh (fun n -> Ty_Param n)

type ty =
  | Apply of OldUtils.tyname * ty list
  | TyParam of ty_param
  | Basic of string
  | Tuple of ty list
  | Arrow of ty * ty
  | Handler of handler_ty

and handler_ty =
  { value: ty
  ; (* the type of the _argument_ of value *)
  finally: ty
  (* the return type of finally *) }

(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
  
let in_channel_ty = Basic "in_channel"
let out_channel_ty = Basic "out_channel"
  
let universal_ty = Basic "_"

let char_ty = Basic "char"

let int_ty = Basic "int"

let string_ty = Basic "string"

let bool_ty = Basic "bool"

let float_ty = Basic "float"

let unit_ty = Tuple []

let empty_ty = Apply ("empty", [])

type substitution = (ty_param * ty) list

(** [subst_ty sbst ty] replaces type parameters in [ty] according to [sbst]. *)
let rec subst_ty sbst ty =
  let rec subst = function
    | Apply (ty_name, tys) -> Apply (ty_name, List.map subst tys)
    | TyParam p as ty -> (
      match OldUtils.lookup p sbst with Some ty -> ty | None -> ty )
    | Basic _ as ty -> ty
    | Tuple tys -> Tuple (List.map subst tys)
    | Arrow (ty1, ty2) -> Arrow (subst ty1, subst_ty sbst ty2)
    | Handler {value= ty1; finally= ty2} ->
        Handler {value= subst ty1; finally= subst ty2}
  in
  subst ty


(** [identity_subst] is a substitution that makes no changes. *)
let identity_subst = []

(** [compose_subst sbst1 sbst2] returns a substitution that first performs
    [sbst2] and then [sbst1]. *)
let compose_subst sbst1 sbst2 =
  sbst1 @ OldUtils.assoc_map (subst_ty sbst1) sbst2


(** [free_params ty] returns three lists of type parameters that occur in [ty].
    Each parameter is listed only once and in order in which it occurs when
    [ty] is displayed. *)
let free_params ty =
  let flatten_map f lst = List.fold_left ( @ ) [] (List.map f lst) in
  let rec free_ty = function
    | Apply (_, tys) -> flatten_map free_ty tys
    | TyParam p -> [p]
    | Basic _ -> []
    | Tuple tys -> flatten_map free_ty tys
    | Arrow (ty1, ty2) -> free_ty ty1 @ free_ty ty2
    | Handler {value= ty1; finally= ty2} -> free_ty ty1 @ free_ty ty2
  in
  OldUtils.uniq (free_ty ty)


(** [occurs_in_ty p ty] checks if the type parameter [p] occurs in type [ty]. *)
let occurs_in_ty p ty = List.mem p (free_params ty)

(** [fresh_ty ()] gives a type [TyParam p] where [p] is a new type parameter on
    each call. *)
let fresh_ty () = TyParam (fresh_ty_param ())

let refreshing_subst ps =
  let ps' = List.map (fun p -> (p, fresh_ty_param ())) ps in
  let sbst = OldUtils.assoc_map (fun p' -> TyParam p') ps' in
  (List.map snd ps', sbst)


(** [refresh (ps,qs,rs) ty] replaces the polymorphic parameters [ps,qs,rs] in [ty] with fresh
    parameters. It returns the  *)
let refresh params ty =
  let params', sbst = refreshing_subst params in
  (params', subst_ty sbst ty)


(** [beautify ty] returns a sequential replacement of all type parameters in
    [ty] that can be used for its pretty printing. *)
let beautify (ps, ty) =
  let next_ty_param = OldUtils.fresh (fun n -> Ty_Param n) in
  let xs = free_params ty in
  let xs_map = List.map (fun p -> (p, next_ty_param ())) xs in
  let subst ps ps_map =
    List.map
      (fun p -> match OldUtils.lookup p ps_map with None -> p | Some p' -> p')
      ps
  in
  let sbst = OldUtils.assoc_map (fun p' -> TyParam p') xs_map in
  (subst ps xs_map, subst_ty sbst ty)


let beautify2 ty1 ty2 =
  match beautify ([], Tuple [ty1; ty2]) with
  | ps, Tuple [ty1; ty2] -> ((ps, ty1), (ps, ty2))
  | _ -> assert false


let print ((ps as poly), t) ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    match t with
    | Arrow (t1, t2) ->
        print ~at_level:5 "@[<h>%t ->@ %t@]" (ty ~max_level:4 t1) (ty t2)
    | Basic b -> print "%s" b
    | Apply (t, []) -> print "%s" t
    | Apply (t, [s]) -> print ~at_level:1 "%t %s" (ty ~max_level:1 s) t
    | Apply (t, ts) ->
        print ~at_level:1 "(%t) %s" (Print.sequence ", " ty ts) t
    | TyParam (Ty_Param k as p) ->
        let c = if List.mem p ps then "'" else "'_" in
        if 0 <= k && k <= 25 then
          print "%s%c" c (char_of_int (k + int_of_char 'a'))
        else print "%sty%i" c (k - 25)
    | Tuple [] -> print "unit"
    | Tuple ts ->
        print ~at_level:2 "@[<hov>%t@]"
          (Print.sequence " * " (ty ~max_level:1) ts)
    | Handler {value= t1; finally= t2} ->
        print ~at_level:4 "%t =>@ %t" (ty ~max_level:2 t1) (ty t2)
  in
  ty t ppf


let print_beautiful sch = print (beautify sch)
