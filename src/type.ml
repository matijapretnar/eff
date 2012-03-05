module C = Common

type param = int

type ty =
  | Basic of string
  | Param of param (* a type variable *)
  | Apply of C.tyname * ty list
  | Arrow of ty * ty
  | Tuple of ty list
  | Record of (C.field * ty) list
  | Sum of (C.label * ty option) list
  | Effect of effect_sig
  | Handler of handler_ty

and handler_ty = {
  value: ty; (* the type of the _argument_ of value *)
  finally: ty; (* the return type of finally *)
}

and op_ty = ty * ty

and effect_sig = (C.opname * op_ty) list

type substitution = (param * ty) list

let empty_subst = []

(* This type is used when type checking is turned off. Its name
   is syntactically incorrect so that the programmer cannot accidentally
   define it. *)
let universal_ty = Basic "_"
   
let int_ty = Basic "int"
let bool_ty = Basic "bool"
let string_ty = Basic "string"
let float_ty = Basic "float"
let unit_ty = Tuple []
let empty_ty = Sum []

let next_param = C.fresh "type parameter" 

let fresh_param () = Param (next_param ())

let subst_ty sbst =
  let rec subst = function
    | Basic _ as t -> t
    | Param p as t ->
        begin match C.lookup p sbst with
          | Some u -> u
          | None -> t
        end
    | Apply (t, lst) -> Apply (t, C.map subst lst)
    | Arrow (t1, t2) -> Arrow (subst t1, subst t2)
    | Tuple lst -> Tuple (C.map subst lst)
    | Record lst -> Record (C.assoc_map subst lst)
    | Sum lst -> Sum (C.assoc_map (C.option_map subst) lst)
    | Effect lst -> Effect (C.assoc_map (fun (t1,t2) -> (subst t1, subst t2)) lst)
    | Handler {value=t1; finally=t2} -> Handler {value=subst t1; finally=subst t2}
  in
  subst

let compose_subst subst1 subst2 =
  List.map (fun (k, t) -> (k, subst_ty subst2 t)) subst1

let concat_subst subst1 subst2 = subst1 @ subst2

let free_params t =
  let rec free = function
    | Basic _ -> []
    | Apply (_, lst) -> List.flatten (List.map free lst)
    | Param p -> [p]
    | Arrow (t1, t2) -> free t1 @ free t2
    | Tuple lst -> List.flatten (List.map free lst)
    | Record lst -> List.flatten (List.map (fun (_,t) -> free t) lst)
    | Sum lst -> List.flatten (List.map (function (_,None) -> [] | (_, Some t) -> free t) lst)
    | Effect lst -> List.flatten (List.map (function (_,(t1,t2)) -> free t1 @ free t2) lst)
    | Handler {value=t1; finally=t2} -> free t1 @ free t2
  in
    C.uniq (free t)

exception Occurs

let occurs_in_ty p t =
  let rec check = function
    | Basic _ -> ()
    | Apply (_, lst) -> List.iter check lst
    | Param q -> if p = q then raise Occurs
    | Arrow (t1, t2) -> check t1; check t2
    | Tuple lst -> List.iter check lst
    | Record lst -> List.iter (fun (_,t) -> check t) lst
    | Sum lst -> List.iter (function (_,None) -> () | (_,Some t) -> check t) lst
    | Effect lst -> List.iter (fun (_,(t1,t2)) -> check t1; check t2) lst
    | Handler {value=t1; finally=t2} -> check t1; check t2
  in
  try
    check t ; false
  with
    Occurs -> true

(** [reresh ps ty] renames the polymorphic parameters [ps] in [ty] to new parameters. *)
let refresh ps ty =
  let sbst = List.map (fun p -> (p, fresh_param ())) ps in
  let rec refresh = function
    | Basic b -> Basic b
    | Param p -> (try List.assoc p sbst with Not_found -> Param p)
    | Apply (t, lst) -> Apply (t, C.map refresh lst)
    | Arrow (t1, t2) -> Arrow (refresh t1, refresh t2)
    | Tuple lst -> Tuple (C.map refresh lst)
    | Record lst -> Record (C.assoc_map refresh lst)
    | Sum lst -> Sum (C.assoc_map (C.option_map refresh) lst)
    | Effect lst -> Effect (C.assoc_map (fun (t1,t2) ->
                                                let u1 = refresh t1 in 
                                                let u2 = refresh t2 in
                                                  (u1, u2)) lst)
    | Handler {value=t1; finally=t2} ->
        let u1 = refresh t1 in
        let u2 = refresh t2 in
          Handler {value = u1; finally = u2}
  in
    refresh ty

(** [beautify ty] returns a substitution from type parameters to integers,
    to be used for pretty printing. *)
let beautify ty =
  let next_param = C.fresh "beautify" in
  let sbst = ref [] in
  let rec scan = function
    | Basic _ -> ()
    | Param p ->
        begin match C.lookup p !sbst with
        | Some _ -> ()
        | None ->
            let m = next_param () in
            sbst := (p, m) :: !sbst ;
        end
    | Apply (t, lst) -> List.iter scan lst
    | Arrow (t1, t2) -> scan t1 ; scan t2
    | Tuple lst -> List.iter scan lst
    | Record lst -> List.iter (fun (_,t) -> scan t) lst
    | Sum lst -> List.iter (function (_,None) -> () | (_, Some t) -> scan t) lst
    | Effect lst -> List.iter (fun (_,(t1,t2)) -> scan t1 ; scan t2) lst
    | Handler {value=t1; finally=t2} -> scan t1; scan t2
  in
    scan ty ;
    !sbst

(** [beautify2 t1 t2] returns a substitution for type parameters,
    to be used for pretty printing of types [t1] and [t2]. *)
let beautify2 t1 t2 = beautify (Arrow (t1, t2))
