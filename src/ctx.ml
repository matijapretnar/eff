(** Type inference contexts *)
module C = Common
module T = Type

let extend_var x pt ctx = (x, pt) :: ctx

let extend_vars vars ctx =
  List.fold_right (fun (x, t) ctx -> extend_var x ([], t) ctx) vars ctx

(** Initial context has no variables and only builtin types *)
let initial = []

(** [freeparams ctx] returns a list of all free type parameters in [ctx] *)
let free_params lst =
  C.uniq (List.flatten (List.map (fun (_,(ps,t)) -> C.diff (T.free_params t) ps) lst))

(** [subst_ctx sbst ctx] applies a type substitution to all types occurring in
    [ctx]. *)
let subst_ctx sbst ctx =
  C.assoc_map
        (fun (ps,t) -> 
          assert (List.for_all (fun (p,_) -> not (List.mem p ps)) sbst) ;
          (ps, T.subst_ty sbst t))
        ctx

(* [generalize_vars sbst ctx vars] generalizes the given variables. *)
let generalize_vars sbst ctx vars =
  let ctx = subst_ctx sbst ctx in
  let qs = free_params ctx in
    C.assoc_map (fun t -> C.diff (T.free_params (T.subst_ty sbst t)) qs, t) vars

(* [generalize sbst ctx t] returns the variables over which we may generalize type [t]. *)
let generalize sbst ctx t =
  let ctx = subst_ctx sbst ctx in
  let ps = T.free_params (T.subst_ty sbst t) in
  let qs = free_params ctx in
    C.diff ps qs
