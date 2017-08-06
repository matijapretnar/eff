(********************)
(* TYPE DEFINITIONS *)
(********************)

(* Type definitions for different kinds of schemes *)
type context = (Untyped.variable, Type.ty) Common.assoc
type 'a t = context * 'a * Unification.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t
type abstraction_scheme = (Type.ty * Type.dirty) t
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t

(********************)
(* HELPER FUNCTIONS *)
(********************)

let ty_less ~loc ty1 ty2 (ctx, ty, cnstrs) = (ctx, ty, cnstrs)
  (* (ctx, ty, Constraints.add_ty_constraint ~loc ty1 ty2 cnstrs) *)

let remove_context ~loc ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs)
    | Some u -> (ctx, ty, cnstrs)
  in
  List.fold_right trim ctx ([], ty, cnstrs)

let less_context ~loc ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs)
    | Some u -> ty_less ~loc u t ((x, u) :: ctx, ty, cnstrs)
  in
  List.fold_right trim ctx ([], ty, cnstrs)

let trim_context ~loc ctx_p ty_sch =
  let ty_sch = less_context ~loc ctx_p ty_sch in
  let ty_sch = remove_context ~loc ctx_p ty_sch in
  ty_sch

let just new_cnstrs (ctx, ty, cnstrs) =
  (ctx, ty, Unification.union new_cnstrs cnstrs)

(* Create a new type scheme from 'ctx' and 'ty'
    Then apply the changes from 'changes' to the new scheme
*)
let create_ty_scheme ctx ty changes =
  List.fold_right Common.id changes (ctx, ty, Unification.empty)

(*****************************)
(* INTERFACE IMPLEMENTATIONS *)
(*****************************)

(* Create a simple scheme (with only a type) *)
let simple ty = ([], ty, Unification.empty)

(* Add a key:v value:ty pair to the context *)
let add_to_context v ty (ctx, t, u) = (Common.update v ty ctx, t, u)

(* Get the type from a scheme *)
let get_type (ctx, ty, u) = ty

(* Convert a type scheme to a new dirty type scheme (used for values) *)
let make_dirty (ctx, ty, constraints) = (ctx, (ty, Type.fresh_dirt ()), constraints)

(* Refresh a scheme (generate new type/dirt variables) *)
let refresh (ctx, ty, cnstrs) =
  let sbst = Params.refreshing_subst () in
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, (* Constraints.subst sbst *) cnstrs

let abstract ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  ([], (ty_p, drty_c), Unification.empty)

(**********************)
(* SMART CONSTRUCTORS *)
(**********************)

(* Abstraction
Use primary ctx from c
Use Arrow type
Union constraints from p and c

*)
let lambda ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  create_ty_scheme ctx_c (Type.Arrow (ty_p, drty_c)) [
      trim_context ~loc ctx_p;
      just cnstrs_p;
      just cnstrs_c
    ]
