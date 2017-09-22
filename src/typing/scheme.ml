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

let ty_cnstr ~loc ty1 ty2 (ctx, ty, cnstrs) =
  (ctx, ty, Unification.add_ty_constraint ty1 ty2 cnstrs)

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
    | Some u -> ty_cnstr ~loc u t ((x, u) :: ctx, ty, cnstrs)
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
  Common.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Unification.subst sbst cnstrs

(****************************)
(* ABSTRACTION CONSTRUCTORS *)
(****************************)

let abstract ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  match create_ty_scheme ctx_c (Type.Arrow (ty_p, drty_c)) [
      trim_context ~loc ctx_p;
      just cnstrs_p;
      just cnstrs_c
    ] with
  | ctx, Type.Arrow (ty_p, drty_c), cnstrs -> ctx, (ty_p, drty_c), cnstrs
  | _ -> assert false

and abstract2 ~loc (ctx_p1, ty_p1, cnstrs_p1) (ctx_p2, ty_p2, cnstrs_p2) (ctx_c, drty_c, cnstrs_c) =
  match create_ty_scheme ctx_c (Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c)) [
      trim_context ~loc (ctx_p1 @ ctx_p2);
      just cnstrs_p1;
      just cnstrs_p2;
      just cnstrs_c
    ] with
  | ctx, Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c), cnstrs -> ctx, (ty_p1, ty_p2, drty_c), cnstrs
  | _ -> assert false

(***************************)
(* EXPRESSION CONSTRUCTORS *)
(***************************)

let var x ty = ([(x, ty)], ty, Unification.empty)

let const c =
  let ty = match c with
    | Const.Integer _ -> Type.int_ty
    | Const.String _ -> Type.string_ty
    | Const.Boolean _ -> Type.bool_ty
    | Const.Float _ -> Type.float_ty
  in
  simple ty

let lambda ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  create_ty_scheme ctx_c (Type.Arrow (ty_p, drty_c)) [
      trim_context ~loc ctx_p;
      just cnstrs_p;
      just cnstrs_c
    ]

let tuple es =
  let ctx, tys, constraints =
    List.fold_right (fun e (ctx, tys, constraints) ->
        let e_ctx, e_ty, e_constraints = e in
        e_ctx @ ctx, e_ty :: tys, Unification.list_union [e_constraints; constraints]
      ) es ([], [], Unification.empty)
  in
  (ctx, Type.Tuple tys, constraints)

let effect ty_par ty_res eff_name =
  let drt = {Type.ops = [eff_name]; Type.rest = Params.fresh_dirt_param ()} in
  let ty = Type.Arrow (ty_par, (ty_res, drt)) in
  simple ty

let handler effect_clauses value_clause =
  simple Type.int_ty

(***************************)
(* COMPUTATION CONSTRUCTORS*)
(***************************)


(************************)
(* PATTERN CONSTRUCTORS *)
(************************)

let pvar x =
  let ty = Type.fresh_ty () in
  let scheme = Scheme.simple ty in
  add_to_context x ty scheme

let pconst const =
  let ty = ty_of_const const in
  simple ty

let pnonbinding () =
  let ty = Type.fresh_ty () in
  simple ty

let pas p x =
  let ty = Scheme.get_type p in
  add_to_context x ty p

let ptuple ps =
  let infer p (ctx, tys, chngs) =
    let ctx_p, ty_p, cnstrs_p = p in
    ctx_p @ ctx, ty_p :: tys, Unification.union cnstrs_p chngs
  in
  let ctx, tys, chngs = List.fold_right infer ps ([], [], Unification.empty) in
  let ty = Type.Tuple tys in
  scheme.simple ty

(**********************)
(* PRINTING FUNCTIONS *)
(**********************)

let subst_ty_scheme sbst (ctx, ty, cnstrs) =
  let ty = Type.subst_ty sbst ty in
  let cnstrs = Unification.subst sbst cnstrs in
  let ctx = Common.assoc_map (Type.subst_ty sbst) ctx in
  (ctx, ty, cnstrs)

let subst_dirty_scheme sbst (ctx, drty, cnstrs) =
  let drty = Type.subst_dirty sbst drty in
  let cnstrs = Unification.subst sbst cnstrs in
  let ctx = Common.assoc_map (Type.subst_ty sbst) ctx in
  (ctx, drty, cnstrs)

let beautify_ty_scheme ty_sch =
  let sbst = Params.beautifying_subst () in
  subst_ty_scheme sbst (ty_sch)

let beautify_dirty_scheme drty_sch =
  let sbst = Params.beautifying_subst () in
  subst_dirty_scheme sbst (drty_sch)

let print_context ctx ppf =
  let print_binding (x, t) ppf =
    Print.print ppf "%t : %t" (Untyped.Variable.print ~safe:true x) (Type.print_ty t)
  in
  Print.sequence ", " print_binding ctx ppf

let print_ty_scheme ty_sch ppf =
  let (ctx, ty, cnstrs) = beautify_ty_scheme ty_sch in
  Print.print ppf "%t |- %t | %t"
    (print_context ctx)
    (Type.print_ty ty)
    (Unification.print cnstrs)

let print_dirty_scheme ty_sch ppf =
  let (ctx, (ty, drt), cnstrs) = beautify_dirty_scheme ty_sch in
  Print.print ppf "%t |- %t ! %t | %t"
    (print_context ctx)
    (Type.print_ty ty)
    (Type.print_dirt drt)
    (Unification.print cnstrs)
