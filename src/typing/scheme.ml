(********************)
(* TYPE DEFINITIONS *)
(********************)

(* Type definitions for different kinds of schemes *)
type context = (Untyped.variable, Type.ty) OldUtils.assoc
type 'a t = context * 'a * Unification.t
type ty_scheme = Type.ty t
type dirty_scheme = Type.dirty t
type abstraction_scheme = (Type.ty * Type.dirty) t
type abstraction2_scheme = (Type.ty * Type.ty * Type.dirty) t

(********************)
(* HELPER FUNCTIONS *)
(********************)

let ty_cnstr ~loc ty1 ty2 (ctx, ty, cnstrs) =
  (ctx, ty, Unification.add_ty_constraint ~loc ty1 ty2 cnstrs)

let remove_context ~loc ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match OldUtils.lookup x ctx_p with
    | None -> ((x, t) :: ctx, ty, cnstrs)
    | Some u -> (ctx, ty, cnstrs)
  in
  List.fold_right trim ctx ([], ty, cnstrs)

let less_context ~loc ctx_p (ctx, ty, cnstrs) =
  let trim (x, t) (ctx, ty, cnstrs) =
    match OldUtils.lookup x ctx_p with
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
  List.fold_right OldUtils.id changes (ctx, ty, Unification.empty)

(**********************)
(* PRINTING FUNCTIONS *)
(**********************)

let subst_ty_scheme sbst (ctx, ty, cnstrs) =
  let ty = Type.subst_ty sbst ty in
  let cnstrs = Unification.subst sbst cnstrs in
  let ctx = OldUtils.assoc_map (Type.subst_ty sbst) ctx in
  (ctx, ty, cnstrs)

let subst_dirty_scheme sbst (ctx, drty, cnstrs) =
  let drty = Type.subst_dirty sbst drty in
  let cnstrs = Unification.subst sbst cnstrs in
  let ctx = OldUtils.assoc_map (Type.subst_ty sbst) ctx in
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
  Print.print ppf "(%t) |- (%t) | [%t]"
    (print_context ctx)
    (Type.print_ty ty)
    (Unification.print cnstrs)

let print_dirty_scheme ty_sch ppf =
  let (ctx, (ty, drt), cnstrs) = beautify_dirty_scheme ty_sch in
  Print.print ppf "(%t) |- (%t) ! (%t) | [%t]"
    (print_context ctx)
    (Type.print_ty ty)
    (Type.print_dirt drt)
    (Unification.print cnstrs)

(******************)
(* SCHEME SOLVERS *)
(******************)

let solve_ty (ctx, ty, cnstrs) =
  Unification.unify_ty ctx ty cnstrs

let solve_dirty (ctx, ty, cnstrs) =
  Unification.unify_dirty ctx ty cnstrs

(*****************************)
(* INTERFACE IMPLEMENTATIONS *)
(*****************************)

(* Create a simple scheme (with only a type) *)
let simple ty = ([], ty, Unification.empty)

(* Add a key:v value:ty pair to the context *)
let add_to_context v ty (ctx, t, u) = (OldUtils.update v ty ctx, t, u)

(* Get the type from a scheme *)
let get_type (ctx, ty, u) = ty

(* Get the context from a scheme *)
let get_context (ctx, ty, u) = ctx

(* Convert a type scheme to a new dirty type scheme (used for values) *)
let make_dirty (ctx, ty, constraints) = (ctx, (ty, Type.fresh_dirt ()), constraints)

(* Refresh a scheme (generate new type/dirt variables) *)
let refresh (ctx, ty, cnstrs) =
  let sbst = Params.refreshing_subst () in
  OldUtils.assoc_map (Type.subst_ty sbst) ctx, Type.subst_ty sbst ty, Unification.subst sbst cnstrs

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

let var ~loc x ty = solve_ty ([(x, ty)], ty, Unification.empty)

let const ~loc c =
  let ty = match c with
    | Const.Integer _ -> Type.int_ty
    | Const.String _ -> Type.string_ty
    | Const.Boolean _ -> Type.bool_ty
    | Const.Float _ -> Type.float_ty
  in
  solve_ty (simple ty)

let lambda ~loc (ctx_p, ty_p, cnstrs_p) (ctx_c, drty_c, cnstrs_c) =
  let sch = create_ty_scheme ctx_c (Type.Arrow (ty_p, drty_c)) [
      trim_context ~loc ctx_p;
      just cnstrs_p;
      just cnstrs_c
    ] in
  solve_ty sch

let tuple ~loc es =
  let ctx, tys, constraints =
    List.fold_right (fun e (ctx, tys, constraints) ->
        let e_ctx, e_ty, e_constraints = e in
        e_ctx @ ctx, e_ty :: tys, Unification.list_union [e_constraints; constraints]
      ) es ([], [], Unification.empty)
  in
  solve_ty (ctx, Type.Tuple tys, constraints)

let effect ~loc ty_par ty_res eff_name =
  (* let drt = {Type.ops = [eff_name]; Type.rest = Params.fresh_dirt_param ()} in *)
  let drt = Type.fresh_dirt_ops (Type.Op eff_name) in
  let ty = Type.Arrow (ty_par, (ty_res, drt)) in
  solve_ty (simple ty)

let handler ~loc effect_clauses value_clause =
  (* make the required elements for the handler *)
  let param = Type.fresh_dirty () in
  let ret = Type.fresh_dirty () in
  let (ret_ty, ret_drt) = ret in
  let (param_ty, param_drt) = param in
  let cnstr = Unification.empty in
  let ctx = [] in

  (* add constraints for the value clause *)
  let (ctx_v, (ty_p_v, drty_r_v), cnstr_v) = value_clause in
  let cnstr = Unification.add_dirty_constraint ~loc drty_r_v ret cnstr in
  let cnstr = Unification.add_ty_constraint ~loc param_ty ty_p_v cnstr in
  let cnstr = Unification.list_union [cnstr; cnstr_v] in
  let ctx = ctx_v @ ctx in

  (* add constraints for the effect clause *)
  let handle_effect_clause ((_, (ty_par, ty_ret)), abstr) (ctx, cnstr) =
    let (ctx_e, (ty_p_e, ty_k_e, drty_r_e), cnstr_e) = abstr in
    let ctx = ctx_e @ ctx in
    let cnstr = Unification.add_ty_constraint ~loc ty_par ty_p_e cnstr in
    let cnstr = Unification.add_ty_constraint ~loc (Type.Arrow (ty_ret, ret)) ty_k_e cnstr in
    let cnstr = Unification.add_dirty_constraint ~loc drty_r_e ret cnstr in
    let cnstr = Unification.list_union [cnstr; cnstr_e] in
    (ctx, cnstr)
  in
  let (ctx, cnstr) = List.fold_right handle_effect_clause effect_clauses (ctx, cnstr) in

  (* loop over all effect that can be handled, input and output contain these effects *)
  let effs = List.map (fun (eff, _) -> eff) (OldUtils.uniq (List.map fst effect_clauses)) in
  let param_drt = Type.add_ops_list effs param_drt in
  let cnstr = Unification.add_dirt_constraint ~loc param_drt ret_drt cnstr in

  (* result *)
  let ty = Type.Handler ((param_ty, param_drt), ret) in
  solve_ty (ctx, ty, cnstr)

(***************************)
(* COMPUTATION CONSTRUCTORS*)
(***************************)

let value ~loc e = solve_dirty (make_dirty e)

let apply ~loc e1 e2 =
  let ctx_e1, ty_e1, cnstrs_e1 = e1 in
  let ctx_e2, ty_e2, cnstrs_e2 = e2 in
  let drty = Type.fresh_dirty () in
  let constraints = Unification.union cnstrs_e1 cnstrs_e2  in
  let constraints = Unification.add_ty_constraint ~loc ty_e1 (Type.Arrow (ty_e2, drty)) constraints in
  solve_dirty (ctx_e1 @ ctx_e2, drty, constraints)

let patmatch ~loc es cases =
  let ctx_e, ty_e, cnstrs_e = es in
  let drty = Type.fresh_dirty () in
  match cases with
    | [] ->
      let constraints = Unification.add_ty_constraint ~loc ty_e Type.empty_ty cnstrs_e in
      solve_dirty (ctx_e, drty, constraints)
    | _::_ ->
      let fold a (ctx, constraints) =
        let ctx_a, (ty_p, drty_c), cnstrs_a = a in
        ctx_a @ ctx,
        Unification.list_union [cnstrs_a; constraints]
        |> Unification.add_ty_constraint ~loc ty_e ty_p
        |> Unification.add_dirty_constraint ~loc drty_c drty
      in
      let ctx, constraints = List.fold_right fold cases (ctx_e, cnstrs_e) in
      solve_dirty (ctx, drty, constraints)

let handle ~loc e c =
  let ctx_e, ty_e, cnstrs_e = e in
  let ctx_c, drty_c, cnstrs_c = c in
  let drty = Type.fresh_dirty () in
  let constraints =
    Unification.list_union [cnstrs_e; cnstrs_c]
    |> Unification.add_ty_constraint ~loc ty_e (Type.Handler (drty_c, drty))
  in
  solve_dirty (ctx_e @ ctx_c, drty, constraints)

(************************)
(* PATTERN CONSTRUCTORS *)
(************************)

let pvar ~loc x =
  let ty = Type.fresh_ty () in
  let sch = simple ty in
  solve_ty (add_to_context x ty sch)

let pconst ~loc const =
  let ty = match const with
    | Const.Integer _ -> Type.int_ty
    | Const.String _ -> Type.string_ty
    | Const.Boolean _ -> Type.bool_ty
    | Const.Float _ -> Type.float_ty
  in
  solve_ty (simple ty)

let pnonbinding ~loc () =
  let ty = Type.fresh_ty () in
  solve_ty (simple ty)

let pas ~loc p x =
  let ty = get_type p in
  solve_ty (add_to_context x ty p)

let ptuple ~loc ps =
  let infer p (ctx, tys, chngs) =
    let ctx_p, ty_p, cnstrs_p = p in
    ctx_p @ ctx, ty_p :: tys, Unification.union cnstrs_p chngs
  in
  let ctx, tys, chngs = List.fold_right infer ps ([], [], Unification.empty) in
  let ty = Type.Tuple tys in
  solve_ty (simple ty)

let precord ~loc ctx ty changes = solve_ty (create_ty_scheme ctx ty changes)

