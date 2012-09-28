module C = Common
module T = Type

let warn_implicit_sequencing = ref false;;

let disable_typing = ref false;;

(* XXX: Obsolete comments, fix.

   We perform type inference int the style of Standard ML 97, i.e.,
   Hindley-Milner polymorphism with value restriction. Throughout, we work with
   a reference to a type substitution, usually called [cstr], in which we
   collect the results of unification. That is, we perform unification as early
   as posssible (rather than collect all equations and then solve them), and
   store the results in [cstr]. 

   The effect of carrying around the substitution is that we need to be careful
   about when to apply it:
   
   1. we apply the substitution to types [t1] and [t2] before trying to solve
      the equation [t1 = t2].

   2. we apply the substitution to a type which we just looked up in the context.
*)

(* Can a computation safely be generalized, i.e., is it non-expansive in the parlance of
   SML? In our case non-expansive simply means "is a value". *)
let nonexpansive = function
  | Core.Value _ -> true
  | Core.Apply _ | Core.Match _ | Core.While _ | Core.For _ | Core.New _
  | Core.Handle _ | Core.Let _ | Core.LetRec _ | Core.Check _ -> false

let gather add_news =
  List.fold_right (fun add_new cnstrs -> add_new cnstrs) add_news Type.empty

let subnews ~pos nws1 nws2 cnstrs = Print.debug "Unifying freshness constraints."; cnstrs
let subtype ~pos ty1 ty2 cnstrs = Type.add_ty_constraint ~pos ty1 ty2 cnstrs
let subdirt ~pos drt1 drt2 cnstrs = Type.add_dirt_constraint ~pos drt1 drt2 cnstrs
let subregion ~pos rgn1 rgn2 cnstrs = Type.add_region_constraint ~pos rgn1 rgn2 cnstrs
let subdirty ~pos (nws1, ty1, d1) (nws2, ty2, d2) cnstrs =
  subnews ~pos nws1 nws2 (subtype ~pos ty1 ty2 (subdirt ~pos (Type.DirtParam d1) (Type.DirtParam d2) cnstrs))

let just cnstrs1 cnstrs2 = Type.join_disjoint_constraints cnstrs1 cnstrs2
let merge cnstrs1 cnstrs2 = Type.join_constraints cnstrs1 cnstrs2


let canonize_context ~pos (ctx, ty, cnstrs) =
  let add (x, ty) (ctx, cnstrs) =
    match Common.lookup x ctx with
    | None ->
        let ty' = Type.fresh_ty () in
        ((x, ty') :: ctx, subtype ~pos ty' ty cnstrs)
    | Some ty' ->
        (ctx, subtype ~pos ty' ty cnstrs)
  in
  let ctx, cnstrs = List.fold_right add ctx ([], cnstrs) in
  ctx, ty, cnstrs

let add_ty_constraint cstr pos t1 t2 =
  cstr := Type.add_ty_constraint ~pos t1 t2 !cstr

let add_fresh_constraint cstr pos frsh1 frsh2 =
  Print.debug "Unifying freshness constraints."

let add_dirt_constraint cstr pos drt1 drt2 =
  cstr := Type.add_dirt_constraint ~pos drt1 drt2 !cstr

let add_region_constraint cstr pos rgn1 rgn2 =
  cstr := Type.add_region_constraint ~pos rgn1 rgn2 !cstr

let add_dirty_constraint cstr pos (lst1, t1, drt1) (lst2, t2, drt2) =
  add_fresh_constraint cstr pos lst1 lst2; (* XXX very fishy *)
  add_ty_constraint cstr pos t1 t2;
  add_dirt_constraint cstr pos (Type.DirtParam drt1) (Type.DirtParam drt2)

let join_constraints cstr cstr' =
  cstr := Type.join_constraints cstr' !cstr

let lift_dirty (frsh, t, d) = (frsh, t, Type.DirtParam d)

let ty_of_const = function
  | Common.Integer _ -> Type.int_ty
  | Common.String _ -> Type.string_ty
  | Common.Boolean _ -> Type.bool_ty
  | Common.Float _ -> Type.float_ty

let unify_contexts ~pos ctxs =
  let unify_with_context ctx1 (ctx2, cstrs) =
    let unify (x, t) (ctx2, cstrs)=
      match Common.lookup x ctx2 with
      | None ->
          let u = Type.fresh_ty () in
          ((x, u) :: ctx2, Type.add_ty_constraint pos u t cstrs)
      | Some u ->
          (ctx2, Type.add_ty_constraint pos u t cstrs)
    in
    List.fold_right unify ctx1 (ctx2, cstrs)
  in
  List.fold_right unify_with_context ctxs ([], Type.empty)

let trim_context ~pos ctx vars =
  let trim (x, t) (ctx, cstrs) =
    match Common.lookup x vars with
    | None -> ((x, t) :: ctx, cstrs)
    | Some u -> (ctx, Type.add_ty_constraint pos u t cstrs)
  in
  List.fold_right trim ctx ([], Type.empty)

(* [infer_pattern cstr pp] infers the type of pattern [pp]. It returns the list of pattern
   variables with their types, which are all guaranteed to be fresh parameters, together
   with the type of the whole pattern. *)
let rec infer_pattern (p, pos) =
  (* We do not check for overlaps as all identifiers are distinct - desugar needs to do those *)
  if !disable_typing then [], Type.universal_ty, Type.empty else
  match p with
  | Pattern.Var x ->
      let ty = Type.fresh_ty () in
      [(x, ty)], ty, Type.empty
  | Pattern.As (p, x) ->
      let ctx, ty, cnstrs = infer_pattern p in
      (x, ty) :: ctx, ty, cnstrs
  | Pattern.Nonbinding ->
      [], T.fresh_ty (), Type.empty
  | Pattern.Const const ->
      [], ty_of_const const, Type.empty
  | Pattern.Tuple ps ->
      let infer p (ctx, tys, cnstrs) =
        let ctx', ty', cnstrs' = infer_pattern p in
        ctx' @ ctx, ty' :: tys, just cnstrs' cnstrs
      in
      let ctx, tys, cnstrs = List.fold_right infer ps ([], [], Type.empty) in
      ctx, Type.Tuple tys, cnstrs
  | Pattern.Record [] ->
      assert false
  | Pattern.Record (((fld, _) :: _) as lst) ->
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~pos "Unbound record field label %s" fld
      | Some (ty, (ty_name, us)) ->
          let infer (fld, p) (ctx, cnstrs) =
            begin match C.lookup fld us with
            | None -> Error.typing ~pos "Unexpected field %s in a pattern of type %s." fld ty_name
            | Some ty ->
                let ctx', ty', cnstrs' = infer_pattern p in
                ctx' @ ctx, gather [
                  subtype ~pos ty ty';
                  just cnstrs;
                  just cnstrs'
                ]
            end
        in
        let ctx, cnstrs = List.fold_right infer lst ([], Type.empty) in
        ctx, ty, cnstrs
      end
  | Pattern.Variant (lbl, p) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~pos "Unbound constructor %s" lbl
      | Some (ty, u) ->
        begin match p, u with
          | None, None -> [], ty, Type.empty
          | Some p, Some u ->
              let ctx', ty', cnstrs' = infer_pattern p in
              ctx', ty, gather [
                subtype ~pos u ty';
                just cnstrs'
              ]
          | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument." lbl
          | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument." lbl
        end
      end

let (@@) = Type.join_constraints
let (@!@) = Type.join_disjoint_constraints

let rec infer_abstraction env (p, c) =
  let ctx_p, ty_p, cnstrs_p = infer_pattern p in
  let ctx_c, drty_c, cnstrs_c = infer_comp env c in
  let ctx, cnstrs_ctx = trim_context ~pos:(snd c) ctx_c ctx_p in
  ctx, ty_p, drty_c, gather [
    merge cnstrs_ctx;
    just cnstrs_p;
    just cnstrs_c
  ]

and infer_abstraction2 env (p1, p2, c) =
  let ctx_p1, ty_p1, cnstrs_p1 = infer_pattern p1 in
  let ctx_p2, ty_p2, cnstrs_p2 = infer_pattern p2 in
  let ctx_c, drty_c, cnstrs_c = infer_comp env c in
  let ctx, cnstrs_ctx = trim_context ~pos:(snd c) ctx_c (ctx_p1 @ ctx_p2) in
  ctx, ty_p1, ty_p2, drty_c, gather [
    merge cnstrs_ctx;
    just cnstrs_p1;
    just cnstrs_p2;
    just cnstrs_c
  ]

and infer_let ~pos env defs =
  (* Check for implicit sequencing *)
  (* Refresh freshes *)
  (* Check for duplicate variables *)
  let add_binding (p, c) (env, ctxs, ctxp, frshs, drts, cstrs) =
    let cstr = ref Type.empty in
    let ctx_p, t_p, cstr_p = infer_pattern p in
    let ctx_c, (frsh, t_c, drt), cstr_c = infer_comp env c in
    join_constraints cstr (cstr_p @!@ cstr_c);
    add_ty_constraint cstr (snd c) t_c t_p;
    let ctxs, ctxp, env =
      if nonexpansive (fst c) then
        let env = List.fold_right (fun (x, t) env -> Ctx.extend env x (ctx_c, t_c, cstr_c)) ctx_p env in
        ctxs, [], env
      else
        (* let ctx = List.fold_right (fun (x, t) ctx -> (x, t) :: ctx) ctx_p ctx in *)
        ctx_c :: ctxs, ctx_p @ ctxp, env
    in
    (env, ctxs, ctxp, frsh @ frshs, drt :: drts, !cstr @@ cstrs)
  in  
  let env, ctxs, ctxp, frshs, drts, cstr =
    List.fold_right add_binding defs (env, [], [], [], [], Type.empty) in
  let ctx, cstr_ctxs = unify_contexts ~pos ctxs in
    (env, ctx, ctxp, frshs, drts, cstr_ctxs @@ cstr)


and infer_let_rec ~pos env defs =
  if not (Common.injective fst defs) then
    Error.typing ~pos "Multiply defined recursive value.";

  let lst =
    Common.assoc_map (fun a ->
      let u = T.fresh_ty () in
      (u, a))
      defs

  in
  let cstr = ref Type.empty in
  let vars = Common.assoc_map
    (fun (u, ((p, c) as a)) ->
      let ctx, tp, tc, cstr_c = infer_abstraction env a in
      let t = T.Arrow (tp, tc) in
      add_ty_constraint cstr (snd c) t u;
      join_constraints cstr cstr_c;
      (ctx, t)) lst in
  let ctxs, ctxp =
    List.fold_right
      (fun (x, (ctx, t)) (ctxs, ctxp) -> (ctx :: ctxs, (x, t) :: ctxp)) vars ([], []) in
  let ctx, cstr_c = unify_contexts ~pos ctxs in
  let cstr = cstr_c @@ !cstr in
  let env = List.fold_right (fun (x, (_, t)) env -> Ctx.extend env x (Unify.normalize (ctx, t, cstr))) vars env in
    ctxp, env, ctx, cstr

(* [infer_expr env cstr (e,pos)] infers the type of expression [e] in context
   [env]. It returns the inferred type of [e]. *)
and infer_expr env (e, pos) =
  let ty_scheme = match e with

  | Core.Var x ->
      begin match Ctx.lookup env x with
      | Some (ctx, ty, cnstrs) ->
          (ctx, ty, cnstrs)
      | None ->
          let ty = T.fresh_ty () in
          [(x, ty)], ty, Type.empty
      end

  | Core.Const const -> [], ty_of_const const, Type.empty

  | Core.Tuple es ->
      let infer e (ctx, tys, cnstrs) =
        let ctx', ty', cnstrs' = infer_expr env e in
        ctx' @ ctx, ty' :: tys, just cnstrs' cnstrs
      in
      let ctx, tys, cnstrs = List.fold_right infer es ([], [], Type.empty) in
      ctx, Type.Tuple tys, cnstrs

  | Core.Record [] -> assert false

  | Core.Record (((fld, _) :: _) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos "Fields in a record must be distinct." ;
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~pos "Unbound record field label %s" fld
      | Some (ty, (ty_name, arg_types)) ->
          if List.length lst <> List.length arg_types then
            Error.typing ~pos "malformed record of type %s" ty_name;
          let infer (fld, e) (ctx, cnstrs) =
            begin match C.lookup fld arg_types with
            | None -> Error.typing ~pos "Unexpected field %s in a pattern of type %s." fld ty_name
            | Some ty ->
                let ctx', ty', cnstrs' = infer_expr env e in
                ctx' @ ctx, gather [
                  subtype ~pos ty' ty;
                  just cnstrs;
                  just cnstrs'
                ]
            end
        in
        let ctx, cnstrs = List.fold_right infer lst ([], Type.empty) in
        ctx, ty, cnstrs
      end

  | Core.Variant (lbl, e) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~pos "Unbound constructor %s" lbl
      | Some (ty, arg_type) ->
        begin match e, arg_type with
          | None, None -> [], ty, Type.empty
          | Some e, Some u ->
              let ctx', ty', cnstrs' = infer_expr env e in
              ctx', ty, gather [
                subtype ~pos ty' u;
                just cnstrs'
              ]
          | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument." lbl
          | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument." lbl
        end
      end
      
  | Core.Lambda a ->
      let ctx, ty1, drty2, cnstrs = infer_abstraction env a in
      ctx, T.Arrow (ty1, drty2), cnstrs
      
  | Core.Operation (e, op) ->
      let rgn = T.fresh_region_param () in
      begin match Tctx.infer_operation op rgn with
      | None -> Error.typing ~pos "Unbound operation %s" op
      | Some (ty, (t1, t2)) ->
          let ctx, u, cstr_u = infer_expr env e in
          let d = T.fresh_dirt_param () in
          ctx, T.Arrow (t1, ([], t2, d)), gather [
            subtype ~pos u ty;
            subdirt ~pos (Type.DirtAtom (rgn, op)) (Type.DirtParam d);
            just cstr_u
          ]
      end

  | Core.Handler {Core.operations = ops; Core.value = a_val; Core.finally = a_fin} -> 
      let t_value = T.fresh_ty () in
      let dirt = T.fresh_dirt_param () in
      let t_finally = T.fresh_ty () in
      let t_yield = T.fresh_ty () in
      let constrain_operation ((e, op), a2) (ctx, cnstrs) =
        (* XXX Correct when you know what to put instead of the fresh region .*)
        begin match Tctx.infer_operation op (T.fresh_region_param ()) with
        | None -> Error.typing ~pos "Unbound operation %s in a handler" op
        | Some (ty, (t1, t2)) ->
            let ctxe, u, cstr_e = infer_expr env e in
            let ctxa, u1, tk, u2, cstr_a = infer_abstraction2 env a2 in
            ctxe @ ctxa @ ctx, gather [
              subtype ~pos u ty;
              subtype ~pos t1 u1;
              subtype ~pos (T.Arrow (t2, ([], t_yield, dirt))) tk;
              subdirty ~pos u2 ([], t_yield, dirt);
              just cstr_e;
              just cstr_a;
              just cnstrs
            ]
        end
      in
        let ctxs, cnstrs = List.fold_right constrain_operation ops ([], Type.empty) in
        let ctx1, valt1, valt2, cstr_val = infer_abstraction env a_val in
        let ctx2, fint1, fint2, cstr_fin = infer_abstraction env a_fin in
        ctx1 @ ctx2 @ ctxs, Type.Handler(t_value, t_finally), gather [
          subtype ~pos t_value valt1;
          subdirty ~pos valt2 ([], t_yield, dirt);
          subdirty ~pos fint2 ([], t_finally, dirt);
          subtype ~pos t_yield fint1;
          just cstr_val;
          just cstr_fin;
          just cnstrs
        ]

  in
  let ctx, ty, cstr = Unify.normalize (canonize_context ~pos ty_scheme) in
  Print.debug "Type of %t is (%t) %t | %t" (Print.expression (e, pos)) (Print.context ctx) (Print.ty Trio.empty ty) (Print.constraints Trio.empty cstr);
  (ctx, ty, cstr)
              
(* [infer_comp env cstr (c,pos)] infers the type of computation [c] in context [env].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp env (c, pos) =
  (* XXX Why isn't it better to just not call type inference when type checking is disabled? *)
  (* Print.debug "Inferring type of %t" (Print.computation (c, pos)); *)
  if !disable_typing then ([], ([], Type.Basic "_", Type.fresh_dirt_param ()), Type.empty) else
  let rec infer env (c, pos) =
    let ctx, (frsh, ty, drt), cstr = match c with
      | Core.Apply (e1, e2) ->
          let ctx1, ty1, cnstrs1 = infer_expr env e1 in
          let ctx2, ty2, cnstrs2 = infer_expr env e2 in
          let drty = T.fresh_dirty () in
          ctx1 @ ctx2, lift_dirty drty, gather [
            subtype ~pos ty1 (T.Arrow (ty2, drty));
            just cnstrs1;
            just cnstrs2
          ]

      | Core.Value e ->
          let ctx, ty, cnstrs = infer_expr env e in
          ctx, ([], ty, Type.DirtEmpty), cnstrs

      | Core.Match (e, []) ->
          let ctx, ty_in, cnstrs = infer_expr env e in
          let ty_out = Type.fresh_ty () in
          ctx, ([], ty_out, Type.DirtEmpty), gather [
            subtype ~pos ty_in Type.empty_ty;
            just cnstrs
          ]

      | Core.Match (e, cases) ->
          let ctx_in, ty_in, cnstrs_in = infer_expr env e in
          let ty_out = T.fresh_ty () in
          let drt_out = T.fresh_dirt () in
          let infer_case ((p, c) as a) (ctx, frshs, cnstrs) =
            (* XXX Refresh fresh instances *)
            let ctx', ty_in', (frsh_out, ty_out', drt_out'), cnstrs' = infer_abstraction env a in
            ctx' @ ctx, frsh_out @ frshs, gather [
              subtype ~pos:(snd e) ty_in ty_in';
              subtype ~pos:(snd c) ty_out' ty_out;
              subdirt ~pos:(snd c) (Type.DirtParam drt_out') drt_out;
              just cnstrs';
              just cnstrs
            ]
          in
          let ctx, frshs, cnstrs = List.fold_right infer_case cases (ctx_in, [], cnstrs_in) in
          ctx, (frshs, ty_out, drt_out), cnstrs
              
      | Core.New (eff, r) ->
          begin match Tctx.fresh_tydef ~pos:pos eff with
          | (params, Tctx.Effect ops) ->
              let ctx, cnstrs = begin match r with
              | None -> [], Type.empty
              | Some (e, lst) ->
                  let ctxe, te, cstr_e = infer_expr env e in
                  let infer (op, a) (ctx, cstrs) =
                    match Common.lookup op ops with
                    | None -> Error.typing ~pos "Effect type %s does not have operation %s" eff op
                    | Some (u1, u2) ->
                        let ctx', t1, t2, t, cstr_a = infer_abstraction2 env a in
                        let d_empty = T.fresh_dirt_param () in
                        ctx' @ ctx, gather [
                          subtype ~pos(* p1 *) t1 u1;
                          subtype ~pos(* p2 *) t2 te;
                          subdirt ~pos(* c *) (Type.DirtParam d_empty) (Type.DirtEmpty);
                          subdirty ~pos(* c *) t ([], T.Tuple [u2; te], d_empty);
                          just cstr_a;
                          just cstrs
                        ]
                  in
                  List.fold_right infer lst (ctxe, cstr_e)
              end
              in
              let instance = T.fresh_instance_param () in
              let rgn = T.fresh_region_param () in
              ctx, ([instance], Tctx.effect_to_params eff params rgn, Type.DirtEmpty), gather [
                subregion ~pos (Type.RegionAtom (Type.InstanceParam instance)) (Type.RegionParam rgn);
                just cnstrs
              ]
          | _ -> Error.typing ~pos "Effect type expected but %s encountered" eff
          end

      | Core.While (c1, c2) ->
          let ctx1, frsh1, t1, drt1, cnstrs1 = infer env c1 in
          let ctx2, frsh2, t2, drt2, cnstrs2 = infer env c2 in
          let drt = Type.fresh_dirt () in
          (* XXX We must erase all instances generated by c2 *)
          ctx1 @ ctx2, (frsh1, T.unit_ty, drt), gather [
            subtype ~pos t1 Type.bool_ty;
            subtype ~pos t2 Type.unit_ty;
            subdirt ~pos drt1 drt;
            subdirt ~pos drt2 drt;
            just cnstrs1;
            just cnstrs2
          ]

      | Core.For (i, e1, e2, c, _) ->
          let ctx1, ty1, cnstrs1 = infer_expr env e1 in
          let ctx2, ty2, cnstrs2 = infer_expr env e2 in
          let ctx3, frsh, ty, drt, cnstrs3 = infer env c in
          (* XXX We must erase all instances generated by c *)
          ctx1 @ ctx2 @ ctx3, ([], T.unit_ty, drt), gather [
            subtype ~pos:(snd e1) ty1 Type.int_ty;
            subtype ~pos:(snd e2) ty2 Type.int_ty;
            subtype ~pos:(snd c) ty Type.unit_ty;
            just cnstrs1;
            just cnstrs2;
            just cnstrs3
          ]

      | Core.Handle (e1, c2) ->
          let ctx1, ty1, cnstrs1 = infer_expr env e1 in
          let ctx2, frsh, ty2, drt2, cnstrs2 = infer env c2 in
          let ty3 = T.fresh_ty () in
          ctx1 @ ctx2, (frsh, ty3, drt2), gather [
            subtype ~pos ty1 (T.Handler (ty2, ty3));
            just cnstrs1;
            just cnstrs2
          ]

      | Core.Let (defs, c) -> 
          let cstr = ref Type.empty in
          let env, ctx1, ctxp, let_frshs, let_drts, cstrs = infer_let ~pos env defs in
          let ctx2, frsh, tc, dc, cstr_c = infer env c in
          let ctx, cstr_cs = unify_contexts ~pos [ctx1; ctx2] in
          let ctx, cstr_diff = trim_context ~pos ctx ctxp in
          let drt = Type.fresh_dirt () in
            List.iter (fun let_drt -> add_dirt_constraint cstr pos (Type.DirtParam let_drt) drt) let_drts;
            add_dirt_constraint cstr pos dc drt ;
            join_constraints cstr ((cstr_c @!@ cstrs) @@ cstr_cs @@ cstr_diff);
            ctx, (let_frshs @ frsh, tc, drt), !cstr

      | Core.LetRec (defs, c) ->
          let cstr = ref Type.empty in
          let vars, env, ctx1, cstrs = infer_let_rec ~pos env defs in
          let ctx2, frsh, tc, dc, cstr_c = infer env c in
          let ctx, cstr_cs = unify_contexts ~pos [ctx1; ctx2] in
          let ctx, cstr_diff = trim_context ~pos ctx vars in
          join_constraints cstr ((cstr_c @!@ cstrs) @@ cstr_cs @@ cstr_diff);
          ctx, (frsh, tc, dc), !cstr

      | Core.Check c ->
          ignore (infer env c);
          [], ([], T.unit_ty, Type.DirtEmpty), Type.empty
    in
    let ctx, ty, cstr = Unify.normalize (canonize_context ~pos (ctx, ty, cstr)) in
    ctx, frsh, ty, drt, cstr
  in
  let ctx, frsh, ty, drt, cstr = infer env (c, pos) in
  let d = T.fresh_dirt_param () in
  Print.debug "Type of %t is (%t) %t | %t" (Print.computation (c, pos)) (Print.context ctx) (Print.ty Trio.empty ty) (Print.constraints Trio.empty cstr);
  ctx, (frsh, ty, d), (Type.add_dirt_constraint pos drt (Type.DirtParam d) cstr)

