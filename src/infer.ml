module C = Common
module T = Type

let warn_implicit_sequencing = ref false;;

let disable_typing = ref false;;

let ty_less = Scheme.ty_less
let dirt_less = Scheme.dirt_less
let region_covers = Scheme.region_covers
let dirty_less = Scheme.dirty_less
let just = Scheme.just
let trim_context = Scheme.trim_context

(* Can a computation safely be generalized, i.e., is it non-expansive in the parlance of
   SML? In our case non-expansive simply means "is a value". *)
let nonexpansive = function
  | Core.Value _ -> true
  | Core.Apply _ | Core.Match _ | Core.While _ | Core.For _ | Core.New _
  | Core.Handle _ | Core.Let _ | Core.LetRec _ | Core.Check _ -> false

let simple ty = ([], ty, Constraints.empty)
let empty_dirt () = { Type.ops = []; Type.rest = Type.fresh_dirt_param () }

let ty_of_const = function
  | Common.Integer _ -> Type.int_ty
  | Common.String _ -> Type.string_ty
  | Common.Boolean _ -> Type.bool_ty
  | Common.Float _ -> Type.float_ty

(* [infer_pattern p] infers the type of pattern [p]. It returns the list of pattern
   variables with their types, which are all guaranteed to be fresh parameters, together
   with the type of the whole pattern. *)
let rec infer_pattern (p, pos) =
  (* We do not check for overlaps as all identifiers are distinct - desugar needs to do those *)
  if !disable_typing then simple Type.universal_ty else
  let unify = Scheme.finalize_pattern_scheme ~pos in
  let ty_sch = match p with
  | Pattern.Var x ->
      let ty = Type.fresh_ty () in
      [(x, ty)], ty, Constraints.empty
  | Pattern.As (p, x) ->
      let ctx, ty, cnstrs = infer_pattern p in
      (x, ty) :: ctx, ty, cnstrs
  | Pattern.Nonbinding -> simple (Type.fresh_ty ())
  | Pattern.Const const -> simple (ty_of_const const)
  | Pattern.Tuple ps ->
      let infer p (ctx, tys, cnstrs) =
        let ctx', ty', cnstrs' = infer_pattern p in
        ctx' @ ctx, ty' :: tys, just cnstrs' :: cnstrs
      in
      let ctx, tys, cnstrs = List.fold_right infer ps ([], [], []) in
      unify ctx (Type.Tuple tys) cnstrs
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
                ctx' @ ctx, [
                  ty_less ~pos ty ty';
                  just cnstrs'
                ] @ cnstrs;
            end
        in
        let ctx, cnstrs = List.fold_right infer lst ([], []) in
        unify ctx ty cnstrs
      end
  | Pattern.Variant (lbl, p) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~pos "Unbound constructor %s" lbl
      | Some (ty, u) ->
        begin match p, u with
          | None, None -> simple ty
          | Some p, Some u ->
              let ctx', ty', cnstrs' = infer_pattern p in
              unify ctx' ty [
                ty_less ~pos u ty';
                just cnstrs'
              ]
          | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument." lbl
          | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument." lbl
        end
      end
  in
  Print.debug "%t : %t" (Core.print_pattern (p, pos)) (Scheme.print_ty_scheme ty_sch);
  ty_sch

(* [infer_expr env cstr (e,pos)] infers the type of expression [e] in context
   [env]. It returns the inferred type of [e]. *)
let rec infer_expr env (e, pos) =
  if !disable_typing then simple Type.universal_ty else
  let unify = Scheme.finalize_ty_scheme ~pos in
  let ty_sch = match e with

  | Core.Var x ->
      begin match Ctx.lookup env x with
      | Some (ctx, ty, cnstrs) ->
          (ctx, ty, cnstrs)
      | None ->
          let ty = T.fresh_ty () in
          let ty' = T.fresh_ty () in
          unify [(x, ty)] ty' [ty_less ~pos ty ty']
      end

  | Core.Const const -> simple (ty_of_const const)

  | Core.Tuple es ->
      let infer e (ctx, tys, cnstrs) =
        let ctx', ty', cnstrs' = infer_expr env e in
        ctx' @ ctx, ty' :: tys, just cnstrs' :: cnstrs
      in
      let ctx, tys, cnstrs = List.fold_right infer es ([], [], []) in
      unify ctx (Type.Tuple tys) cnstrs

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
                ctx' @ ctx, [
                  ty_less ~pos ty' ty;
                  just cnstrs'
                ] @ cnstrs
            end
        in
        let ctx, cnstrs = List.fold_right infer lst ([], []) in
        unify ctx ty cnstrs
      end

  | Core.Variant (lbl, e) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~pos "Unbound constructor %s" lbl
      | Some (ty, arg_type) ->
        begin match e, arg_type with
          | None, None -> simple ty
          | Some e, Some u ->
              let ctx', ty', cnstrs' = infer_expr env e in
              unify ctx' ty [
                ty_less ~pos ty' u;
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
      let r = T.fresh_region_param () in
      begin match Tctx.infer_operation op r with
      | None -> Error.typing ~pos "Unbound operation %s" op
      | Some (ty, (t1, t2)) ->
          let ctx, u, cstr_u = infer_expr env e in
          let rt = Type.fresh_region_param () in
          unify ctx (T.Arrow (t1, (t2, {T.ops = [op, rt]; T.rest = Type.fresh_dirt_param ()}))) [
            ty_less ~pos u ty;
            Scheme.add_region_bound rt [Constraints.Region r];
            just cstr_u
          ]
      end

  | Core.Handler {Core.operations = ops; Core.value = a_val; Core.finally = a_fin} -> 
      let t_value = T.fresh_ty () in
      let dirt = T.fresh_dirt () in
      let t_finally = T.fresh_ty () in
      let t_yield = T.fresh_ty () in
      let constrain_operation ((e, op), a2) (ctx, cnstrs, ops) =
        (* XXX Correct when you know what to put instead of the fresh region .*)
        let r = T.fresh_region_param () in
        begin match Tctx.infer_operation op r with
        | None -> Error.typing ~pos "Unbound operation %s in a handler" op
        | Some (ty, (t1, t2)) ->
            let ctxe, u, cstr_e = infer_expr env e in
            let ctxa, u1, tk, u2, cstr_a = infer_abstraction2 env a2 in
            let ops =
              begin match Common.lookup op ops with
              | None -> (op, ref [r]) :: ops
              | Some rs -> rs := r :: !rs; ops
              end
              in
            ctxe @ ctxa @ ctx, [
              ty_less ~pos u ty;
              ty_less ~pos t1 u1;
              ty_less ~pos (T.Arrow (t2, (t_yield, dirt))) tk;
              dirty_less ~pos u2 (t_yield, dirt);
              just cstr_e;
              just cstr_a
            ] @ cnstrs, ops
        end
      in
        let ctxs, cnstrs, ops = List.fold_right constrain_operation ops ([], [], []) in
        let ctx1, valt1, valt2, cstr_val = infer_abstraction env a_val in
        let ctx2, fint1, (fint2, findrt), cstr_fin = infer_abstraction env a_fin in
        let drt_rest = Type.fresh_dirt_param () in
        (* XXX *)
        let make_dirt (op, rs) (left_dirt, right_dirt, cnstrs) =
          let pres = Type.fresh_region_param () in
          let without = Type.fresh_region_param () in
          (* Print.info "DIRT: %t >= %t" (Print.dirt_param without) (Print.dirt (Type.Without (pres, !rs))); *)
          ((op, pres) :: left_dirt, (op, without) :: right_dirt, Scheme.add_region_bound without [Constraints.Without (pres, !rs)] :: cnstrs)
        in
        let left_rops, right_rops, cnstrs_ops =
          List.fold_right make_dirt ops ([], [], []) in
(*         let left_rops = List.map (fun rop -> (rop, Type.Present)) rops
        and right_rops = List.map (fun rop -> (rop, Type.Absent)) rops in
 *)        unify (ctx1 @ ctx2 @ ctxs) (Type.Handler((t_value, {Type.ops = left_rops; Type.rest = drt_rest}), (t_finally, dirt))) ([
          (* dirt_handles_ops drt_value rops; *)
          dirt_less ~pos {Type.ops = right_rops; Type.rest = drt_rest} dirt;
          ty_less ~pos t_value valt1;
          dirty_less ~pos valt2 (t_yield, dirt);
          ty_less ~pos fint2 t_finally;
          dirt_less ~pos findrt dirt;
          ty_less ~pos t_yield fint1;
          just cstr_val;
          just cstr_fin
        ] @ cnstrs_ops @ cnstrs)
  in
  Print.debug "%t : %t" (Core.print_expression (e, pos)) (Scheme.print_ty_scheme ty_sch);
  ty_sch
              
(* [infer_comp env cstr (c,pos)] infers the type of computation [c] in context [env].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp env (c, pos) =
  if !disable_typing then simple Type.universal_dirty else
  let unify = Scheme.finalize_dirty_scheme ~pos in
  let drty_sch = match c with

  | Core.Value e ->
      let ctx, ty, cnstrs = infer_expr env e in
      ctx, (ty, empty_dirt ()), cnstrs

  | Core.Let (defs, c) -> 
      let env, _, change = infer_let ~pos env defs in
      change (infer_comp env c)

  | Core.LetRec (defs, c) ->
      let env, _, change = infer_let_rec ~pos env defs in
      change (infer_comp env c)

  | Core.Match (e, []) ->
      let ctx, ty_in, cnstrs = infer_expr env e in
      let ty_out = Type.fresh_ty () in
      unify ctx (ty_out, empty_dirt ()) [
        ty_less ~pos ty_in Type.empty_ty;
        just cnstrs
      ]

  | Core.Match (e, cases) ->
      let ctx_in, ty_in, cnstrs_in = infer_expr env e in
      let drty_out = T.fresh_dirty () in
      let infer_case ((p, c) as a) (ctx, cnstrs) =
        (* XXX Refresh fresh instances *)
        let ctx', ty_in', drty_out', cnstrs' = infer_abstraction env a in
        ctx' @ ctx, [
          ty_less ~pos:(snd e) ty_in ty_in';
          dirty_less ~pos:(snd c) drty_out' drty_out;
          just cnstrs'
        ] @ cnstrs
      in
      let ctx, cnstrs = List.fold_right infer_case cases (ctx_in, [just cnstrs_in]) in
      unify ctx drty_out cnstrs

  | Core.While (c1, c2) ->
      let ctx1, (ty1, drt1), cnstrs1 = infer_comp env c1 in
      let ctx2, (ty2, drt2), cnstrs2 = infer_comp env c2 in
      let drt = Type.fresh_dirt () in
      (* XXX We must erase all instances generated by c2 *)
      unify (ctx1 @ ctx2) (T.unit_ty, drt) [
        ty_less ~pos ty1 Type.bool_ty;
        ty_less ~pos ty2 Type.unit_ty;
        dirt_less ~pos drt1 drt;
        dirt_less ~pos drt2 drt;
        just cnstrs1;
        just cnstrs2
      ]

  | Core.For (i, e1, e2, c, _) ->
      let ctx1, ty1, cnstrs1 = infer_expr env e1 in
      let ctx2, ty2, cnstrs2 = infer_expr env e2 in
      let ctx3, (ty, drt), cnstrs3 = infer_comp env c in
      (* XXX We must erase all instances generated by c *)
      unify (ctx1 @ ctx2 @ ctx3) (T.unit_ty, drt) [
        ty_less ~pos:(snd e1) ty1 Type.int_ty;
        ty_less ~pos:(snd e2) ty2 Type.int_ty;
        ty_less ~pos:(snd c) ty Type.unit_ty;
        just cnstrs1;
        just cnstrs2;
        just cnstrs3
      ]

  | Core.Apply (e1, e2) ->
      let ctx1, ty1, cnstrs1 = infer_expr env e1 in
      let ctx2, ty2, cnstrs2 = infer_expr env e2 in
      let drty = T.fresh_dirty () in
      unify (ctx1 @ ctx2) drty [
        ty_less ~pos ty1 (T.Arrow (ty2, drty));
        just cnstrs1;
        just cnstrs2
      ]

  | Core.New (eff, r) ->
      begin match Tctx.fresh_tydef ~pos:pos eff with
      | (params, Tctx.Effect ops) ->
          let ctx, cnstrs = begin match r with
          | None -> [], []
          | Some (e, lst) ->
              let ctxe, te, cstr_e = infer_expr env e in
              let infer (op, a) (ctx, cstrs) =
                match Common.lookup op ops with
                | None -> Error.typing ~pos "Effect type %s does not have operation %s" eff op
                | Some (u1, u2) ->
                    let ctx', t1, t2, t, cstr_a = infer_abstraction2 env a in
                    let d_empty = T.fresh_dirt () in
                    ctx' @ ctx, [
                      ty_less ~pos(* p1 *) u1 t1;
                      ty_less ~pos(* p2 *) te t2;
                      (* XXX Warn that d_empty has to be empty *)
                      (* dirt_pure c d_empty; *)
                      dirty_less ~pos(* c *) t (T.Tuple [u2; te], d_empty);
                      just cstr_a
                    ] @ cstrs
              in
              List.fold_right infer lst (ctxe, [just cstr_e])
          end
          in
          let instance = T.fresh_instance_param () in
          let rgn = T.fresh_region_param () in
          unify ctx (Tctx.effect_to_params eff params rgn, empty_dirt ()) ([
                      region_covers rgn instance;
                    ] @ cnstrs)
      | _ -> Error.typing ~pos "Effect type expected but %s encountered" eff
      end

  | Core.Handle (e1, c2) ->
      let ctx1, ty1, cnstrs1 = infer_expr env e1
      and ctx2, (ty2, drt2), cnstrs2 = infer_comp env c2
      and ty_in = T.fresh_ty ()
      and drt_in = T.fresh_dirt ()
      and ty_out, drt_out = T.fresh_dirty () in
      unify (ctx1 @ ctx2) (ty_out, drt_out) [
        ty_less ~pos ty1 (T.Handler ((ty_in, drt_in), (ty_out, drt_out)));
        ty_less ~pos ty2 ty_in;
        dirt_less ~pos drt2 drt_in;
        just cnstrs1;
        just cnstrs2
      ]

  | Core.Check c ->
      ignore (infer_comp env c);
      simple (T.unit_ty, empty_dirt ())

  in
  Print.debug "%t : %t" (Core.print_computation (c, pos)) (Scheme.print_dirty_scheme drty_sch);
  drty_sch

and infer_abstraction env (p, c) =
  let ctx_p, ty_p, cnstrs_p = infer_pattern p in
  let ctx_c, drty_c, cnstrs_c = infer_comp env c in
  match Scheme.finalize_ty_scheme ~pos:(snd c) ctx_c (Type.Arrow (ty_p, drty_c)) [
    trim_context ~pos:(snd c) ctx_p;
    just cnstrs_p;
    just cnstrs_c
  ] with
  | ctx, Type.Arrow (ty_p, drty_c), cnstrs -> ctx, ty_p, drty_c, cnstrs
  | _ -> assert false

and infer_abstraction2 env (p1, p2, c) =
  let ctx_p1, ty_p1, cnstrs_p1 = infer_pattern p1 in
  let ctx_p2, ty_p2, cnstrs_p2 = infer_pattern p2 in
  let ctx_c, drty_c, cnstrs_c = infer_comp env c in
  match Scheme.finalize_ty_scheme ~pos:(snd c) ctx_c (Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c)) [
  trim_context ~pos:(snd c) (ctx_p1 @ ctx_p2);
    just cnstrs_p1;
    just cnstrs_p2;
    just cnstrs_c
  ] with
  | ctx, Type.Arrow (Type.Tuple [ty_p1; ty_p2], drty_c), cnstrs -> ctx, ty_p1, ty_p2, drty_c, cnstrs
  | _ -> assert false

and infer_let ~pos env defs =
  (* Check for implicit sequencing *)
  (* Refresh freshes *)
  (* Check for duplicate variables *)
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (env, ctxs, ctxp, vars, cstrs) =
    let ctx_p, t_p, cstr_p = infer_pattern p in
    let ctx_c, (t_c, drt'), cstr_c = infer_comp env c in
    let vars = (List.map fst ctx_p) @ vars in
    let changes = [
      ty_less ~pos:(snd c) t_c t_p;
      dirt_less ~pos:(snd c) drt' drt;
      just cstr_p;
      just cstr_c
    ]
    in
    let env, ctxp =
      if nonexpansive (fst c) then
        let env = List.fold_right (fun (x, t) env -> Ctx.extend env x (Scheme.finalize_ty_scheme ~pos ctx_c t changes)) ctx_p env in
        env, ctxp
      else
        env, ctx_p @ ctxp
    in
    env, ctx_c @ ctxs, ctxp, vars, changes @ cstrs
  in
  let env, ctxs, ctxp, vars, cstrs = List.fold_right add_binding defs (env, [], [], [], []) in
  env, vars, fun (ctx2, (tc, dc), cstr_c) ->
    Scheme.finalize_dirty_scheme ~pos (ctxs @ ctx2) (tc, drt) ([
          dirt_less ~pos dc drt;
          trim_context ~pos ctxp;
          just cstr_c;
        ] @ cstrs)

and infer_let_rec ~pos env defs =
  if not (Common.injective fst defs) then Error.typing ~pos "Multiply defined recursive value.";
  let infer (x, ((p, c) as a)) (vars, ctx, cnstrs) =
    let ctx', tp, tc, cnstrs_a = infer_abstraction env a in
    (x, Type.Arrow (tp, tc)) :: vars, ctx' @ ctx, [
      just cnstrs_a
    ] @ cnstrs
  in
  let vars, ctx, cnstrs = List.fold_right infer defs ([], [], []) in
  let cnstrs = [
    trim_context ~pos vars
  ] @ cnstrs
 in
  let env = List.fold_right (fun (x, t) env -> Ctx.extend env x (Scheme.finalize_ty_scheme ~pos ctx t cnstrs)) vars env in
  env, vars, fun (ctx2, (tc, dc), cstr_c) ->
  Scheme.finalize_dirty_scheme ~pos (ctx @ ctx2) (tc, dc) (just cstr_c :: cnstrs)
