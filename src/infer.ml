module C = Common
module T = Type

let warn_implicit_sequencing = ref false;;
let disable_typing = ref false;;

let ty_less = Scheme.ty_less
let dirt_less = Scheme.dirt_less
let dirty_less = Scheme.dirty_less
let just = Scheme.just
let trim_context = Scheme.trim_context

let simple ty = ([], ty, Constraints.empty)
let empty_dirt () = { Type.ops = []; Type.rest = Type.fresh_dirt_param () }

let ty_of_const = function
  | Common.Integer _ -> Type.int_ty
  | Common.String _ -> Type.string_ty
  | Common.Boolean _ -> Type.bool_ty
  | Common.Float _ -> Type.float_ty

(* [infer_pattern p] infers the type scheme of a pattern [p].
   This consists of:
   - the context, which contains bound variables and their types,
   - the type of the whole pattern (what it matches against), and
   - constraints connecting all these types.
   Note that unlike in ordinary type schemes, context types are positive while
   pattern type is negative. *)
let rec infer_pattern (p, pos) =
  if !disable_typing then simple Type.universal_ty else
  let unify = Scheme.finalize_pattern_scheme in
  let ty_sch = match p with

  | Pattern.Var x ->
      let ty = Type.fresh_ty () in
      [(x, ty)], ty, Constraints.empty

  | Pattern.As (p, x) ->
      let ctx, ty, cnstrs = infer_pattern p in
      (x, ty) :: ctx, ty, cnstrs

  | Pattern.Nonbinding ->
      simple (Type.fresh_ty ())

  | Pattern.Const const ->
      simple (ty_of_const const)

  | Pattern.Tuple ps ->
      let infer p (ctx, tys, chngs) =
        let ctx_p, ty_p, cnstrs_p = infer_pattern p in
        ctx_p @ ctx, ty_p :: tys, [
          just cnstrs_p
        ] @ chngs
      in
      let ctx, tys, chngs = List.fold_right infer ps ([], [], []) in
      unify ctx (Type.Tuple tys) chngs

  | Pattern.Record [] ->
      assert false

  | Pattern.Record (((fld, _) :: _) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos "Fields in a record must be distinct";
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~pos "Unbound record field label %s" fld
      | Some (ty, (ty_name, fld_tys)) ->
          let infer (fld, p) (ctx, chngs) =
            begin match C.lookup fld fld_tys with
            | None -> Error.typing ~pos "Unexpected field %s in a pattern of type %s" fld ty_name
            | Some fld_ty ->
                let ctx_p, ty_p, cnstrs_p = infer_pattern p in
                ctx_p @ ctx, [
                  ty_less ~pos fld_ty ty_p;
                  just cnstrs_p
                ] @ chngs
            end
        in
        let ctx, chngs = List.fold_right infer lst ([], []) in
        unify ctx ty chngs
      end

  | Pattern.Variant (lbl, p) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~pos "Unbound constructor %s" lbl
      | Some (ty, arg_ty) ->
          begin match p, arg_ty with
            | None, None -> simple ty
            | Some p, Some arg_ty ->
                let ctx_p, ty_p, cnstrs_p = infer_pattern p in
                unify ctx_p ty [
                  ty_less ~pos arg_ty ty_p;
                  just cnstrs_p
                ]
            | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument" lbl
            | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument" lbl
          end
      end

  in
  (* Print.debug "%t : %t" (Syntax.print_pattern (p, pos)) (Scheme.print_ty_scheme ty_sch); *)
  ty_sch

(* [infer_expr env e] infers the type scheme of an expression [e] in a
   typing environment [env] of generalised variables.
   The scheme consists of:
   - the context, which contains non-generalised variables and their types,
   - the type of the expression, and
   - constraints connecting all these types. *)
let rec infer_expr env (e, pos) =
  if !disable_typing then simple Type.universal_ty else
  let unify = Scheme.finalize_ty_scheme ~pos in
  let ty_sch = match e with

  | Syntax.Var x ->
      begin match Ctx.lookup env x with
      | Some (ctx, ty, cnstrs) ->
          (ctx, ty, cnstrs)
      | None ->
          let ty = Type.fresh_ty () in
          unify [(x, ty)] ty []
      end

  | Syntax.Const const ->
      simple (ty_of_const const)

  | Syntax.Tuple es ->
      let infer e (ctx, tys, chngs) =
        let ctx_e, ty_e, cnstrs_e = infer_expr env e in
        ctx_e @ ctx, ty_e :: tys, [
          just cnstrs_e
        ] @ chngs
      in
      let ctx, tys, chngs = List.fold_right infer es ([], [], []) in
      unify ctx (Type.Tuple tys) chngs

  | Syntax.Record [] ->
      assert false

  | Syntax.Record (((fld, _) :: _) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos "Fields in a record must be distinct";
      begin match Tctx.infer_field fld with
      | None -> Error.typing ~pos "Unbound record field label %s" fld
      | Some (ty, (ty_name, fld_tys)) ->
          if List.length lst <> List.length fld_tys then
            Error.typing ~pos "The record of type %s has an incorrect number of fields" ty_name;
          let infer (fld, e) (ctx, chngs) =
            begin match C.lookup fld fld_tys with
            | None -> Error.typing ~pos "Unexpected field %s in a record of type %s" fld ty_name
            | Some fld_ty ->
                let ctx_e, ty_e, cnstrs_e = infer_expr env e in
                ctx_e @ ctx, [
                  ty_less ~pos ty_e fld_ty;
                  just cnstrs_e
                ] @ chngs
            end
        in
        let ctx, chngs = List.fold_right infer lst ([], []) in
        unify ctx ty chngs
      end

  | Syntax.Variant (lbl, e) ->
      begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~pos "Unbound constructor %s" lbl
      | Some (ty, arg_ty) ->
          begin match e, arg_ty with
            | None, None -> simple ty
            | Some e, Some arg_ty ->
                let ctx_e, ty_e, cnstrs_e = infer_expr env e in
                unify ctx_e ty [
                  ty_less ~pos ty_e arg_ty;
                  just cnstrs_e
                ]
            | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument" lbl
            | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument" lbl
          end
      end
      
  | Syntax.Lambda a ->
      let ctx, ty1, drty2, cnstrs = infer_abstraction env a in
      ctx, Type.Arrow (ty1, drty2), cnstrs
      
  | Syntax.Operation (e, op) ->
      let r = Type.fresh_region_param () in
      begin match Tctx.infer_operation op r with
      | None -> Error.typing ~pos "Unbound operation %s" op
      | Some (eff_ty, (ty_par, ty_res)) ->
          let ctx_e, ty_e, cnstrs_e = infer_expr env e in
          let drt = {Type.ops = [op, r]; Type.rest = Type.fresh_dirt_param ()} in
          unify ctx_e (Type.Arrow (ty_par, (ty_res, drt))) [
            ty_less ~pos ty_e eff_ty;
            just cnstrs_e
          ]
      end

  | Syntax.Handler {Syntax.operations = ops; Syntax.value = a_val; Syntax.finally = a_fin} -> 
      let drt_mid = Type.fresh_dirt () in
      let ty_mid = Type.fresh_ty () in

      let infer ((e, op), a2) (ctx, chngs, ops) =
        let r = Type.fresh_region_param () in
        begin match Tctx.infer_operation op r with
        | None -> Error.typing ~pos "Unbound operation %s in a handler" op
        | Some (eff_ty, (ty_par, ty_arg)) ->
            let ctx_e, ty_e, cnstrs_e = infer_expr env e in
            let ctx_a, ty_p, ty_k, drty_c, cnstrs_a = infer_abstraction2 env a2 in
            let ops =
              begin match Common.lookup op ops with
              | None -> (op, ref [r]) :: ops
              | Some rs -> rs := r :: !rs; ops
              end
              in
            ctx_e @ ctx_a @ ctx, [
              ty_less ~pos ty_e eff_ty;
              ty_less ~pos ty_par ty_p;
              ty_less ~pos (Type.Arrow (ty_arg, (ty_mid, drt_mid))) ty_k;
              dirty_less ~pos drty_c (ty_mid, drt_mid);
              just cnstrs_e;
              just cnstrs_a
            ] @ chngs, ops
        end
      in
      let ctxs, chngs, ops = List.fold_right infer ops ([], [], []) in

      let make_dirt (op, rs) (ops_in, ops_out, chngs) =
        let r_in = Type.fresh_region_param () in
        let r_out = Type.fresh_region_param () in
        let chngs = [
          Scheme.add_handled_constraint r_in r_out !rs
        ] @ chngs
        in
        (op, r_in) :: ops_in, (op, r_out) :: ops_out, chngs
      in
      let ops_in, ops_out, chngs_ops = List.fold_right make_dirt ops ([], [], []) in

      let ctx_val, ty_val, drty_val, cnstrs_val = infer_abstraction env a_val in
      let ctx_fin, ty_fin, drty_fin, cnstrs_fin = infer_abstraction env a_fin in

      let ty_in = Type.fresh_ty () in
      let drt_rest = Type.fresh_dirt_param () in
      let drt_in = {Type.ops = ops_in; Type.rest = drt_rest} in
      let drt_out = Type.fresh_dirt () in
      let ty_out = Type.fresh_ty () in

      unify (ctx_val @ ctx_fin @ ctxs) (Type.Handler((ty_in, drt_in), (ty_out, drt_out))) ([
        dirt_less ~pos {Type.ops = ops_out; Type.rest = drt_rest} drt_mid;
        ty_less ~pos ty_in ty_val;
        dirty_less ~pos drty_val (ty_mid, drt_mid);
        ty_less ~pos ty_mid ty_fin;
        dirt_less ~pos drt_mid drt_out;
        dirty_less ~pos drty_fin (ty_out, drt_out);
        just cnstrs_val;
        just cnstrs_fin
      ] @ chngs_ops @ chngs)

  in
  (* Print.debug "%t : %t" (Syntax.print_expression (e, pos)) (Scheme.print_ty_scheme ty_sch); *)
  ty_sch
              
(* [infer_comp env c] infers the dirty type scheme of a computation [c] in a
   typing environment [env] of generalised variables.
   The scheme consists of:
   - the context, which contains non-generalised variables and their types,
   - the type of the expression,
   - the dirt of the computation, and
   - constraints connecting all these types. *)
and infer_comp env (c, pos) =
  if !disable_typing then simple Type.universal_dirty else
  let unify = Scheme.finalize_dirty_scheme ~pos in
  let drty_sch = match c with

  | Syntax.Value e ->
      let ctx, ty, cnstrs = infer_expr env e in
      ctx, (ty, empty_dirt ()), cnstrs

  | Syntax.Let (defs, c) ->
      let vars, nonpoly, change = infer_let ~pos env defs in
      let change2 (ctx_c, drty_c, cnstrs_c) =
        Scheme.finalize_dirty_scheme ~pos (ctx_c) drty_c ([
          Scheme.remove_context ~pos nonpoly;
          just cnstrs_c
        ])
      in
      let env' = List.fold_right (fun (x, ty_sch) env -> Ctx.extend env x ty_sch) vars env in
      change2 (change (infer_comp env' c))

  | Syntax.LetRec (defs, c) ->
      let vars, change = infer_let_rec ~pos env defs in
      let env' = List.fold_right (fun (x, ty_sch) env -> Ctx.extend env x ty_sch) vars env in
      change (infer_comp env' c)

  | Syntax.Match (e, []) ->
      let ctx_e, ty_e, cnstrs_e = infer_expr env e in
      unify ctx_e (Type.fresh_ty (), empty_dirt ()) [
        ty_less ~pos ty_e Type.empty_ty;
        just cnstrs_e
      ]

  | Syntax.Match (e, cases) ->
      let ctx_e, ty_e, cnstrs_e = infer_expr env e in
      let drty = Type.fresh_dirty () in
      let infer_case ((p, c) as a) (ctx, chngs) =
        let ctx_a, ty_p, drty_c, cnstrs_a = infer_abstraction env a in
        ctx_a @ ctx, [
          ty_less ~pos:(snd e) ty_e ty_p;
          dirty_less ~pos:(snd c) drty_c drty;
          just cnstrs_a
        ] @ chngs
      in
      let ctx, chngs = List.fold_right infer_case cases (ctx_e, [just cnstrs_e]) in
      unify ctx drty chngs

  | Syntax.While (c1, c2) ->
      let ctx_c1, (ty_c1, drt_c1), cnstrs_c1 = infer_comp env c1 in
      let ctx_c2, (ty_c2, drt_c2), cnstrs_c2 = infer_comp env c2 in
      let drt = Type.fresh_dirt () in
      unify (ctx_c1 @ ctx_c2) (Type.unit_ty, drt) [
        ty_less ~pos ty_c1 Type.bool_ty;
        ty_less ~pos ty_c2 Type.unit_ty;
        dirt_less ~pos drt_c1 drt;
        dirt_less ~pos drt_c2 drt;
        just cnstrs_c1;
        just cnstrs_c2
      ]

  | Syntax.For (i, e1, e2, c, _) ->
      let ctx_e1, ty_e1, cnstrs_e1 = infer_expr env e1 in
      let ctx_e2, ty_e2, cnstrs_e2 = infer_expr env e2 in
      let ctx_c, (ty_c, drt_c), cnstrs_c = infer_comp env c in
      unify (ctx_e1 @ ctx_e2 @ ctx_c) (Type.unit_ty, drt_c) [
        ty_less ~pos:(snd e1) ty_e1 Type.int_ty;
        ty_less ~pos:(snd e2) ty_e2 Type.int_ty;
        ty_less ~pos:(snd c) ty_c Type.unit_ty;
        just cnstrs_e1;
        just cnstrs_e2;
        just cnstrs_c
      ]

  | Syntax.Apply (e1, e2) ->
      let ctx_e1, ty_e1, cnstrs_e1 = infer_expr env e1 in
      let ctx_e2, ty_e2, cnstrs_e2 = infer_expr env e2 in
      let drty = Type.fresh_dirty () in
      unify (ctx_e1 @ ctx_e2) drty [
        ty_less ~pos ty_e1 (Type.Arrow (ty_e2, drty));
        just cnstrs_e1;
        just cnstrs_e2
      ]

  | Syntax.New (eff, rsrc) ->
      begin match Tctx.fresh_tydef ~pos eff with
      | (params, Tctx.Effect ops) ->
          let ctx, chngs =
            begin match rsrc with
            | None -> [], []
            | Some (e, op_defs) ->
                let ctx_e, ty_e, cnstrs_e = infer_expr env e in
                let infer (op, a) (ctx, chngs) =
                  match Common.lookup op ops with
                  | None -> Error.typing ~pos "Effect type %s does not have operation %s" eff op
                  | Some (ty_par, ty_res) ->
                      let ctx_a, ty_p1, ty_p2, drty_c, cnstrs_a = infer_abstraction2 env a in
                      ctx_a @ ctx, [
                        ty_less ~pos ty_par ty_p1;
                        ty_less ~pos ty_e ty_p2;
                        dirty_less ~pos drty_c (Type.Tuple [ty_res; ty_e], empty_dirt ());
                        just cnstrs_a
                      ] @ chngs
                in
                List.fold_right infer op_defs (ctx_e, [just cnstrs_e])
            end
          in
          let inst = Type.fresh_instance_param () in
          let r = Type.fresh_region_param () in
          unify ctx (Tctx.effect_to_params eff params r, empty_dirt ()) ([
            Scheme.add_instance_constraint inst r
          ] @ chngs)
      | _ -> Error.typing ~pos "Effect type expected but %s encountered" eff
      end

  | Syntax.Handle (e, c) ->
      let ctx_e, ty_e, cnstrs_e = infer_expr env e
      and ctx_c, drty_c, cnstrs_c = infer_comp env c
      and drty = Type.fresh_dirty () in
      unify (ctx_e @ ctx_c) drty [
        ty_less ~pos ty_e (Type.Handler (drty_c, drty));
        just cnstrs_e;
        just cnstrs_c
      ]

  | Syntax.Check c ->
      ignore (infer_comp env c);
      simple (Type.unit_ty, empty_dirt ())

  in
  (* Print.debug "%t : %t" (Syntax.print_computation (c, pos)) (Scheme.print_dirty_scheme drty_sch); *)
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
  (* XXX Check for implicit sequencing *)
  let drt = Type.fresh_dirt () in
  let add_binding (p, c) (poly, nonpoly, ctx, chngs) =
    let ctx_p, ty_p, cnstrs_p = infer_pattern p in
    let ctx_c, drty_c, cnstrs_c = infer_comp env c in
    let poly, nonpoly =
      match fst c with
      | Syntax.Value _ ->
          ctx_p @ poly, nonpoly
      | Syntax.Apply _ | Syntax.Match _ | Syntax.While _ | Syntax.For _ | Syntax.New _
      | Syntax.Handle _ | Syntax.Let _ | Syntax.LetRec _ | Syntax.Check _ ->
          poly, ctx_p @ nonpoly
    in
    poly, nonpoly, ctx_c @ ctx, [
      dirty_less ~pos:(snd c) drty_c (ty_p, drt);
      just cnstrs_p;
      just cnstrs_c
    ] @ chngs
  in
  let poly, nonpoly, ctx, chngs = List.fold_right add_binding defs ([], [], [], []) in
  let extend_poly (x, ty) env =
    let ty_sch = Scheme.finalize_ty_scheme ~pos ctx ty chngs in
    (x, ty_sch) :: env
  in
  let vars = List.fold_right extend_poly poly [] in
  let change (ctx_c, (ty_c, drt_c), cnstrs_c) =
    Scheme.finalize_dirty_scheme ~pos (ctx @ ctx_c) (ty_c, drt) ([
      dirt_less ~pos drt_c drt;
      Scheme.less_context ~pos nonpoly;
      just cnstrs_c;
    ] @ chngs)
  in
  vars, nonpoly, change

and infer_let_rec ~pos env defs =
  let infer (x, a) (poly, ctx, chngs) =
    let ctx_a, ty_p, drty_c, cnstrs_a = infer_abstraction env a in
    (x, Type.Arrow (ty_p, drty_c)) :: poly, ctx_a @ ctx, [
      just cnstrs_a
    ] @ chngs
  in
  let poly, ctx, chngs = List.fold_right infer defs ([], [], []) in
  let chngs = trim_context ~pos poly :: chngs in
  let extend_poly (x, ty) env =
    let ty_sch = Scheme.finalize_ty_scheme ~pos ctx ty chngs in
    (x, ty_sch) :: env
  in
  let vars = List.fold_right extend_poly poly [] in
  let change (ctx_c, drty_c, cnstrs_c) =
    Scheme.finalize_dirty_scheme ~pos (ctx @ ctx_c) drty_c ([
        just cnstrs_c;
    ] @ chngs)
  in
  vars, change
