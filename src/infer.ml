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

let simple ty = ([], ty, Type.empty)
let empty_dirt () = Type.fresh_dirt_param ()

let gather add_news =
  List.fold_right (fun add_new cnstrs -> add_new cnstrs) add_news Type.empty

let ty_less ~pos ty1 ty2 cnstrs =
  Type.add_ty_constraint ~pos ty1 ty2 cnstrs
let dirt_less ~pos d1 d2 cnstrs =
  Type.add_dirt_constraint ~pos (Type.DirtParam d1) (Type.DirtParam d2) cnstrs
let dirt_causes_op ~pos d r op cnstrs =
  Type.add_dirt_constraint ~pos (Type.DirtAtom (r, op)) (Type.DirtParam d) cnstrs
let dirt_pure ~pos d cnstrs =
  Type.add_dirt_constraint ~pos (Type.DirtParam d) (Type.DirtEmpty) cnstrs
let region_covers ~pos r i cnstrs =
  Type.add_region_constraint ~pos (Type.RegionAtom (Type.InstanceParam i)) (Type.RegionParam r) cnstrs
let dirty_less ~pos (nws1, ty1, d1) (nws2, ty2, d2) cnstrs =
  Print.debug ~pos "Unifying freshness constraints %t <= %t." (Print.fresh_instances nws1) (Print.fresh_instances nws2);
  ty_less ~pos ty1 ty2 (dirt_less ~pos d1 d2 cnstrs)

let just cnstrs1 cnstrs2 = Type.join_disjoint_constraints cnstrs1 cnstrs2
let merge cnstrs1 cnstrs2 = Type.join_constraints cnstrs1 cnstrs2

let unify_context ~pos ctx =
  let add (x, ty) (ctx, cnstrs) =
    match Common.lookup x ctx with
    | None ->
        let ty' = Type.fresh_ty () in
        ((x, ty') :: ctx, ty_less ~pos ty' ty cnstrs)
    | Some ty' ->
        (ctx, ty_less ~pos ty' ty cnstrs)
  in
  List.fold_right add ctx ([], Type.empty)

let canonize_context ~pos (ctx, ty, cnstrs) =
  let ctx, cnstrs_ctx = unify_context ~pos ctx in
  ctx, ty, merge cnstrs_ctx cnstrs

let ty_of_const = function
  | Common.Integer _ -> Type.int_ty
  | Common.String _ -> Type.string_ty
  | Common.Boolean _ -> Type.bool_ty
  | Common.Float _ -> Type.float_ty

let trim_context ~pos ctx ctx_p =
  let trim (x, t) (ctx, cstrs) =
    match Common.lookup x ctx_p with
    | None -> ((x, t) :: ctx, cstrs)
    | Some u -> (ctx, Type.add_ty_constraint pos u t cstrs)
  in
  List.fold_right trim ctx ([], Type.empty)

(* [infer_pattern cstr pp] infers the type of pattern [pp]. It returns the list of pattern
   variables with their types, which are all guaranteed to be fresh parameters, together
   with the type of the whole pattern. *)
let rec infer_pattern (p, pos) =
  (* We do not check for overlaps as all identifiers are distinct - desugar needs to do those *)
  if !disable_typing then simple Type.universal_ty else
  match p with
  | Pattern.Var x ->
      let ty = Type.fresh_ty () in
      [(x, ty)], ty, Type.empty
  | Pattern.As (p, x) ->
      let ctx, ty, cnstrs = infer_pattern p in
      (x, ty) :: ctx, ty, cnstrs
  | Pattern.Nonbinding -> simple (Type.fresh_ty ())
  | Pattern.Const const -> simple (ty_of_const const)
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
                  ty_less ~pos ty ty';
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
          | None, None -> simple ty
          | Some p, Some u ->
              let ctx', ty', cnstrs' = infer_pattern p in
              ctx', ty, gather [
                ty_less ~pos u ty';
                just cnstrs'
              ]
          | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument." lbl
          | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument." lbl
        end
      end

(* [infer_expr env cstr (e,pos)] infers the type of expression [e] in context
   [env]. It returns the inferred type of [e]. *)
let rec infer_expr env (e, pos) =
  if !disable_typing then simple Type.universal_ty else
  let ty_scheme = match e with

  | Core.Var x ->
      begin match Ctx.lookup env x with
      | Some (ctx, ty, cnstrs) ->
          (ctx, ty, cnstrs)
      | None ->
          let ty = T.fresh_ty () in
          [(x, ty)], ty, Type.empty
      end

  | Core.Const const -> simple (ty_of_const const)

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
                  ty_less ~pos ty' ty;
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
          | None, None -> simple ty
          | Some e, Some u ->
              let ctx', ty', cnstrs' = infer_expr env e in
              ctx', ty, gather [
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
          let d = T.fresh_dirt_param () in
          ctx, T.Arrow (t1, ([], t2, d)), gather [
            ty_less ~pos u ty;
            dirt_causes_op ~pos d r op;
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
              ty_less ~pos u ty;
              ty_less ~pos t1 u1;
              ty_less ~pos (T.Arrow (t2, ([], t_yield, dirt))) tk;
              dirty_less ~pos u2 ([], t_yield, dirt);
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
          ty_less ~pos t_value valt1;
          dirty_less ~pos valt2 ([], t_yield, dirt);
          dirty_less ~pos fint2 ([], t_finally, dirt);
          ty_less ~pos t_yield fint1;
          just cstr_val;
          just cstr_fin;
          just cnstrs
        ]

  in
  let ctx, ty, cstr = Unify.normalize (canonize_context ~pos ty_scheme) in
  Print.debug "Type of %t is %t" (Print.expression (e, pos)) (Print.ty_scheme (ctx, ty, cstr));
  (ctx, ty, cstr)
              
(* [infer_comp env cstr (c,pos)] infers the type of computation [c] in context [env].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp env (c, pos) =
  if !disable_typing then simple Type.universal_dirty else
  let ctx, (frsh, ty, drt), cstr = match c with

  | Core.Value e ->
      let ctx, ty, cnstrs = infer_expr env e in
      ctx, ([], ty, empty_dirt ()), cnstrs

  | Core.Let (defs, c) -> 
      let env, ctx1, ctxp, let_frshs, let_drt, cstrs = infer_let ~pos env defs in
      let ctx2, (frsh, tc, dc), cstr_c = infer_comp env c in
      let ctx, cstr_cs = unify_context ~pos (ctx1 @ ctx2) in
      let ctx, cstr_diff = trim_context ~pos ctx ctxp in
      ctx, (let_frshs @ frsh, tc, let_drt), gather [
        dirt_less ~pos dc let_drt;
        merge cstr_cs;
        merge cstr_diff;
        just cstr_c;
        just cstrs
      ]

  | Core.LetRec (defs, c) ->
      let env, ctx1, cstrs = infer_let_rec ~pos env defs in
      let ctx2, (frsh, tc, dc), cstr_c = infer_comp env c in
      ctx1 @ ctx2, (frsh, tc, dc), gather [
        just cstrs;
        just cstr_c
      ]

  | Core.Match (e, []) ->
      let ctx, ty_in, cnstrs = infer_expr env e in
      let ty_out = Type.fresh_ty () in
      ctx, ([], ty_out, empty_dirt ()), gather [
        ty_less ~pos ty_in Type.empty_ty;
        just cnstrs
      ]

  | Core.Match (e, cases) ->
      let ctx_in, ty_in, cnstrs_in = infer_expr env e in
      let ty_out = T.fresh_ty () in
      let drt_out = T.fresh_dirt_param () in
      let infer_case ((p, c) as a) (ctx, frshs, cnstrs) =
        (* XXX Refresh fresh instances *)
        let ctx', ty_in', (frsh_out, ty_out', drt_out'), cnstrs' = infer_abstraction env a in
        ctx' @ ctx, frsh_out @ frshs, gather [
          ty_less ~pos:(snd e) ty_in ty_in';
          ty_less ~pos:(snd c) ty_out' ty_out;
          dirt_less ~pos:(snd c) drt_out' drt_out;
          just cnstrs';
          just cnstrs
        ]
      in
      let ctx, frshs, cnstrs = List.fold_right infer_case cases (ctx_in, [], cnstrs_in) in
      ctx, (frshs, ty_out, drt_out), cnstrs
          

  | Core.While (c1, c2) ->
      let ctx1, (frsh1, t1, drt1), cnstrs1 = infer_comp env c1 in
      let ctx2, (frsh2, t2, drt2), cnstrs2 = infer_comp env c2 in
      let drt = Type.fresh_dirt_param () in
      (* XXX We must erase all instances generated by c2 *)
      ctx1 @ ctx2, (frsh1, T.unit_ty, drt), gather [
        ty_less ~pos t1 Type.bool_ty;
        ty_less ~pos t2 Type.unit_ty;
        dirt_less ~pos drt1 drt;
        dirt_less ~pos drt2 drt;
        just cnstrs1;
        just cnstrs2
      ]

  | Core.For (i, e1, e2, c, _) ->
      let ctx1, ty1, cnstrs1 = infer_expr env e1 in
      let ctx2, ty2, cnstrs2 = infer_expr env e2 in
      let ctx3, (frsh, ty, drt), cnstrs3 = infer_comp env c in
      (* XXX We must erase all instances generated by c *)
      ctx1 @ ctx2 @ ctx3, ([], T.unit_ty, drt), gather [
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
      ctx1 @ ctx2, drty, gather [
        ty_less ~pos ty1 (T.Arrow (ty2, drty));
        just cnstrs1;
        just cnstrs2
      ]

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
                      ty_less ~pos(* p1 *) t1 u1;
                      ty_less ~pos(* p2 *) t2 te;
                      (* XXX Warn that d_empty has to be empty *)
                      dirt_pure ~pos(* c *) d_empty;
                      dirty_less ~pos(* c *) t ([], T.Tuple [u2; te], d_empty);
                      just cstr_a;
                      just cstrs
                    ]
              in
              List.fold_right infer lst (ctxe, cstr_e)
          end
          in
          let instance = T.fresh_instance_param () in
          let rgn = T.fresh_region_param () in
          ctx, ([instance], Tctx.effect_to_params eff params rgn, empty_dirt ()), gather [
            region_covers ~pos rgn instance;
            just cnstrs
          ]
      | _ -> Error.typing ~pos "Effect type expected but %s encountered" eff
      end

  | Core.Handle (e1, c2) ->
      let ctx1, ty1, cnstrs1 = infer_expr env e1 in
      let ctx2, (frsh, ty2, drt2), cnstrs2 = infer_comp env c2 in
      let ty3 = T.fresh_ty () in
      ctx1 @ ctx2, (frsh, ty3, drt2), gather [
        ty_less ~pos ty1 (T.Handler (ty2, ty3));
        just cnstrs1;
        just cnstrs2
      ]

  | Core.Check c ->
      ignore (infer_comp env c);
      simple ([], T.unit_ty, empty_dirt ())

  in
  let ctx, ty, cstr = Unify.normalize (canonize_context ~pos (ctx, ty, cstr)) in
  Print.debug "Type of %t is (%t) %t | %t" (Print.computation (c, pos)) (Print.context ctx) (Print.ty Trio.empty ty) (Print.constraints Trio.empty cstr);
  ctx, (frsh, ty, drt), cstr

and infer_abstraction env (p, c) =
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
  let drt = Type.fresh_dirt_param () in
  let add_binding (p, c) (env, ctxs, ctxp, frshs, cstrs) =
    let ctx_p, t_p, cstr_p = infer_pattern p in
    let ctx_c, (frsh, t_c, drt'), cstr_c = infer_comp env c in
    let env, ctxp =
      if nonexpansive (fst c) then
        let env = List.fold_right (fun (x, t) env -> Ctx.extend env x (ctx_c, t_c, cstr_c)) ctx_p env in
        env, ctxp
      else
        env, ctx_p @ ctxp
    in
    env, ctx_c @ ctxs, ctxp, frsh @ frshs, gather [
      ty_less ~pos:(snd c) t_c t_p;
      dirt_less ~pos:(snd c) drt' drt;
      just cstr_p;
      just cstr_c
    ]
  in
  let env, ctxs, ctxp, frshs, cstrs = List.fold_right add_binding defs (env, [], [], [], Type.empty) in
  let ctx, cstr_ctxs = unify_context ~pos ctxs in
  env, ctx, ctxp, frshs, drt, gather [
    merge cstr_ctxs;
    just cstrs
  ]

and infer_let_rec ~pos env defs =
  if not (Common.injective fst defs) then Error.typing ~pos "Multiply defined recursive value.";
  let infer (x, ((p, c) as a)) (vars, ctx, cnstrs) =
    let ctx', tp, tc, cnstrs_a = infer_abstraction env a in
    (x, Type.Arrow (tp, tc)) :: vars, ctx' @ ctx, gather [
      just cnstrs_a;
      just cnstrs
    ]
  in
  let vars, ctx, cnstrs = List.fold_right infer defs ([], [], Type.empty) in
  let ctx, cnstrs_ctx = unify_context ~pos ctx in
  let ctx, cnstrs_diff = trim_context ~pos ctx vars in
  let cnstrs = gather [
    merge cnstrs_diff;
    merge cnstrs_ctx;
    just cnstrs
  ] in
  let env = List.fold_right (fun (x, t) env -> Ctx.extend env x (Unify.normalize (ctx, t, cnstrs))) vars env in
  env, ctx, cnstrs