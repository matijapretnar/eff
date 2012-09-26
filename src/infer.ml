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

let add_ty_constraint cstr pos t1 t2 =
  cstr := Constr.TypeConstraint (t1, t2, pos) :: !cstr

let add_fresh_constraint cstr pos frsh1 frsh2 =
  Print.debug "Unifying freshness constraints."

let add_dirt_constraint cstr pos drt1 drt2 =
  cstr := Constr.DirtConstraint (drt1, drt2, pos) :: !cstr

let add_region_constraint cstr pos rgn1 rgn2 =
  cstr := Constr.RegionConstraint (rgn1, rgn2, pos) :: !cstr

let add_dirty_constraint cstr pos (lst1, t1, drt1) (lst2, t2, drt2) =
  add_fresh_constraint cstr pos lst1 lst2; (* XXX very fishy *)
  add_ty_constraint cstr pos t1 t2;
  add_dirt_constraint cstr pos (Constr.DirtParam drt1) (Constr.DirtParam drt2)

let add_constraints cstr cstr' =
  cstr := cstr' @ !cstr

let lift_dirty (frsh, t, d) = (frsh, t, Constr.DirtParam d)

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
          ((x, u) :: ctx2, Constr.TypeConstraint (u, t, pos) :: cstrs)
      | Some u ->
          (ctx2, Constr.TypeConstraint (u, t, pos) :: cstrs)
    in
    List.fold_right unify ctx1 (ctx2, cstrs)
  in
  List.fold_right unify_with_context ctxs ([], [])


let trim_context ~pos ctx vars =
  let trim (x, t) (ctx, cstrs) =
    match Common.lookup x vars with
    | None -> ((x, t) :: ctx, cstrs)
    | Some u -> (ctx, Constr.TypeConstraint (u, t, pos) :: cstrs)
  in
  List.fold_right trim ctx ([], [])

(* [infer_pattern cstr pp] infers the type of pattern [pp]. It returns the list of pattern
   variables with their types, which are all guaranteed to be fresh parameters, together
   with the type of the whole pattern. *)
let infer_pattern pp =
  let cstr = ref [] in
  if not (Pattern.linear_pattern pp) then
    Error.typing ~pos:(snd pp) "Variables in a pattern must be distinct." ;
  let vars = ref [] in
  let rec infer (p, pos) =
    match p with
      | Pattern.Var x ->
        (* XXX Why are we looking at disable_typing here? Probably not needed. If
           it is needed, why don't we return [T.universal_ty] for types of constants?
        *)
        let t = (if !disable_typing then T.universal_ty else T.fresh_ty ()) in
          vars := (x, t) :: !vars;
          t
      | Pattern.As (p, x) ->
        let t = infer p in
          vars := (x, t) :: !vars;
          t
      | Pattern.Nonbinding -> T.fresh_ty ()
      | Pattern.Const const -> ty_of_const const
      | Pattern.Tuple ps -> T.Tuple (C.map infer ps)
      | Pattern.Record [] -> assert false
      | Pattern.Record (((fld, _) :: _) as lst) ->
        (match Tctx.infer_field fld with
          | None -> Error.typing ~pos "Unbound record field label %s" fld
          | Some (ty, (t, us)) ->
            let constrain_record_pattern (fld, p) =
              begin match C.lookup fld us with
                | None -> Error.typing ~pos "Unexpected field %s in a pattern of type %s." fld t
                | Some u -> add_ty_constraint cstr pos u (infer p)
              end
            in
              List.iter constrain_record_pattern lst;
              ty)
      | Pattern.Variant (lbl, p) ->
        (match Tctx.infer_variant lbl with
          | None -> Error.typing ~pos "Unbound constructor %s" lbl
          | Some (ty, u) ->
            begin match p, u with
              | None, None -> ()
              | Some p, Some u -> add_ty_constraint cstr pos u (infer p)
              | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument." lbl
              | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument." lbl
            end;
            ty)
  in
  let t = infer pp in
  !vars, t, !cstr

let extend_with_pattern ?(forbidden_vars=[]) p =
  let ctx, t, cstr = infer_pattern p in
    match C.find (fun (x,_) -> List.mem_assoc x ctx) forbidden_vars with
      | Some (x,_) -> Error.typing ~pos:(snd p) "Several definitions of %t." (Print.variable x)
      | None -> ctx, t, cstr


let rec infer_abstraction env (p, c) =
  let ctxp, tp, cstrp = infer_pattern p in
  let env = List.fold_right (fun (x, _) env -> Ctx.extend_ty env x) ctxp env in
  let ctxc, tc, cstrc = infer_comp env c in
  let ctx, cstr = trim_context ~pos:(snd c) ctxc ctxp in
  ctx, tp, tc, cstrp @ cstrc @ cstr

and infer_abstraction2 env (p1, p2, c) =
  let ctx1, t1, cstr1 = extend_with_pattern p1 in
  let ctx2, t2, cstr2 = extend_with_pattern ~forbidden_vars:ctx1 p2 in
  let env = List.fold_right (fun (x, _) env -> Ctx.extend_ty env x) ctx1 env in
  let env = List.fold_right (fun (x, _) env -> Ctx.extend_ty env x) ctx2 env in
  let ctx, cstr_pts = unify_contexts ~pos:(snd p1) [ctx1; ctx2] in
  let ctx3, t3, cstr3 = infer_comp env c in
  let ctx, cstr = trim_context ~pos:(snd c) ctx3 ctx in
  ctx, t1, t2, t3, cstr1 @ cstr2 @ cstr3 @ cstr_pts @ cstr

and infer_let env pos defs =
  (* Check for implicit sequencing *)
  (* Refresh freshes *)
  (* Check for duplicate variables *)
  let add_binding (p, c) (env, ctxs, ctxp, frshs, drts, cstrs) =
    let cstr = ref [] in
    let ctx_p, t_p, cstr_p = infer_pattern p in
    let ctx_c, (frsh, t_c, drt), cstr_c = infer_comp env c in
    add_constraints cstr (cstr_p @ cstr_c);
    add_ty_constraint cstr (snd c) t_c t_p;
    let ctxs, ctxp, env =
      if nonexpansive (fst c) then
        let env = List.fold_right (fun (x, t) env -> Ctx.extend env x (ctx_c, t_c, cstr_c)) ctx_p env in
        ctxs, [], env
      else
        (* let ctx = List.fold_right (fun (x, t) ctx -> (x, t) :: ctx) ctx_p ctx in *)
        let env = List.fold_right (fun (x, _) env -> Ctx.extend_ty env x) ctx_p env in
        ctx_c :: ctxs, ctx_p @ ctxp, env
    in
    (env, ctxs, ctxp, frsh @ frshs, drt :: drts, !cstr @ cstrs)
  in  
  let env, ctxs, ctxp, frshs, drts, cstr =
    List.fold_right add_binding defs (env, [], [], [], [], []) in
  let ctx, cstr_ctxs = unify_contexts ~pos ctxs in
    (env, ctx, ctxp, frshs, drts, cstr_ctxs @ cstr)


and infer_let_rec env pos defs =
  if not (Common.injective fst defs) then
    Error.typing ~pos "Multiply defined recursive value.";

  let lst =
    Common.assoc_map (fun a ->
      let u = T.fresh_ty () in
      (u, a))
      defs

  in
  let cstr = ref [] in
  let env' = List.fold_right (fun (f, (u, _)) env -> Ctx.extend_ty env f) lst env in
  let vars = Common.assoc_map
    (fun (u, ((p, c) as a)) ->
      let ctx, tp, tc, cstr_c = infer_abstraction env' a in
      let t = T.Arrow (tp, tc) in
      add_ty_constraint cstr (snd c) t u;
      add_constraints cstr cstr_c;
      (ctx, t)) lst in
  let ctxs, ctxp =
    List.fold_right
      (fun (x, (ctx, t)) (ctxs, ctxp) -> (ctx :: ctxs, (x, t) :: ctxp)) vars ([], []) in
  let ctx, cstr_c = unify_contexts ~pos ctxs in
  let cstr = cstr_c @ !cstr in
  let env = List.fold_right (fun (x, (_, t)) env -> Ctx.extend env x (Unify.normalize (ctx, t, cstr))) vars env in
    ctxp, env, ctx, cstr

(* [infer_expr env cstr (e,pos)] infers the type of expression [e] in context
   [env]. It returns the inferred type of [e]. *)
and infer_expr env (e,pos) : Ctx.ty_scheme =
  let cstr = ref [] in
  let ctx, t = match e with
    | Core.Var x ->
        begin match Ctx.lookup env x with
        | Some (Some (ctx, ty, cstrs)) -> add_constraints cstr cstrs; ctx, ty
        | Some None ->
            let t = T.fresh_ty () in
            [(x, t)], t
        | None -> Error.typing ~pos "Unknown variable %t" (Print.variable x)
        end
    | Core.Const const -> [], ty_of_const const
    | Core.Tuple es ->
        let ctxs, ts = List.split (C.map (fun e -> let ctx, t, cstr_e = infer_expr env e in add_constraints cstr cstr_e; (ctx, t)) es) in
        let ctx, cstrs = unify_contexts ~pos ctxs in
        add_constraints cstr cstrs;
        ctx, T.Tuple ts
    | Core.Record [] -> assert false
    | Core.Record (((fld,_)::_) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos "Fields in a record must be distinct." ;
      (match Tctx.infer_field fld with
        | None -> Error.typing ~pos "Unbound record field label %s in a pattern" fld
        | Some (ty, (t_name, arg_types)) ->
          if List.length lst <> List.length arg_types then
            Error.typing ~pos "malformed record of type %s" t_name
          else
            let arg_types', ctxs = List.fold_right (fun (f, e) (flds, ctxs) ->
                                                let ctx, t, cstr_e = infer_expr env e in
                                                add_constraints cstr cstr_e;
                                                ((f, t) :: flds, ctxs)) lst ([], []) in
            let constrain_record_arg (fld, t) =
              begin match C.lookup fld arg_types with
                | None -> Error.typing ~pos "Unexpected record field label %s in a pattern" fld
                | Some u -> add_ty_constraint cstr pos t u
              end
            in
              List.iter constrain_record_arg arg_types';
              let ctx, cstrs = unify_contexts ~pos ctxs in
              add_constraints cstr cstrs;
              ctx, ty)
          
    | Core.Variant (lbl, u) ->
      (match Tctx.infer_variant lbl with
        | None -> Error.typing ~pos "Unbound constructor %s in a pattern" lbl
        | Some (ty, arg_type) ->
          let ctx = begin match arg_type, u with
            | None, None -> []
            | Some ty, Some u ->
              let ctx, ty', cstr_u = infer_expr env u in
                add_constraints cstr cstr_u;
                add_ty_constraint cstr pos ty' ty;
                ctx
            | _, _ -> Error.typing ~pos "Wrong number of arguments for label %s." lbl
          end
          in ctx, ty)
        
    | Core.Lambda a ->
        let ctx, t1, t2, cstr_abs = infer_abstraction env a in
        add_constraints cstr cstr_abs;
        ctx, T.Arrow (t1, t2)
        
    | Core.Operation (e, op) ->
        let rgn = T.fresh_region_param () in
        (match Tctx.infer_operation op rgn with
          | None -> Error.typing ~pos "Unbound operation %s" op
          | Some (ty, (t1, t2)) ->
            let ctx, u, cstr_u = infer_expr env e in
            let d = T.fresh_dirt_param () in
              add_ty_constraint cstr pos u ty;
              add_dirt_constraint cstr pos (Constr.DirtAtom (rgn, op)) (Constr.DirtParam d);
              add_constraints cstr cstr_u;
              (* An operation creates no new instances. *)
              ctx, T.Arrow (t1, ([], t2, d)))

    | Core.Handler {Core.operations=ops; Core.value=a_val; Core.finally=a_fin} -> 
        let t_value = T.fresh_ty () in
        let dirt = T.fresh_dirt_param () in
        let t_finally = T.fresh_ty () in
        let t_yield = T.fresh_ty () in
        let constrain_operation ((e, op), a2) =
          (* XXX Correct when you know what to put instead of the fresh region .*)
          (match Tctx.infer_operation op (T.fresh_region_param ()) with
            | None -> Error.typing ~pos "Unbound operation %s in a handler" op
            | Some (ty, (t1, t2)) ->
              let ctxe, u, cstr_e = infer_expr env e in
                add_ty_constraint cstr pos u ty;
                add_constraints cstr cstr_e;
                let ctxa, u1, tk, u2, cstr_a = infer_abstraction2 env a2 in
                  add_constraints cstr cstr_a;
                  add_ty_constraint cstr pos t1 u1;
                  (* XXX maybe we need to change the direction of inequalities here,
                     or even require equalities. *)
                  (* XXX Think also what to do about fresh instances. *)
                  add_ty_constraint cstr pos tk (T.Arrow (t2, ([], t_yield, dirt)));
                  add_dirty_constraint cstr pos ([], t_yield, dirt) u2;
                  let ctx, cstrs = unify_contexts ~pos [ctxe; ctxa] in
                  add_constraints cstr cstrs;
                  ctx)
        in
          let ctxs = List.map constrain_operation ops in
          let ctx1, valt1, valt2, cstr_val = infer_abstraction env a_val in
          let ctx2, fint1, fint2, cstr_fin = infer_abstraction env a_fin in
            add_ty_constraint cstr pos valt1 t_value;
            add_dirty_constraint cstr pos valt2 ([], t_yield, dirt);
            add_dirty_constraint cstr pos fint2 ([], t_finally, dirt);
            add_ty_constraint cstr pos fint1 t_yield;
            add_constraints cstr (cstr_val @ cstr_fin);
            let ctx, cstrs = unify_contexts ~pos (ctx1 :: ctx2 :: ctxs) in
            add_constraints cstr cstrs;
            ctx, T.Handler (t_value, t_finally)
  in
  Print.debug "Type of %t is (%t) %t | %t" (Print.expression (e, pos)) (Print.context ctx) (Print.ty Trio.empty t) (Print.constraints Trio.empty !cstr);
  Unify.normalize (ctx, t, !cstr)
              
(* [infer_comp env cstr (c,pos)] infers the type of computation [c] in context [env].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp env (c, pos) : (Core.variable, Type.ty) Common.assoc * Type.dirty * Constr.constraints list =
  (* XXX Why isn't it better to just not call type inference when type checking is disabled? *)
  (* Print.debug "Inferring type of %t" (Print.computation (c, pos)); *)
  if !disable_typing then T.universal_dirty else
  let rec infer env (c, pos) =
    let cstr = ref [] in
    let ctx, (frsh, ty, drt) = match c with
      | Core.Apply (e1, e2) ->
          let ctx1, t1, cstr1 = infer_expr env e1 in
          let ctx2, t2, cstr2 = infer_expr env e2 in
          let ctx, cstrs = unify_contexts ~pos [ctx1; ctx2] in
          let t = T.fresh_dirty () in
          add_constraints cstr (cstr1 @ cstr2 @ cstrs);
          add_ty_constraint cstr pos t1 (T.Arrow (t2, t));
          ctx, lift_dirty t

      | Core.Value e ->
          let ctx, t, cstr_e = infer_expr env e in
          add_constraints cstr cstr_e;
          ctx, ([], t, Constr.DirtEmpty)

      | Core.Match (e, []) ->
        let ctx, t_in, cstr_e = infer_expr env e in
        let t_out = T.fresh_ty () in
        add_ty_constraint cstr pos t_in T.empty_ty;
        add_constraints cstr cstr_e;
        ctx, ([], t_out, Constr.DirtEmpty)

      | Core.Match (e, lst) ->
          let ctxe, t_in, cstr_in = infer_expr env e in
          add_constraints cstr cstr_in;
          let t_out = T.fresh_ty () in
          let drt_out = T.fresh_dirt_param () in
          let infer_case ((p, e') as a) =
            (* XXX Refresh fresh instances *)
            let ctxa, t_in', (frsh_out, t_out', drt_out'), cstr_case = infer_abstraction env a in
            add_constraints cstr cstr_case;
            add_ty_constraint cstr (snd e) t_in t_in';
            add_ty_constraint cstr (snd e') t_out' t_out;
            add_dirt_constraint cstr (snd e') (Constr.DirtParam drt_out') (Constr.DirtParam drt_out);
            ctxa, frsh_out
            (* XXX Collect fresh instances from all branches. *)
          in
          let ctxs, frshs = List.split (List.map infer_case lst) in
          let ctx, cstrs = unify_contexts ~pos ctxs in
          add_constraints cstr cstrs;
          ctx, (List.flatten frshs, t_out, Constr.DirtParam drt_out)
              
      | Core.New (eff, r) ->
        begin match Tctx.fresh_tydef ~pos:pos eff with
          | (params, Tctx.Effect ops) ->
            let ctx = begin match r with
              | None -> []
              | Some (e, lst) ->
                let ctxe, te, cstr_e = infer_expr env e in
                add_constraints cstr cstr_e;
                let ctxs =
                  List.map
                    (fun (op, (((_,pos1), (_,pos2), (_,posc)) as a)) ->
                      match C.lookup op ops with
                        | None -> Error.typing ~pos "Effect type %s does not have operation %s" eff op
                        | Some (u1, u2) ->
                          let ctx, t1, t2, t, cstr_a = infer_abstraction2 env a in
                            add_constraints cstr cstr_a;
                            add_ty_constraint cstr pos1 t1 u1;
                            add_ty_constraint cstr pos2 t2 te;
                            (* Here, we should have that resources create no fresh instances. *)
                            let d_empty = T.fresh_dirt_param () in
                            add_dirt_constraint cstr posc (Constr.DirtParam d_empty) (Constr.DirtEmpty); 
                            add_dirty_constraint cstr posc t ([], T.Tuple [u2; te], d_empty);
                            ctx)
                    lst in
                    let ctx, cstrs = unify_contexts ~pos ctxs in
                    add_constraints cstr cstrs;
                    ctx
            end
            in
            let instance = T.fresh_instance_param () in
            let rgn = T.fresh_region_param () in
              add_region_constraint cstr pos (Constr.RegionAtom (Constr.InstanceParam instance)) (Constr.RegionParam rgn) ;
              ctx, ([instance], Tctx.effect_to_params eff params rgn, Constr.DirtEmpty)
          | _ -> Error.typing ~pos "Effect type expected but %s encountered" eff
          end

      | Core.While (c1, c2) ->
        let dirt = Constr.fresh_dirt () in
        let ctx1, frsh1, t1, d1, cstr1 = infer env c1 in
          add_ty_constraint cstr pos t1 T.bool_ty;
          add_dirt_constraint cstr pos d1 dirt;
          let ctx2, frsh2, t2, d2, cstr2 = infer env c2 in
          add_ty_constraint cstr pos t2 T.unit_ty;
          add_dirt_constraint cstr pos d2 dirt;
          let ctx, cstrs = unify_contexts ~pos [ctx1; ctx2] in
          add_constraints cstr (cstr1 @ cstr2 @ cstrs);
          (* XXX We need to make sure to erase all instances generated by frsh2 *)
          (* XXX could add "diverges" dirt *)
          ctx, (frsh1, T.unit_ty, dirt)

      | Core.For (i, e1, e2, c, _) ->
          let ctx1, t1, cstr1 = infer_expr env e1 in
          add_ty_constraint cstr (snd e1) t1 T.int_ty;
          let ctx2, t2, cstr2 = infer_expr env e2 in
          add_ty_constraint cstr (snd e2) t2 T.int_ty;
          add_constraints cstr (cstr1 @ cstr2);
          let env = Ctx.extend_ty env i in
          let ctx3, frsh, ty, drt, cstr_c = infer env c in
          add_ty_constraint cstr (snd c) ty T.unit_ty;
          add_constraints cstr cstr_c;
          let ctx, cstrs = unify_contexts ~pos [ctx1; ctx2; ctx3] in
          add_constraints cstr (cstrs);
          (* XXX We need to make sure to erase all instances generated by frsh *)
          ctx, ([], T.unit_ty, drt)

      | Core.Handle (e1, c2) ->
          let ctx1, t1, cstr1 = infer_expr env e1 in
          let ctx2, frsh, t2, d2, cstr2 = infer env c2 in
          add_constraints cstr (cstr1 @ cstr2);
          let t3 = T.fresh_ty () in
          let t1' = T.Handler (t2, t3) in
            add_ty_constraint cstr pos t1' t1;
          let ctx, cstrs = unify_contexts ~pos [ctx1; ctx2] in
          add_constraints cstr (cstrs);
            (* XXX Are instances created by c2 just passed through?
                What about ones that are created during handling? *)
            ctx, (frsh, t3, d2)

      | Core.Let (defs, c) -> 
          let env, ctx1, ctxp, let_frshs, let_drts, cstrs = infer_let env pos defs in
          let ctx2, frsh, tc, dc, cstr_c = infer env c in
          let ctx, cstr_cs = unify_contexts ~pos [ctx1; ctx2] in
          let ctx, cstr_diff = trim_context ~pos ctx ctxp in
          let drt = Constr.fresh_dirt () in
            List.iter (fun let_drt -> add_dirt_constraint cstr pos (Constr.DirtParam let_drt) drt) let_drts;
            add_dirt_constraint cstr pos dc drt ;
            add_constraints cstr (cstr_c @ cstrs @ cstr_cs @ cstr_diff);
            ctx, (let_frshs @ frsh, tc, drt)

      | Core.LetRec (defs, c) ->
          let vars, env, ctx1, cstrs = infer_let_rec env pos defs in
          let ctx2, frsh, tc, dc, cstr_c = infer env c in
          let ctx, cstr_cs = unify_contexts ~pos [ctx1; ctx2] in
          let ctx, cstr_diff = trim_context ~pos ctx vars in
          add_constraints cstr (cstr_c @ cstrs @ cstr_cs @ cstr_diff);
          ctx, (frsh, tc, dc)

      | Core.Check c ->
          ignore (infer env c);
          [], ([], T.unit_ty, Constr.DirtEmpty)
    in
    let ctx, ty, cstr = Unify.normalize (ctx, ty, !cstr) in
    ctx, frsh, ty, drt, cstr
  in
  let ctx, frsh, ty, drt, cstr = infer env (c, pos) in
  let d = T.fresh_dirt_param () in
  Print.debug "Type of %t is (%t) %t | %t" (Print.computation (c, pos)) (Print.context ctx) (Print.ty Trio.empty ty) (Print.constraints Trio.empty cstr);
  ctx, (frsh, ty, d), (Constr.DirtConstraint (drt, Constr.DirtParam d, pos) :: cstr)

