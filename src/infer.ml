module C = Common
module T = Type

let warn_implicit_sequencing = ref false;;

let disable_typing = ref false;;

(* We perform type inference int the style of Standard ML 97, i.e.,
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

let empty_constraint = []

let add_ty_constraint cstr pos t1 t2 =
  cstr := (t1, t2, pos) :: !cstr

let add_dirt_constraint cstr pos drt1 drt2 =
  ()

let add_dirty_constraint cstr pos (t1, drt1) (t2, drt2) =
  add_ty_constraint cstr pos t1 t2;
  add_dirt_constraint cstr pos drt1 drt2


let ty_of_const = function
  | Common.Integer _ -> Type.int_ty
  | Common.String _ -> Type.string_ty
  | Common.Boolean _ -> Type.bool_ty
  | Common.Float _ -> Type.float_ty

(* [infer_pattern cstr pp] infers the type of pattern [pp]. It returns the list of
   pattern variables with their types, which are all guaranteed to be [Type.Meta]'s, together
   with the type of the pattern. *)
let infer_pattern cstr pp =
  if not (Pattern.linear_pattern pp) then
    Error.typing ~pos:(snd pp) "Variables in a pattern must be distinct." ;
  let vars = ref [] in
  let rec infer (p, pos) =
    match p with
      | Pattern.Var x ->
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
                  | Some u -> add_ty_constraint cstr pos (infer p) u
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
                | Some p, Some u -> add_ty_constraint cstr pos (infer p) u
                | None, Some _ -> Error.typing ~pos "Constructor %s should be applied to an argument." lbl
                | Some _, None -> Error.typing ~pos "Constructor %s cannot be applied to an argument." lbl
              end;
              ty)
  in
  let t = infer pp in
    !vars, t

let extend_with_pattern ?(forbidden_vars=[]) ctx cstr p =
  let vars, t = infer_pattern cstr p in
  match C.find (fun (x,_) -> List.mem_assoc x vars) forbidden_vars with
    | Some (x,_) -> Error.typing ~pos:(snd p) "Several definitions of %s." x
    | None -> vars, t, List.fold_right (fun (x, t) ctx -> Ctx.extend_ty ctx x t) vars ctx

let rec infer_abstraction ctx cstr (p, c) =
  let _, t1, ctx = extend_with_pattern ctx cstr p in
  let t2 = infer_comp ctx cstr c in
    t1, (t2 : T.dirty)

and infer_abstraction2 ctx cstr (p1, p2, c) =
  let vs, t1, ctx = extend_with_pattern ctx cstr p1 in
  let _, t2, ctx = extend_with_pattern ~forbidden_vars:vs ctx cstr p2 in
  let t3 = infer_comp ctx cstr c in
    t1, t2, (t3 : T.dirty)

and infer_handler_case_abstraction ctx cstr (p, k, e) =
  let vs, t1, ctx = extend_with_pattern ctx cstr p in
  let _, tk, ctx = extend_with_pattern ~forbidden_vars:vs ctx cstr k in
  let t2 = infer_comp ctx cstr e in
    tk, t1, (t2 : T.dirty)

and infer_let ctx cstr pos defs =
  (if !warn_implicit_sequencing && List.length defs >= 2 then
      let positions = List.map (fun (_, (_, pos)) -> pos) defs in
        Print.warning ~pos "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
          (Print.sequence "," Print.position positions));
  let delta = T.fresh_dirt () in
  let vars = List.fold_left
    (fun vs (p,c) ->
      let tc = infer_comp ctx cstr c in
      let ws, tp = infer_pattern cstr p in
      add_dirty_constraint cstr (snd c) tc (tp, delta);
      match C.find_duplicate (List.map fst ws) (List.map fst vs) with
        | Some x -> Error.typing ~pos "Several definitions of %s." x
        | None ->
            let poly = nonexpansive (fst c) in
            let ws = Common.assoc_map (fun ty -> (poly, ty)) ws
          in
          List.rev ws @ vs)
    [] defs
  in
  let sbst = Unify.solve !cstr in
  let ctx = Ctx.subst_ctx ctx sbst in
  let vars = Common.assoc_map (fun (poly, ty) -> Ctx.generalize ctx poly (T.subst_ty sbst ty)) vars in
  let ctx = List.fold_right (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme) vars ctx
  in
    vars, delta, ctx

and infer_let_rec ctx cstr pos defs =
  if not (Common.injective fst defs) then
    Error.typing ~pos "Multiply defined recursive value.";
  let lst =
    List.map (fun (f,(p,c)) ->
      let u1 = T.fresh_ty () in
      let u2 = T.fresh_dirty () in
      (f, u1, u2, p, c))
      defs
  in
  let vars = List.fold_right (fun (f,u1,u2,_,_) vars -> (f, (T.Arrow (u1, u2))) :: vars) lst [] in
  let ctx' = List.fold_right (fun (f,u1,u2,_,_) ctx -> Ctx.extend_ty ctx f (T.Arrow (u1, u2))) lst ctx in
  List.iter
    (fun (_,u1,u2,p,c) ->
      let _, tp, ctx' = extend_with_pattern ctx' cstr p in
      let tc = infer_comp ctx' cstr c in
      add_ty_constraint cstr (snd p) u1 tp;
      add_dirty_constraint cstr (snd c) u2 tc)
    lst;
  let sbst = Unify.solve !cstr in
  let vars = Common.assoc_map (T.subst_ty sbst) vars in
  let ctx = Ctx.subst_ctx ctx sbst in
  let vars = Common.assoc_map (Ctx.generalize ctx true) vars in
  let ctx = List.fold_right (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme) vars ctx
  in
    vars, ctx

(* [infer_expr ctx cstr (e,pos)] infers the type of expression [e] in context
   [ctx]. It returns the inferred type of [e]. *)
and infer_expr ctx cstr (e,pos) =
  match e with
    | Core.Var x -> Ctx.lookup ~pos ctx x
    | Core.Const const -> ty_of_const const
    | Core.Tuple es -> T.Tuple (C.map (infer_expr ctx cstr) es)
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
            let arg_types' = C.assoc_map (infer_expr ctx cstr) lst in
            let constrain_record_arg (fld, t) =
              begin match C.lookup fld arg_types with
                | None -> Error.typing ~pos "Unexpected record field label %s in a pattern" fld
                | Some u -> add_ty_constraint cstr pos t u
              end
            in
              List.iter constrain_record_arg arg_types';
              ty)
          
    | Core.Variant (lbl, u) ->
      (match Tctx.infer_variant lbl with
        | None -> Error.typing ~pos "Unbound constructor %s in a pattern" lbl
        | Some (ty, arg_type) ->
          begin match arg_type, u with
            | None, None -> ()
            | Some ty, Some u ->
              let ty' = infer_expr ctx cstr u in
                add_ty_constraint cstr pos ty ty'
            | _, _ -> Error.typing ~pos "Wrong number of arguments for label %s." lbl
          end;
          ty)
        
    | Core.Lambda a ->
        let t1, t2 = infer_abstraction ctx cstr a in
        T.Arrow (t1, t2)
        
    | Core.Operation (e, op) ->
      (match Tctx.infer_operation op with
        | None -> Error.typing ~pos "Unbound operation %s" op
        | Some (ty, (t1, t2)) ->
          let u = infer_expr ctx cstr e in
          let dirt = T.DirtAtom (T.fresh_region (), op) in
            (* XXX do something about regions *)
            add_ty_constraint cstr pos u ty;
            T.Arrow (t1, (t2, dirt)))

    | Core.Handler {Core.operations=ops; Core.value=a_val; Core.finally=a_fin} -> 
        let t_value = T.fresh_ty () in
        let dirt = T.fresh_dirt () in
        let t_finally = T.fresh_ty () in
        let t_yield = T.fresh_ty () in
        let constrain_operation ((e, op), a2) =
          (match Tctx.infer_operation op with
            | None -> Error.typing ~pos "Unbound operation %s in a handler" op
            | Some (ty, (t1, t2)) ->
              let u = infer_expr ctx cstr e in
                add_ty_constraint cstr pos u ty;
                let tk, u1, u2 = infer_handler_case_abstraction ctx cstr a2 in
                  add_ty_constraint cstr pos t1 u1;
                  (* XXX maybe we need to change the direction of inequalities here,
                     or even require equalities. *)
                  add_ty_constraint cstr pos tk (T.Arrow (t2, (t_yield, dirt)));
                  add_dirty_constraint cstr pos (t_yield, dirt) u2)
        in
          List.iter constrain_operation ops;
          let (valt1, valt2) = infer_abstraction ctx cstr a_val in
          let (fint1, fint2) = infer_abstraction ctx cstr a_fin in
            add_ty_constraint cstr pos valt1 t_value;
            add_dirty_constraint cstr pos valt2 (t_yield, dirt);
            add_dirty_constraint cstr pos fint2 (t_finally, dirt);
            add_ty_constraint cstr pos fint1 t_yield;
            T.Handler { T.value = t_value; T.finally = t_finally }
              
(* [infer_comp ctx cstr (c,pos)] infers the type of computation [c] in context [ctx].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp ctx cstr cp =
  (* XXX Why isn't it better to just not call type inference when type checking is disabled? *)
  if !disable_typing then T.universal_dirty else
  let rec infer ctx (c, pos) =
    match c with
      | Core.Apply (e1, e2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer_expr ctx cstr e2 in
          let t = T.fresh_dirty () in
          add_ty_constraint cstr pos t1 (T.Arrow (t2, t));
          t

      | Core.Value e ->
          infer_expr ctx cstr e, T.empty_dirt

      | Core.Match (e, []) ->
        let t_in = infer_expr ctx cstr e in
        let t_out = T.fresh_ty () in
        add_ty_constraint cstr pos t_in T.empty_ty;
        t_out, T.empty_dirt

      | Core.Match (e, lst) ->
          let t_in = infer_expr ctx cstr e in
          let t_out = T.fresh_dirty () in
          let infer_case ((p, e') as a) =
            let t_in', t_out' = infer_abstraction ctx cstr a in
            add_ty_constraint cstr (snd e) t_in t_in';
            add_dirty_constraint cstr (snd e') t_out' t_out
          in
          List.iter infer_case lst;
          t_out
              
      | Core.New (eff, r) ->
          begin match Tctx.fresh_tydef ~pos:pos eff with
          | ((ps,_,_), Tctx.Effect ops) ->
              begin match r with
              | None -> ()
              | Some (e, lst) ->
                  let te = infer_expr ctx cstr e in
                  List.iter
                    (fun (op, (((_,pos1), (_,pos2), (_,posc)) as a)) ->
                       match C.lookup op ops with
                       | None -> Error.typing ~pos "Effect type %s does not have operation %s" eff op
                       | Some (u1, u2) ->
                           let t1, t2, t = infer_abstraction2 ctx cstr a in
                           add_ty_constraint cstr pos1 t1 u1;
                           add_ty_constraint cstr pos2 t2 te;
                           add_dirty_constraint cstr posc t (T.Tuple [u2; te], T.empty_dirt))
                    lst
              end;
              (* XXX Here we need to change T.Apply to something that creates an
                 effect instance/region thingy. *)
              T.Apply (eff, List.map (fun p -> Type.TyParam p) ps), T.empty_dirt
          | _ -> Error.typing ~pos "Effect type expected but %s encountered" eff
          end

      | Core.While (c1, c2) ->
        let dirt = T.fresh_dirt () in
        let t1 = infer ctx c1 in
          add_dirty_constraint cstr pos t1 (T.bool_ty, dirt);
          let t2 = infer ctx c2 in
          add_dirty_constraint cstr pos t2 (T.unit_ty, dirt);
          (* XXX could add "diverges" dirt *)
          (T.unit_ty, dirt)

      | Core.For (i, e1, e2, c, _) ->
          let t1 = infer_expr ctx cstr e1 in
          add_ty_constraint cstr (snd e1) t1 T.int_ty;
          let t2 = infer_expr ctx cstr e2 in
          add_ty_constraint cstr (snd e2) t2 T.int_ty;
          let ctx = Ctx.extend_ty ctx i T.int_ty in
          let t = infer ctx c in
          let dirt = T.fresh_dirt () in
          add_dirty_constraint cstr (snd c) t (T.unit_ty, dirt);
          (T.unit_ty, dirt)

      | Core.Handle (e1, c2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2, d2 = infer ctx c2 in
          let t3 = T.fresh_ty () in
          let t1' = T.Handler {T.value = t2; T.finally = t3} in
            add_ty_constraint cstr pos t1' t1;
            (t3, d2)

      | Core.Let (defs, c) -> 
          let _, dlet, ctx = infer_let ctx cstr pos defs in
          let tc, dc = infer ctx c in
          let dirt = T.fresh_dirt () in
            add_dirt_constraint cstr pos dlet dirt ;
            add_dirt_constraint cstr pos dc dirt ;
            tc, dirt

      | Core.LetRec (defs, c) ->
          let _, ctx = infer_let_rec ctx cstr pos defs in
          infer ctx c

      | Core.Check c ->
          ignore (infer ctx c);
          T.unit_ty, T.empty_dirt
  in
  let ty = infer ctx cp in
    ty

