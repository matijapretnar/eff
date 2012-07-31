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

let add_constraint cstr pos t1 t2 = cstr := (t1, t2, pos) :: !cstr

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
          let t = (if !disable_typing then T.universal_ty else T.fresh_param ()) in
          vars := (x, t) :: !vars;
          t
      | Pattern.As (p, x) ->
          let t = infer p in
          vars := (x, t) :: !vars;
          t
      | Pattern.Nonbinding -> T.fresh_param ()
      | Pattern.Const const -> ty_of_const const
      | Pattern.Tuple ps -> T.Tuple (C.map infer ps)
      | Pattern.Record [] -> assert false
      | Pattern.Record (((fld, _) :: _) as lst) ->
          let (t, ps, us) = Tctx.infer_field fld !Tctx.global in
          let unify_record_pattern (fld, p) =
          begin match C.lookup fld us with
          | None -> Error.typing ~pos:pos "Unexpected field %s in a pattern of type %s." fld t
          | Some u -> add_constraint cstr pos (infer p) u
          end
          in
            List.iter unify_record_pattern lst;
            T.Apply (t, ps)
      | Pattern.Variant (lbl, p) ->
          let (t, ps, u) = Tctx.infer_variant lbl !Tctx.global in
          begin match p, u with
          | None, None -> ()
          | Some p, Some u -> add_constraint cstr pos (infer p) u
          | None, Some _ -> Error.typing ~pos:pos "Label %s should be applied to an argument." lbl
          | Some _, None -> Error.typing ~pos:pos "Label %s cannot be applied to an argument." lbl
          end;
          T.Apply (t, ps)
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
    t1, t2

and infer_abstraction2 ctx cstr (p1, p2, c) =
  let vs, t1, ctx = extend_with_pattern ctx cstr p1 in
  let _, t2, ctx = extend_with_pattern ~forbidden_vars:vs ctx cstr p2 in
  let t3 = infer_comp ctx cstr c in
    t1, t2, t3

and infer_handler_case_abstraction ctx cstr (p, k, e) =
  let vs, t1, ctx = extend_with_pattern ctx cstr p in
  let _, tk, ctx = extend_with_pattern ~forbidden_vars:vs ctx cstr k in
  let t2 = infer_comp ctx cstr e in
    tk, t1, t2

and infer_let ctx cstr pos defs =
  (if !warn_implicit_sequencing && List.length defs >= 2 then
      let positions = List.map (fun (_, (_, pos)) -> pos) defs in
        Print.warning ~pos:pos "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
          (Print.sequence "," Print.position positions));
  let vars, ctx = List.fold_left
    (fun (vs, ctx') (p,c) ->
      let tc = infer_comp ctx cstr c in
      let ws, tp = infer_pattern cstr p in
      add_constraint cstr (snd c) tc tp;
      Check.is_irrefutable p;
      match C.find_duplicate (List.map fst ws) (List.map fst vs) with
        | Some x -> Error.typing ~pos:pos "Several definitions of %s." x
        | None ->
            let sbst = Unify.solve !cstr in
            let ws = Common.assoc_map (T.subst_ty sbst) ws in
            let ctx = Ctx.subst_ctx ctx sbst in            
            let ws = Common.assoc_map (Ctx.generalize ctx (nonexpansive (fst c))) ws
          in
          let ctx' = List.fold_right (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme) ws ctx' in
            (List.rev ws @ vs, ctx'))
    ([], ctx) defs in
  vars, Ctx.subst_ctx ctx (Unify.solve !cstr)

and infer_let_rec ctx cstr pos defs =
  if not (Common.injective fst defs) then
    Error.typing ~pos:pos "Multiply defined recursive value.";
  let lst =
    List.map (fun (f,(p,c)) ->
      let u1 = T.fresh_param () in
      let u2 = T.fresh_param () in
      (f, u1, u2, p, c))
      defs
  in
  let vars = List.fold_right (fun (f,u1,u2,_,_) vars -> (f, (T.Arrow (u1, u2))) :: vars) lst [] in
  let ctx' = List.fold_right (fun (f,u1,u2,_,_) ctx -> Ctx.extend_ty ctx f (T.Arrow (u1, u2))) lst ctx in
  List.iter
    (fun (_,u1,u2,p,c) ->
      let _, tp, ctx' = extend_with_pattern ctx' cstr p in
      let tc = infer_comp ctx' cstr c in
      add_constraint cstr (snd p) u1 tp;
      add_constraint cstr (snd c) u2 tc;
      Check.is_irrefutable p)
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
    | Core.Var x -> Ctx.lookup ~pos:pos ctx x
    | Core.Const const -> ty_of_const const
    | Core.Tuple es -> T.Tuple (C.map (infer_expr ctx cstr) es)
    | Core.Record [] -> assert false
    | Core.Record (((fld,_)::_) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos:pos "Fields in a record must be distinct.";
      let (t_name, params, arg_types) = Tctx.infer_field fld !Tctx.global in
      if List.length lst <> List.length arg_types then
        Error.typing ~pos:pos "malformed record of type %s" t_name
      else
        let arg_types' = C.assoc_map (infer_expr ctx cstr) lst in
        let unify_record_arg (fld, t) =
          begin match C.lookup fld arg_types with
            | None -> Error.typing ~pos:pos "Unexpected field %s in a pattern." fld
            | Some u -> add_constraint cstr pos t u
          end
        in
        List.iter unify_record_arg arg_types';
        T.Apply (t_name, params)
          
    | Core.Variant (lbl, u) ->
      let (t_name, params, arg_type) = Tctx.infer_variant lbl !Tctx.global in
      begin match arg_type, u with
        | None, None -> ()
        | Some ty, Some u ->
            let ty' = infer_expr ctx cstr u in
            add_constraint cstr pos ty ty'
        | _, _ -> Error.typing ~pos:pos "Wrong number of arguments for label %s." lbl
      end;
      T.Apply (t_name, params)
        
    | Core.Lambda a ->
        let t1, t2 = infer_abstraction ctx cstr a in
        T.Arrow (t1, t2)
        
    | Core.Operation (e, op) ->
        let (t, ps, t1, t2) = Tctx.infer_operation op !Tctx.global in
        let u = infer_expr ctx cstr e in
        add_constraint cstr pos u (T.Apply (t, ps));
        T.Arrow (t1, t2)

    | Core.Handler {Core.operations=ops; Core.value=a_val; Core.finally=a_fin} -> 
        let t_value = T.fresh_param () in
        let t_finally = T.fresh_param () in
        let t_yield = T.fresh_param () in
        let unify_operation ((e, op), a2) =
          let (t, ps, t1, t2) = Tctx.infer_operation op !Tctx.global in
          let u = infer_expr ctx cstr e in
          add_constraint cstr pos u (T.Apply (t, ps));
          let tk, u1, u2 = infer_handler_case_abstraction ctx cstr a2 in
          add_constraint cstr pos t1 u1;
          add_constraint cstr pos tk (T.Arrow (t2, t_yield));
          add_constraint cstr pos t_yield u2
        in
        List.iter unify_operation ops;
        let (valt1, valt2) = infer_abstraction ctx cstr a_val in
        let (fint1, fint2) = infer_abstraction ctx cstr a_fin in
        add_constraint cstr pos valt1 t_value;
        add_constraint cstr pos valt2 t_yield;
        add_constraint cstr pos fint2 t_finally;
        add_constraint cstr pos fint1 t_yield;
        T.Handler { T.value = t_value; T.finally = t_finally }
  
(* [infer_comp ctx cstr (c,pos)] infers the type of computation [c] in context [ctx].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp ctx cstr cp =
  if !disable_typing then T.universal_ty else
  let rec infer ctx (c, pos) =
    match c with
      | Core.Apply (e1, e2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer_expr ctx cstr e2 in
          let t = T.fresh_param () in
          add_constraint cstr pos t1 (T.Arrow (t2, t));
          t
              
      | Core.Value e ->
          infer_expr ctx cstr e
            
      | Core.Match (e, []) ->
        let t_in = infer_expr ctx cstr e in
        let t_out = T.fresh_param () in
        add_constraint cstr pos t_in T.empty_ty;
        t_out

      | Core.Match (e, lst) ->
          let t_in = infer_expr ctx cstr e in
          let t_out = T.fresh_param () in
          let infer_case ((p, e') as a) =
            let t_in', t_out' = infer_abstraction ctx cstr a in
            add_constraint cstr (snd e) t_in t_in';
            add_constraint cstr (snd e') t_out' t_out
          in
          List.iter infer_case lst;
          Check.check_patterns ~pos:pos (List.map fst lst);
          t_out
              
      | Core.New (eff, r) ->
          begin match Tctx.fresh_tydef ~pos:pos !Tctx.global eff with
          | (ps, T.Effect ops) ->
              begin match r with
              | None -> ()
              | Some (e, lst) ->
                  let te = infer_expr ctx cstr e in
                  List.iter
                    (fun (op, (((_,pos1), (_,pos2), (_,posc)) as a)) ->
                       match C.lookup op ops with
                       | None -> Error.typing ~pos:pos "Effect type %s does not have operation %s" eff op
                       | Some (u1, u2) ->
                           let t1, t2, t = infer_abstraction2 ctx cstr a in
                           add_constraint cstr pos1 t1 u1;
                           add_constraint cstr pos2 t2 te;
                           add_constraint cstr posc t (T.Tuple [u2; te]))
                    lst
              end;
              T.Apply (eff, List.map (fun p -> Type.TyParam p) ps)
          | _ -> Error.typing ~pos:pos "Effect type expected but %s encountered" eff
          end

      | Core.While (c1, c2) ->
          let t1 = infer ctx c1 in
          add_constraint cstr pos t1 T.bool_ty;
          let t2 = infer ctx c2 in
          add_constraint cstr pos t2 T.unit_ty;
          T.unit_ty

      | Core.For (i, e1, e2, c, _) ->
          let t1 = infer_expr ctx cstr e1 in
          add_constraint cstr (snd e1) t1 T.int_ty;
          let t2 = infer_expr ctx cstr e2 in
          add_constraint cstr (snd e2) t2 T.int_ty;
          let ctx = Ctx.extend_ty ctx i T.int_ty in
          let t = infer ctx c in
          add_constraint cstr (snd c) t T.unit_ty;
          T.unit_ty

      | Core.Handle (e1, e2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer ctx e2 in
          let t3 = T.fresh_param () in
          let t1' = T.Handler {T.value = t2; T.finally = t3} in
            add_constraint cstr pos t1' t1;
            t3

      | Core.Let (defs, c) -> 
          let _, ctx = infer_let ctx cstr pos defs in
          infer ctx c

      | Core.LetRec (defs, c) ->
          let _, ctx = infer_let_rec ctx cstr pos defs in
          infer ctx c

      | Core.Check c ->
          ignore (infer ctx c);
          T.unit_ty
  in
  infer ctx cp
