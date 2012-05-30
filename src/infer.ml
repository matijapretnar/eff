module C = Common
module I = Inter
module T = Type

let warn_implicit_sequencing = ref false ;;

let disable_typing = ref false ;;

(* We perform type inference int the style of Standard ML 97, i.e.,
   Hindley-Milner polymorphism with value restriction. Throughout, we work with
   a reference to a type substitution, usually called [sbst], in which we
   collect the results of unification. That is, we perform unification as early
   as posssible (rather than collect all equations and then solve them), and
   store the results in [sbst]. 

   The effect of carrying around the substitution is that we need to be careful
   about when to apply it:
   
   1. we apply the substitution to types [t1] and [t2] before trying to solve
      the equation [t1 = t2].

   2. we apply the substitution to a type which we just looked up in the context.
*)

(* Can a computation safely be generalized, i.e., is it non-expansive in the parlance of
   SML? In our case non-expansive simply means "is a value". *)
let nonexpansive = function
  | I.Value _ -> true
  | (I.Apply _ | I.Match _ | I.While _ | I.For _ | I.New _ | I.Handle _
    | I.Let _ | I.LetRec _ | I.Check _) -> false

let unify = Unify.unify

(* [infer_pattern tctx sbst pp] infers the type of pattern [pp]. It returns the list of
   pattern variables with their types, which are all guaranteed to be [Type.Meta]'s, together
   with the type of the pattern. *)
let infer_pattern tctx sbst pp =
  if not (Pattern.linear_pattern pp) then
    Error.typing ~pos:(snd pp) "Fields in a pattern must be distinct." ;
  let vars = ref [] in
  let rec infer (p, pos) =
    match p with
      | Pattern.Var x ->
            let t = (if !disable_typing then T.universal_ty else T.fresh_param ()) in
              vars := (x, t) :: !vars;
              t
      | Pattern.As (p, x) ->
          let t = infer p in
            vars := (x, t) :: !vars ;
            t
      | Pattern.Nonbinding -> T.fresh_param ()
      | Pattern.Const const -> T.ty_of_const const
      | Pattern.Tuple ps -> T.Tuple (C.map infer ps)
      | Pattern.Record [] -> assert false
      | Pattern.Record (((fld, _) :: _) as lst) ->
          let (t, ps, us) = Tctx.infer_field fld tctx in
          let unify_record_pattern (fld, p) =
            begin match C.lookup fld us with
              | None -> Error.typing ~pos:pos "Unexpected field %s in a pattern of type %s." fld t
              | Some u -> unify tctx sbst pos (infer p) u
            end
          in
            List.iter unify_record_pattern lst;
            T.Apply (t, ps)
      | Pattern.Variant (lbl, p) ->
          let (t, ps, u) = Tctx.infer_variant lbl tctx in
            begin match p, u with
              | None, None -> ()
              | Some p, Some u -> unify tctx sbst pos (infer p) u
              | None, Some _ -> Error.typing ~pos:pos "Label %s should be applied to an argument." lbl
              | Some _, None -> Error.typing ~pos:pos "Label %s cannot be applied to an argument." lbl
            end;
            T.Apply (t, ps)
  in
  let t = infer pp in
    !vars, t

let extend_with_pattern ?(forbidden_vars=[]) tctx ctx sbst p =
  let vars, t = infer_pattern tctx sbst p in
  match C.find (fun (x,_) -> List.mem_assoc x vars) forbidden_vars with
    | Some (x,_) -> Error.typing ~pos:(snd p) "Several definitions of %s." x
    | None -> vars, t, Ctx.extend_vars vars ctx

let rec infer_abstraction tctx ctx sbst (p, c) =
  let _, t1, ctx = extend_with_pattern tctx ctx sbst p in
  let t2 = infer_comp tctx ctx sbst c in
    t1, t2

and infer_abstraction2 tctx ctx sbst (p1, p2, c) =
  let vs, t1, ctx = extend_with_pattern tctx ctx sbst p1 in
  let _, t2, ctx = extend_with_pattern ~forbidden_vars:vs tctx ctx sbst p2 in
  let t3 = infer_comp tctx ctx sbst c in
    t1, t2, t3

and infer_handler_case_abstraction tctx ctx sbst (p, k, e) =
  let vs, t1, ctx = extend_with_pattern tctx ctx sbst p in
  let _, tk, ctx = extend_with_pattern ~forbidden_vars:vs tctx ctx sbst k in
  let t2 = infer_comp tctx ctx sbst e in
    tk, t1, t2

and infer_let tctx ctx sbst pos defs =
  (if !warn_implicit_sequencing && List.length defs >= 2 then
      let positions = List.map (fun (_, (_, pos)) -> pos) defs in
        Print.warning ~pos:pos "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
          (Print.sequence "," Print.position positions));
  let vars, ctx = List.fold_left
    (fun (vs, ctx') (p,c) ->
      let tc = infer_comp tctx ctx sbst c in
      let ws, tp = infer_pattern tctx sbst p in
      unify tctx sbst (snd c) tc tp ;
      Check.is_irrefutable p tctx ;
      match C.find_duplicate (List.map fst ws) (List.map fst vs) with
        | Some x -> Error.typing ~pos:pos "Several definitions of %s." x
        | None -> 
            let ws = Common.assoc_map (T.subst_ty !sbst) ws in
            let ctx = Ctx.subst_ctx !sbst ctx in            
            let ws =
              (if nonexpansive (fst c)
               then Ctx.generalize_vars ctx ws
               else C.assoc_map (fun t -> ([],t)) ws)
          in
          let ctx' = List.fold_right (fun (x,(ps, t)) ctx -> Ctx.extend_var x (ps, t) ctx) ws ctx' in
            (List.rev ws @ vs, ctx'))
    ([], ctx) defs in
  vars, Ctx.subst_ctx !sbst ctx

and infer_let_rec tctx ctx sbst pos defs =
  if not (Common.injective fst defs) then
    Error.typing ~pos:pos "Multiply defined recursive value." ;
  let lst =
    List.map (fun (f,(p,c)) ->
      let u1 = T.fresh_param () in
      let u2 = T.fresh_param () in
      (f, u1, u2, p, c))
      defs
  in
  let vars = List.fold_right (fun (f,u1,u2,_,_) vars -> (f, (T.Arrow (u1, u2))) :: vars) lst [] in
  let ctx' = List.fold_right (fun (f,u1,u2,_,_) ctx -> Ctx.extend_var f ([], T.Arrow (u1, u2)) ctx) lst ctx in
  List.iter
    (fun (_,u1,u2,p,c) ->
      let _, tp, ctx' = extend_with_pattern tctx ctx' sbst p in
      let tc = infer_comp tctx ctx' sbst c in
      unify tctx sbst (snd p) u1 tp ;
      unify tctx sbst (snd c) u2 tc ;
      Check.is_irrefutable p tctx)
    lst ;
  let vars = Common.assoc_map (T.subst_ty !sbst) vars in
  let ctx = Ctx.subst_ctx !sbst ctx in
  let vars = Ctx.generalize_vars ctx vars in
  let ctx = List.fold_right (fun (x,(ps,t)) ctx -> Ctx.extend_var x (ps, t) ctx) vars ctx
  in
  vars, ctx

(* [infer_expr ctx sbst (e,pos)] infers the type of expression [e] in context
   [ctx]. It returns the inferred type of [e]. *)
and infer_expr tctx ctx sbst (e,pos) =
  match e with
    | I.Var x ->
      begin match C.lookup x ctx with
      | Some (ps, t) -> snd (T.refresh ps t)
      | None -> Error.typing ~pos:pos "Unknown name %s" x
      end
    | I.Const const -> T.ty_of_const const
    | I.Tuple es -> T.Tuple (C.map (infer_expr tctx ctx sbst) es)
    | I.Record [] -> assert false
    | I.Record (((fld,_)::_) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos:pos "Fields in a record must be distinct." ;
      let (t_name, params, arg_types) = Tctx.infer_field fld tctx in
      if List.length lst <> List.length arg_types then
        Error.typing ~pos:pos "malformed record of type %s" t_name
      else
        let arg_types' = C.assoc_map (infer_expr tctx ctx sbst) lst in
        let unify_record_arg (fld, t) =
          begin match C.lookup fld arg_types with
            | None -> Error.typing ~pos:pos "Unexpected field %s in a pattern." fld
            | Some u -> unify tctx sbst pos t u
          end
        in
        List.iter unify_record_arg arg_types';
        T.Apply (t_name, params)
          
    | I.Variant (lbl, u) ->
      let (t_name, params, arg_type) = Tctx.infer_variant lbl tctx in
      begin match arg_type, u with
        | None, None -> ()
        | Some ty, Some u ->
          let ty' = infer_expr tctx ctx sbst u in
          unify tctx sbst pos ty ty'
        | _, _ -> Error.typing ~pos:pos "Wrong number of arguments for label %s." lbl
      end;
      T.Apply (t_name, params)
        
    | I.Lambda a ->
      let t1, t2 = infer_abstraction tctx ctx sbst a in
      T.Arrow (t1, t2)
        
    | I.Operation (e, op) ->
      let (t, ps, t1, t2) = Tctx.infer_operation op tctx in
      let u = infer_expr tctx ctx sbst e in
      unify tctx sbst pos u (T.Apply (t, ps)) ;
      T.Arrow (t1, t2)

    | I.Handler {I.operations=ops; I.value=a_val; I.finally=a_fin} -> 
      let t_value = T.fresh_param () in
      let t_finally = T.fresh_param () in
      let t_yield = T.fresh_param () in
      let unify_operation ((e, op), a2) =
        let (t, ps, t1, t2) = Tctx.infer_operation op tctx in
        let u = infer_expr tctx ctx sbst e in
        unify tctx sbst pos u (T.Apply (t, ps));
        let tk, u1, u2 = infer_handler_case_abstraction tctx ctx sbst a2 in
        unify tctx sbst pos t1 u1;
        unify tctx sbst pos tk (T.Arrow (t2, t_yield));
        unify tctx sbst pos t_yield u2
      in
      List.iter unify_operation ops;
      let (valt1, valt2) = infer_abstraction tctx ctx sbst a_val in
      let (fint1, fint2) = infer_abstraction tctx ctx sbst a_fin in
      unify tctx sbst pos valt1 t_value ;
      unify tctx sbst pos valt2 t_yield ;
      unify tctx sbst pos fint2 t_finally ;
      unify tctx sbst pos fint1 t_yield ;
      T.Handler { T.value = t_value; T.finally = t_finally }
  
(* [infer_comp ctx sbst (c,pos)] infers the type of computation [c] in context [ctx].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp tctx ctx sbst cp =
  if !disable_typing then T.universal_ty else
  let rec infer ctx (c, pos) =
    match c with
      | I.Apply (e1, e2) ->
          let t1 = infer_expr tctx ctx sbst e1 in
          let t2 = infer_expr tctx ctx sbst e2 in
          let t = T.fresh_param () in
            unify tctx sbst pos t1 (T.Arrow (t2, t));
            t
              
      | I.Value e ->
          infer_expr tctx ctx sbst e
            
      | I.Match (e, []) ->
        let t_in = infer_expr tctx ctx sbst e in
        let t_out = T.fresh_param () in
          unify tctx sbst pos t_in T.empty_ty ;
          t_out

      | I.Match (e, lst) ->
          let t_in = infer_expr tctx ctx sbst e in
          let t_out = T.fresh_param () in
          let infer_case ((p, e') as a) =
            let t_in', t_out' = infer_abstraction tctx ctx sbst a in
              unify tctx sbst (snd e) t_in t_in' ;
              unify tctx sbst (snd e') t_out' t_out
          in
            List.iter infer_case lst ;
            Check.check_patterns ~pos:pos (List.map fst lst) tctx ;
            t_out
              
      | I.New (eff, r) ->
          begin match Tctx.fresh_tydef ~pos:pos tctx eff with
          | (ps, T.Effect ops) ->
              begin match r with
              | None -> ()
              | Some (e, lst) ->
                  let te = infer_expr tctx ctx sbst e in
                  List.iter
                    (fun (op, (((_,pos1), (_,pos2), (_,posc)) as a)) ->
                       match C.lookup op ops with
                       | None -> Error.typing ~pos:pos "Effect type %s does not have operation %s" eff op
                       | Some (u1, u2) ->
                           let t1, t2, t = infer_abstraction2 tctx ctx sbst a in
                           unify tctx sbst pos1 t1 u1 ;
                           unify tctx sbst pos2 t2 te ;
                           unify tctx sbst posc t (T.Tuple [u2; te]))
                    lst
              end ;
              T.Apply (eff, List.map (fun p -> Type.Param p) ps)
          | _ -> Error.typing ~pos:pos "Effect type expected but %s encountered" eff
          end

      | I.While (c1, c2) ->
          let t1 = infer ctx c1 in
          unify tctx sbst pos t1 T.bool_ty;
          let t2 = infer ctx c2 in
          unify tctx sbst pos t2 T.unit_ty;
          T.unit_ty

      | I.For (i, e1, e2, c, _) ->
          let t1 = infer_expr tctx ctx sbst e1 in
          unify tctx sbst (snd e1) t1 T.int_ty;
          let t2 = infer_expr tctx ctx sbst e2 in
          unify tctx sbst (snd e2) t2 T.int_ty;
          let ctx = Ctx.extend_var i ([], T.int_ty) ctx in
          let t = infer ctx c in
          unify tctx sbst (snd c) t T.unit_ty;
          T.unit_ty

      | I.Handle (e1, e2) ->
          let t1 = infer_expr tctx ctx sbst e1 in
          let t2 = infer ctx e2 in
          let t3 = T.fresh_param () in
          let t1' = T.Handler {T.value = t2; T.finally = t3} in
            unify tctx sbst pos t1' t1;
            t3

      | I.Let (defs, c) -> 
          let _, ctx = infer_let tctx ctx sbst pos defs in
          infer ctx c

      | I.LetRec (defs, c) ->
          let _, ctx = infer_let_rec tctx ctx sbst pos defs in
          infer ctx c

      | I.Check c ->
          ignore (infer ctx c) ;
          T.unit_ty
  in
  infer ctx cp
