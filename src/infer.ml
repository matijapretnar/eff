module C = Common
module I = Inter
module T = Type

let warn_implicit_sequencing = ref false ;;

let disable_typing = ref false ;;

(* We perform type inference int the style of Standard ML 97, i.e., Hindley-Milner polymorphism
   with value restriction. Throughout we work with a reference to a type substitution, usually
   called [sbst], in which we collect the results of unification. That is, we perform unification
   as early as posssible (rather than collect all equations and then solve them), and store the
   results in [sbst]. 

   The effect of carrying around the substitution is that we need to be careful about when
   to apply it:
   
   1. we apply the substitution to types [t1] and [t2] before trying to solve the
      equation [t1 = t2].

   2. we apply the substitution to a type which we just looked up in the context.
*)

(* [ty_apply ctx pos t lst] applies the type constructor [t] to the given list of arguments. *)
let ty_apply ctx pos t lst =
  match Ctx.lookup_tydef t ctx with
    | None -> Error.typing ~pos:pos "Unknown type %s" t
    | Some (ps, d) ->
        try
          let s = List.combine ps lst in
            T.subst_ty s d
        with
            Invalid_argument "List.combine" ->
              Error.typing ~pos:pos "Type constructors %s should be applied to %d arguments" t (List.length ps)

(* Can a computation safely be generalized, i.e., is it non-expansive in the parlance of
   SML? In our case non-expansive simply means "is a value". *)
let nonexpansive = function
  | I.Value _ -> true
  | (I.Apply _ | I.Match _ | I.While _ | I.For _ | I.New _ | I.Handle _
    | I.Let _ | I.LetRec _ | I.Check _) -> false

(* [generalize_vars sbst ctx vars] generalizes the given variables. *)
let generalize_vars sbst ctx vars =
  let ctx = Ctx.subst_ctx sbst ctx in
  let qs = Ctx.free_params ctx in
    C.assoc_map (fun t -> C.diff (T.free_params (T.subst_ty sbst t)) qs, t) vars

(* [generalize sbst ctx t] returns the variables over which we may generalize type [t]. *)
let generalize sbst ctx t =
  let ctx = Ctx.subst_ctx sbst ctx in
  let ps = T.free_params (T.subst_ty sbst t) in
  let qs = Ctx.free_params ctx in
    C.diff ps qs

(* [unify tctx sbst pos t1 t2] solves the equation [t1 = t2] and stores the solution in
   the substitution [sbst]. *)
let unify tctx sbst pos t1 t2 =
  (* [transparent t] tells us whether the type constructor [t] is transparent, i.e.,
     do we unfold it during unificiation. *)
  let transparent t =
    match Ctx.lookup_tydef t tctx with
      | None -> Error.typing ~pos:pos "Unknown type %s" t
      | Some (_, t) ->
          begin match t with
            | (T.Sum (_::_) | T.Effect _ | T.Record _) -> false
            | (T.Basic _ | T.Apply _ | T.Param _ | T.Sum [] |
               T.Arrow _ | T.Tuple _ | T.Handler _ ) -> true
          end
  in
  let rec unify t1 t2 =
    let t1 = T.subst_ty !sbst t1 in
    let t2 = T.subst_ty !sbst t2 in
      match t1, t2 with

      | (t1, t2) when t1 = t2 -> ()

      (* The order of the next two clauses is important in case we have
         an equation between a [T.Meta] and a [T.Nonpoly] because we should
         not turn a T.Nonpoly to a T.Meta which might get polymorphic later on. *)
      | ((T.Param p, t) | (t, T.Param p)) ->
          if T.occurs_in_ty p t
          then begin
            let sbst = T.beautify2 t1 t2 in
            Error.typing ~pos:pos
              "This expression has a forbidden cylclic type %t = %t." (Print.ty ~sbst:sbst [] t1) (Print.ty ~sbst:sbst [] t2)
          end
          else
            let s = [(p, t)] in sbst := T.concat_subst s (T.compose_subst !sbst s)

      | (T.Arrow (u1, v1), T.Arrow (u2, v2)) ->
          unify v1 v2;
          unify u2 u1

      | (T.Tuple lst1, T.Tuple lst2) when List.length lst1 = List.length lst2 ->
          List.iter2 unify lst1 lst2

      | (T.Record lst1, T.Record lst2) ->
          assert false

      | (T.Sum lst1, T.Sum lst2) ->
          assert false

      | (T.Apply (t1, lst1), T.Apply (t2, lst2)) when t1 = t2 && List.length lst1 = List.length lst2  ->
          List.iter2 unify lst1 lst2
            (* The following two cases cannot be merged into one, as the whole matching
               fails if both types are Apply, but only the second one is transparent. *)

      | (T.Apply (t1, lst1), t2) when transparent t1 ->
          unify t2 (ty_apply tctx pos t1 lst1)

      | (t2, T.Apply (t1, lst1)) when transparent t1 ->
          unify t2 (ty_apply tctx pos t1 lst1)

      | (T.Handler h1, T.Handler h2) ->
          unify h2.T.value h1.T.value;
          unify h1.T.finally h2.T.finally

      | (T.Effect lst1, T.Effect lst2) ->
          assert false

      | (t1, t2) ->
          let sbst = T.beautify2 t1 t2 in
            Error.typing ~pos:pos
              "This expression has type %t but it should have type %t." (Print.ty ~sbst:sbst [] t1) (Print.ty ~sbst:sbst [] t2)
  in
    unify t1 t2

(* [infer_pattern tctx sbst pp] infers the type of pattern [pp]. It returns the list of
   pattern variables with their types, which are all guaranteed to be [Type.Meta]'s, together
   with the type of the pattern. *)
let infer_pattern tctx sbst pp =
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
            vars := (x, t) :: !vars ;
            t
      | Pattern.Nonbinding -> T.fresh_param ()
      | Pattern.Const (C.Integer _) -> T.int_ty
      | Pattern.Const (C.String _) -> T.string_ty
      | Pattern.Const (C.Boolean _) -> T.bool_ty
      | Pattern.Const (C.Float _) -> T.float_ty
      | Pattern.Tuple ps -> T.Tuple (C.map infer ps)
      | Pattern.Record [] -> assert false
      | Pattern.Record (((fld, _) :: _) as lst) ->
          let (t, ps, us) = Ctx.infer_field fld tctx in
          let unify_record_pattern (fld, p) =
            begin match C.lookup fld us with
              | None -> Error.typing ~pos:pos "Unexpected field %s in a pattern of type %s." fld t
              | Some u -> unify tctx sbst pos (infer p) u
            end
          in
            List.iter unify_record_pattern lst;
            T.Apply (t, ps)
      | Pattern.Variant (lbl, p) ->
          let (t, ps, u) = Ctx.infer_variant lbl tctx in
            begin match p, u with
              | None, None -> ()
              | Some p, Some u -> unify tctx sbst pos (infer p) u
              | None, Some _ -> Error.typing ~pos:pos "Label %s should be applied to an argument." lbl
              | Some _, None -> Error.typing ~pos:pos "Label %s cannot be applied to an argument." lbl
            end;
            T.Apply (t, ps)
  in
  let t = infer pp in
    !vars, T.subst_ty !sbst t

let extend_with_pattern ?(forbidden_vars=[]) ctx sbst p =
  let vars, t = infer_pattern ctx.Ctx.types sbst p in
  match C.find (fun (x,_) -> List.mem_assoc x vars) forbidden_vars with
    | Some (x,_) -> Error.typing ~pos:(snd p) "Several definitions of %s." x
    | None -> vars, t, Ctx.extend_vars vars ctx

let rec infer_abstraction ctx sbst (p, c) =
  let _, t1, ctx = extend_with_pattern ctx sbst p in
  let t2 = infer_comp ctx sbst c in
    t1, t2

and infer_abstraction2 ctx sbst (p1, p2, c) =
  let vs, t1, ctx = extend_with_pattern ctx sbst p1 in
  let _, t2, ctx = extend_with_pattern ~forbidden_vars:vs ctx sbst p2 in
  let t3 = infer_comp ctx sbst c in
    t1, t2, t3

and infer_handler_case_abstraction ctx sbst k (p, e) =
  let vs, t1, ctx = extend_with_pattern ctx sbst p in
  let _, tk, ctx = extend_with_pattern ~forbidden_vars:vs ctx sbst k in
  let t2 = infer_comp ctx sbst e in
    tk, t1, t2

and infer_let ({Ctx.types=tctx} as ctx) sbst pos defs =
  if !warn_implicit_sequencing then
    begin match defs with
      | [] | [_] -> ()
      | ws ->        
          let positions = List.map (fun (_, (_, pos)) -> pos) ws in
            Print.warning ~pos:pos "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
              (Print.sequence "," Print.position positions)
    end ;
  List.fold_left
    (fun (vs, ctx') (p,c) ->
      let tc = infer_comp ctx sbst c in
      let ws, tp = infer_pattern ctx.Ctx.types sbst p in
      unify tctx sbst (snd c) tc tp ;
      match C.find_duplicate (List.map fst ws) (List.map fst vs) with
        | Some x -> Error.typing ~pos:pos "Several definitions of %s." x
        | None -> 
          let ws =
            (if nonexpansive (fst c)
             then generalize_vars !sbst ctx ws
             else C.assoc_map (fun t -> ([],t)) ws)
          in
          let ctx' = List.fold_right (fun (x,pt) ctx -> Ctx.extend_var x pt ctx) ws ctx' in
            (List.rev ws @ vs, ctx'))
    ([], ctx) defs

and infer_let_rec ({Ctx.types=tctx} as ctx) sbst pos defs =
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
      let _, tp, ctx' = extend_with_pattern ctx' sbst p in
      let tc = infer_comp ctx' sbst c in
      unify tctx sbst (snd p) u1 tp ;
      unify tctx sbst (snd c) u2 tc)
    lst ;
    let vars = generalize_vars !sbst ctx vars in
    let ctx =
      List.fold_right (fun (x,pt) ctx -> Ctx.extend_var x pt ctx) vars ctx
    in
      vars, ctx

(* [infer_expr ctx sbst (e,pos)] infers the type of expression [e] in context
   [ctx]. It returns the inferred type of [e]. *)
and infer_expr ({Ctx.types=tctx} as ctx) sbst (e,pos) =
  match e with
    | I.Var x ->
      begin match C.lookup x ctx.Ctx.variables with
        | Some (ps, t) -> T.refresh ps (T.subst_ty !sbst t)
        | None -> Error.typing ~pos:pos "Unknown name %s" x
      end
    | I.Const (C.Integer _) -> T.int_ty
    | I.Const (C.String _) -> T.string_ty
    | I.Const (C.Boolean _) -> T.bool_ty
    | I.Const (C.Float _) -> T.float_ty
    | I.Tuple es -> T.Tuple (C.map (infer_expr ctx sbst) es)
    | I.Record [] -> assert false
    | I.Record (((fld,_)::_) as lst) ->
      if not (Pattern.linear_record lst) then
        Error.typing ~pos:pos "Fields in a record must be distinct." ;
      let (t_name, params, arg_types) = Ctx.infer_field fld tctx in
      if List.length lst <> List.length arg_types then
        Error.typing ~pos:pos "malformed record of type %s" t_name
      else
        let arg_types' = C.assoc_map (infer_expr ctx sbst) lst in
        let unify_record_arg (fld, t) =
          begin match C.lookup fld arg_types with
            | None -> Error.typing ~pos:pos "Unexpected field %s in a pattern." fld
            | Some u -> unify tctx sbst pos t u
          end
        in
        List.iter unify_record_arg arg_types';
        T.Apply (t_name, params)
          
    | I.Variant (lbl, u) ->
      let (t_name, params, arg_type) = Ctx.infer_variant lbl tctx in
      begin match arg_type, u with
        | None, None -> ()
        | Some ty, Some u ->
          let ty' = infer_expr ctx sbst u in
          unify tctx sbst pos ty ty'
        | _, _ -> Error.typing ~pos:pos "Wrong number of arguments for label %s." lbl
      end;
      T.Apply (t_name, params)
        
    | I.Lambda a ->
      let t1, t2 = infer_abstraction ctx sbst a in
      T.Arrow (t1, t2)
        
    | I.Operation (e, op) ->
      let (t, ps, t1, t2) = Ctx.infer_operation op tctx in
      let u = infer_expr ctx sbst e in
      unify tctx sbst pos u (T.Apply (t, ps)) ;
      T.Arrow (t1, t2)

    | I.Handler {I.operations=ops; I.return=a_ret; I.finally=a_fin} -> 
      let t_value = T.fresh_param () in
      let t_finally = T.fresh_param () in
      let t_yield = T.fresh_param () in
      let unify_operation ((e, op), (k, a)) =
        let (t, ps, t1, t2) = Ctx.infer_operation op tctx in
        let u = infer_expr ctx sbst e in
        unify tctx sbst pos u (T.Apply (t, ps));
        let tk, u1, u2 = infer_handler_case_abstraction ctx sbst k a in
        unify tctx sbst pos t1 u1;
        unify tctx sbst pos tk (T.Arrow (t2, t_yield));
        unify tctx sbst pos t_yield u2
      in
      List.iter unify_operation ops;
      let (rett1, rett2) = infer_abstraction ctx sbst a_ret in
      let (fint1, fint2) = infer_abstraction ctx sbst a_fin in
      unify tctx sbst pos rett1 t_value ;
      unify tctx sbst pos rett2 t_yield ;
      unify tctx sbst pos fint2 t_finally ;
      unify tctx sbst pos fint1 t_yield ;
      T.Handler { T.value = t_value; T.finally = t_finally }
  
(* [infer_comp ctx sbst (c,pos)] infers the type of computation [c] in context [ctx].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp ctx sbst cp =
  if !disable_typing then T.universal_ty else
  let rec infer ({Ctx.types=tctx} as ctx) (c, pos) =
    match c with
      | I.Apply (e1, e2) ->
          let t1 = infer_expr ctx sbst e1 in
          let t2 = infer_expr ctx sbst e2 in
          let t = T.fresh_param () in
            unify tctx sbst pos t1 (T.Arrow (t2, t));
            t
              
      | I.Value e ->
          infer_expr ctx sbst e
            
      | I.Match (e, []) ->
        let t_in = infer_expr ctx sbst e in
        let t_out = T.fresh_param () in
          unify tctx sbst pos t_in T.empty_ty ;
          t_out

      | I.Match (e, lst) ->
          let t_in = infer_expr ctx sbst e in
          let t_out = T.fresh_param () in
          let infer_case ((p, e') as a) =
            let t_in', t_out' = infer_abstraction ctx sbst a in
              unify tctx sbst (snd e) t_in t_in' ;
              unify tctx sbst (snd e') t_out' t_out
          in
            List.iter infer_case lst ;
            t_out
              
      | I.New (eff, r) ->
          begin match Ctx.lookup_tydef eff tctx with
            | None -> Error.typing ~pos:pos "Unknown type %s" eff
            | Some (ps, T.Effect ops) ->
                let subst_pq = C.map (fun p -> (p, T.fresh_param ())) ps in
                let ops = C.assoc_map (fun (t1,t2) -> (T.subst_ty subst_pq t1, T.subst_ty subst_pq t2)) ops in
                  begin match r with
                    | None -> ()
                    | Some (e, lst) ->
                        let te = infer_expr ctx sbst e in
                          List.iter
                            (fun (op, (((_,pos1), (_,pos2), (_,posc)) as a)) ->
                               match C.lookup op ops with
                                 | None -> Error.typing ~pos:pos "Effect type %s does not have operation %s" eff op
                                 | Some (u1, u2) ->
                                     let t1, t2, t = infer_abstraction2 ctx sbst a in
                                       unify tctx sbst pos1 t1 u1 ;
                                       unify tctx sbst pos2 t2 te ;
                                       unify tctx sbst posc t (T.Tuple [u2; te]))
                            lst
                  end ;
                  let qs = List.map snd subst_pq in
                    T.Apply (eff, qs)
            | Some _ -> Error.typing ~pos:pos "Effect type expected but %s encountered" eff
          end

      | I.While (c1, c2) ->
          (let t1 = infer ctx c1 in unify tctx sbst pos t1 T.bool_ty) ;
          (let t2 = infer ctx c2 in unify tctx sbst pos t2 T.unit_ty) ;
          T.unit_ty

      | I.For (i, e1, e2, c, _) ->
          (let t1 = infer_expr ctx sbst e1 in unify tctx sbst (snd e1) t1 T.int_ty) ;
          (let t2 = infer_expr ctx sbst e2 in unify tctx sbst (snd e2) t2 T.int_ty) ;
          let ctx = Ctx.extend_var i ([], T.int_ty) ctx in
          (let t = infer ctx c in unify tctx sbst (snd c) t T.unit_ty) ;
          T.unit_ty

      | I.Handle (e1, e2) ->
          let t1 = infer_expr ctx sbst e1 in
          let t2 = infer ctx e2 in
          let t3 = T.fresh_param () in
          let t1' = T.Handler {T.value = t2; T.finally = t3} in
            unify tctx sbst pos t1' t1;
            t3

      | I.Let (defs, c) -> 
        let _, ctx = infer_let ctx sbst pos defs in
        infer ctx c

      | I.LetRec (defs, c) ->
        let _, ctx = infer_let_rec ctx sbst pos defs in
        infer ctx c

      | I.Check c ->
          ignore (infer ctx c) ;
          T.unit_ty
  in
  infer ctx cp

let infer_top_comp ctx c =
  let sbst = ref T.empty_subst in
  let ty = infer_comp ctx sbst c in
  let ps = (if nonexpansive (fst c) then generalize !sbst ctx ty else []) in
    Ctx.subst_ctx !sbst ctx, (ps, T.subst_ty !sbst ty)

let infer_top_let ({Ctx.types=tctx} as ctx) pos defs =
  let sbst = ref T.empty_subst in
  let vars, ctx = infer_let ctx sbst pos defs in
    let ctx = Ctx.subst_ctx !sbst ctx in
    let vars = C.assoc_map (fun (ps,t) -> (ps, T.subst_ty !sbst t)) vars in
      vars, ctx

let infer_top_let_rec ctx pos defs =
  let sbst = ref T.empty_subst in
  let vars, ctx = infer_let_rec ctx sbst pos defs in
  let ctx = Ctx.subst_ctx !sbst ctx in
  let vars = C.assoc_map (fun (ps,t) -> (ps, T.subst_ty !sbst t)) vars in
  vars, ctx

(** [check_ty ctx pos t] checks that type [t] is well-formed in context [ctx]. *)
let check_ty ctx pos =
  let rec check = function
    | (T.Basic _ | T.Param _) -> ()
    | T.Apply (t, lst) ->
        begin match Ctx.lookup_tydef t ctx with
          | None -> Error.typing ~pos:pos "Unknown type constructors %s" t
          | Some (ps, _) ->
              let n = List.length ps in
                if List.length lst <> n then
                  Error.typing ~pos:pos "Type constructors %s should be applied to %d arguments" t n
        end
    | T.Arrow (t1, t2) -> check t1; check t2
    | T.Tuple lst -> List.iter check lst
    | T.Record lst ->
        if not (Pattern.linear_record lst) then Error.typing ~pos:pos "Fields in a record type must be distinct" ;
        List.iter (fun (_,t) -> check t) lst
    | T.Sum lst ->
        if not (Pattern.linear_record lst) then Error.typing ~pos:pos "Alternatives in a sum type must be distinct" ;
        List.iter (function (_,None) -> () | (_, Some t) -> check t) lst
    | T.Effect lst ->
        if not (Pattern.linear_record lst) then Error.typing ~pos:pos "Operations in an effect type must be distinct" ;
        List.iter (fun (_,(t1,t2)) -> check t1; check t2) lst
    | T.Handler {T.value=t1; T.finally=t2} -> check t1; check t2
  in
    check

let check_ty_noncyclic ctx pos =
  let rec check forbidden = function
    | (T.Basic _ | T.Sum _ | T.Param _) -> ()
    | T.Apply (t, lst) ->
        if List.mem t forbidden
        then Error.typing ~pos:pos "Type definition %s is cyclic." t
        else check (t :: forbidden) (ty_apply ctx pos t lst)
    | T.Arrow (t1, t2) -> check forbidden t1; check forbidden t2
    | T.Tuple lst -> List.iter (check forbidden) lst
    | T.Record lst -> List.iter (fun (_,t) -> check forbidden t) lst
    | T.Effect lst -> List.iter (fun (_,(t1,t2)) -> check forbidden t1; check forbidden t2) lst
    | T.Handler {T.value=t1; T.finally=t2} -> check forbidden t1; check forbidden t2
  in
    check []

(** [check_tydef ctx defs] checks that the simulatenous type definitions [defs]
    is well-formed in context [ctx]. It returns the new context with the type
    definitions added to it. *)
let check_tydef ctx pos defs =
  let check_names {Ctx.types=tctx} = function
    | (T.Basic _ | T.Apply _ | T.Param _ | T.Arrow _ | T.Tuple _ | T.Handler _) -> ()
    | T.Record lst ->
        List.iter (fun (f,_) ->
                     match Ctx.find_field f tctx with
                       | Some u -> Error.typing ~pos:pos "Field %s is already used in type %s" f u
                       | None -> ()
                  ) lst
    | T.Sum lst ->
        List.iter (fun (lbl,_) ->
                     match Ctx.find_variant lbl tctx with
                       | Some u -> Error.typing ~pos:pos "Variant %s is already used in type %s" lbl u
                       | None -> ()
                  ) lst
    | T.Effect lst ->
        List.iter (fun (op, _) ->
                     match Ctx.find_operation op tctx with
                       | Some u -> Error.typing ~pos:pos "Operation %s is already used in type %s" op u
                       | None -> ()
                  ) lst
  in
  let ctx =
    List.fold_left
      (fun ctx (t, (ps,d)) -> check_names ctx d ; Ctx.extend_tydef t (ps,d) ctx) ctx defs
  in
    List.iter (fun (_, (_, d)) -> check_ty ctx.Ctx.types pos d) defs ;
    List.iter (fun (_, (_, d)) -> check_ty_noncyclic ctx.Ctx.types pos d) defs ;
    ctx
