open CoreUtils
module T = Type
module Untyped = UntypedSyntax
module Ctx = SimpleCtx
module Unify = SimpleUnify

type state = {
  context: Ctx.t;
  constraints: (T.ty * Tctx.T.ty * Location.t) list
}


let initial_state = {
  context= Ctx.empty;
  constraints= []
}

let replace_ctx st ctx = {st with context = ctx}

let warn_implicit_sequencing = ref false

(* We perform type inference int the style of Standard ML 97, i.e.,
   Hindley-Milner polymorphism with value restriction. Throughout, we work with
   a reference to a type substitution, usually called [cstr], in which we
   collect the results of unification. That is, we perform unification as early
   as locssible (rather than collect all equations and then solve them), and
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
  | Untyped.Value _ -> true
  | Untyped.Apply _ | Untyped.Match _ | Untyped.Handle _ | Untyped.Let _
   |Untyped.LetRec _ | Untyped.Check _ ->
      false

let empty_constraint = []

let empty_constraints st = {st with constraints = empty_constraint}

let add_ty_constraint st loc t1 t2 = {st with constraints = (t1, t2, loc):: st.constraints}

let extend_ty st x t = {st with context = Ctx.extend_ty st.context x t}

let extend st x ty_scheme = {st with context = Ctx.extend st.context x ty_scheme}

let subst_ctx st sbst = {st with context = Ctx.subst_ctx st.context sbst}

let generalize st = Ctx.generalize st.context

let ctx_lookup st = Ctx.lookup st.context

let infer_effect st = Ctx.infer_effect st.context

let add_effect st eff (ty1, ty2) = {st with context = Ctx.add_effect st.context eff (ty1, ty2)}

(* [infer_pattern cstr pp] infers the type of pattern [pp]. It returns the list of
   pattern variables with their types, which are all guaranteed to be [Type.Meta]'s, together
   with the type of the pattern and updated state. *)
let infer_pattern st pp =
  (* XXX *)
  (*   if not (Pattern.linear_pattern pp) then
    Error.typing ~loc:(snd pp) "Variables in a pattern must be distinct." ; *)
  let rec infer st' vars {it= p; at= loc}=
    match p with
    | Untyped.PVar x ->
        let t = T.fresh_ty () in
        (t, st', (x,t):: vars)
    | Untyped.PAnnotated (p, t) ->
        let (p_t, st', vars) = infer st' vars p in
        (p_t, add_ty_constraint st' loc p_t t, vars)
    | Untyped.PAs (p, x) ->
        let (p_t, st', vars) = infer st' vars p in
        (p_t, st', (x, p_t) :: vars)
    | Untyped.PNonbinding -> (T.fresh_ty (), st', vars)
    | Untyped.PConst const -> (T.Basic (Const.infer_ty const), st', vars)
    | Untyped.PTuple ps -> 
      let ((st', vars), pst) = fold_map 
      (fun (st'', vars') pa -> 
        let (t, st'', vars') = infer st'' vars' pa in
        ((st'', vars'), t)
      ) (st', vars) ps in
      (T.Tuple pst, st', vars)
    | Untyped.PRecord flds -> (
      match Assoc.pop flds with
      | None -> assert false
      | Some ((fld, _), _) -> (
        match Tctx.infer_field fld with
        | None ->
            Error.typing ~loc "Unbound record field label %t"
              (CoreTypes.Field.print fld)
        | Some (ty, (t, us)) ->
            let unify_record_pattern (st'', vars') (fld, p) =
              match Assoc.lookup fld us with
              | None ->
                  Error.typing ~loc
                    "Unexpected field %t in a pattern of type %t."
                    (CoreTypes.Field.print fld)
                    (CoreTypes.TyName.print t)
              | Some u -> 
                let (t, st'', vars') = infer st'' vars' p in
                (add_ty_constraint st'' loc t u, vars')
            in
            let (st', vars) = Assoc.fold_left unify_record_pattern (st', vars) flds in
            (ty, st', vars) 
          ) 
        )
    | Untyped.PVariant (lbl, p) -> (
      match Tctx.infer_variant lbl with
      | None -> assert false
      | Some (ty, u) ->( 
        match (p, u) with
        | None, None -> (ty, st', vars)
        | Some p, Some u -> (
          let (t, st', vars) = infer st' vars p in 
          (ty, add_ty_constraint st' loc t u, vars)
          )
        | None, Some _ -> assert false
        | Some _, None -> assert false 
      )
    )
  in
  let (t, st, vars) = infer st [] pp in
  (vars, t, st)

let extend_with_pattern ?(forbidden_vars = []) st p =
  let (vars, t, st) = infer_pattern st p in
  match List.find_opt (fun (x, _) -> List.mem_assoc x vars) forbidden_vars with
  | Some (x, _) ->
      Error.typing ~loc:p.at "Several definitions of %t."
        (CoreTypes.Variable.print x)
  | None ->
      let st =
        List.fold_right (fun (x, t) st' -> extend_ty st' x t) vars st
      in
      (vars, t, st)

let rec infer_abstraction st (p, c) =
  let old_ctx = st.context in
  let _, t1, st = extend_with_pattern st p in
  let (t2, st) = infer_comp st c in
  (t1, t2, replace_ctx st old_ctx)

and infer_handler_case_abstraction st (p, k, e) =
  let old_ctx = st.context in
  let vs, t1, st = extend_with_pattern st p in
  let _, tk, st = extend_with_pattern ~forbidden_vars:vs st k in
  let (t2, st) = infer_comp st e in
  (tk, t1, t2, replace_ctx st old_ctx)

and infer_let st loc defs =
  ( if !warn_implicit_sequencing && List.length defs >= 2 then
    let locations = List.map (fun (_, c) -> c.at) defs in
    Print.warning ~loc
      "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
      (Print.sequence "," Location.print locations) ) ;
  let rec find_duplicate xs ys =
    match xs with
    | [] -> None
    | x :: xs -> if List.mem x ys then Some x else find_duplicate xs ys
  in
  let infer_fold_fun (vs, st') (p, c) =
    let (tc, st') = infer_comp st' c in
    let (ws, tp, st') = infer_pattern st' p in
    let st' = add_ty_constraint st' c.at tc tp in
    match find_duplicate (List.map fst ws) (List.map fst vs) with
    | Some x ->
        Error.typing ~loc "Several definitions of %t."
          (CoreTypes.Variable.print x)
    | None ->
        let sbst = Unify.solve st'.constraints in
        let ws = Assoc.map (T.subst_ty sbst) (Assoc.of_list ws) in
        let st' = subst_ctx st' sbst in
        let ws = Assoc.map (generalize st' (nonexpansive c.it)) ws in
        let ws = Assoc.to_list ws in
        let st' =
          List.fold_right
            (fun (x, ty_scheme) st'' -> extend st'' x ty_scheme)
            ws st'
        in
        (List.rev ws @ vs, st')
  in
  let vars, st = List.fold_left infer_fold_fun ([], st) defs in
  (vars, subst_ctx st (Unify.solve st.constraints))

and infer_let_rec st loc defs =
  if not (no_duplicates (List.map fst defs)) then
    Error.typing ~loc "Multiply defined recursive value." ;
  let lst =
    List.map
      (fun (f, (p, c)) ->
        let u1 = T.fresh_ty () in
        let u2 = T.fresh_ty () in
        (f, u1, u2, p, c) )
      defs
  in
  let vars =
    List.fold_right
      (fun (f, u1, u2, _, _) vars -> (f, T.Arrow (u1, u2)) :: vars)
      lst []
  in
  let old_ctx = st.context in
  let st =
    List.fold_right
      (fun (f, u1, u2, _, _) st' -> extend_ty st' f (T.Arrow (u1, u2)))
      lst st
  in
   let st = List.fold_left
    (fun st' (_, u1, u2, p, c) ->
      let old_ctx = st'.context in
      let _, tp, st' = extend_with_pattern st' p in
      let (tc, st') = infer_comp st' c in
      let st' = replace_ctx st' old_ctx in
      let st' = add_ty_constraint st' p.at u1 tp in
      add_ty_constraint st' c.at u2 tc 
      )
  st 
  lst in
  let st = replace_ctx st old_ctx in
  let sbst = Unify.solve st.constraints in
  let vars = Assoc.map (T.subst_ty sbst) (Assoc.of_list vars) in
  let st = subst_ctx st sbst in
  let vars = Assoc.map (generalize st true) vars in
  let vars = Assoc.to_list vars in
  let st =
    List.fold_right
      (fun (x, ty_scheme) st' -> extend st' x ty_scheme)
      vars st
  in
  (vars, st)

(* [infer_expr st (e,loc)] infers the type of expression [e] in state
   [st]. It returns the inferred type of [e] and updated state. *)
and infer_expr st {it= e; at= loc} =
  let (tty, st) = match e with
  | Untyped.Var x -> (ctx_lookup ~loc st x, st)
  | Untyped.Const const -> (T.Basic (Const.infer_ty const), st)
  | Untyped.Annotated (t, ty) ->
      let (ty', st) = infer_expr st t in
      (ty, add_ty_constraint st loc ty ty')
  | Untyped.Tuple es -> (
    let (st, tys) = fold_map (fun st' e -> 
      let (t, st') = infer_expr st' e in
      (st', t)
    ) 
    st es 
    in 
    (T.Tuple tys, st)
  )
  | Untyped.Record flds -> (
    match Assoc.pop flds with
    | None -> assert false
    | Some ((fld, _), _) -> (
      (* XXX *)
      (*       if not (Pattern.linear_record flds') then
          Error.typing ~loc "Fields in a record must be distinct." ;*)
      match Tctx.infer_field fld with
      | None ->
          Error.typing ~loc "Unbound record field label %t in a pattern"
            (CoreTypes.Field.print fld)
      | Some (ty, (t_name, arg_types)) ->
          if Assoc.length flds <> Assoc.length arg_types then
            Error.typing ~loc "malformed record of type %t"
              (CoreTypes.TyName.print t_name)
          else
            let (st, arg_types') = Assoc.fold_map (fun st' e -> 
              let (t, st') = infer_expr st' e in
              st', t)
            st flds in
            let unify_record_arg st' (fld, t) =
              match Assoc.lookup fld arg_types with
              | None ->
                  Error.typing ~loc
                    "Unexpected record field label %t in a pattern"
                    (CoreTypes.Field.print fld)
              | Some u -> add_ty_constraint st' loc t u
            in
            (ty, Assoc.fold_left unify_record_arg st arg_types')
      ) 
    )
  | Untyped.Variant (lbl, u) -> (
    match Tctx.infer_variant lbl with
    | None -> assert false
    | Some (ty, arg_type) ->
        ( match (arg_type, u) with
        | None, None -> (ty, st)
        | Some ty_, Some u ->
            let (ty', st) = infer_expr st u in
            (ty, add_ty_constraint st loc ty_ ty')
        | _, _ -> assert false ) ;
    )
  | Untyped.Lambda a ->
      let (t1, t2, st) = infer_abstraction st a in
      (T.Arrow (t1, t2), st)
  | Untyped.Effect op -> (
    match infer_effect st op with
    | None ->
        Error.typing ~loc "Unbound operation %t" (CoreTypes.Effect.print op)
    | Some (t1, t2) -> (T.Arrow (t1, t2), st) 
  )
  | Untyped.Handler{ Untyped.effect_clauses= ops
      ; Untyped.value_clause= a_val
      ; Untyped.finally_clause= a_fin } ->(
      let t_value = T.fresh_ty () in
      let t_finally = T.fresh_ty () in
      let t_yield = T.fresh_ty () in
      let unify_operation st' (op, a2) =
        match infer_effect st' op with
        | None ->
            Error.typing ~loc "Unbound operation %t in a handler"
              (CoreTypes.Effect.print op)
        | Some (t1, t2) ->
            let (tk, u1, u2, st') = infer_handler_case_abstraction st' a2 in
            let st' = add_ty_constraint st' loc t1 u1 in
            (* XXX maybe we need to change the direction of inequalities here,
                     or even require equalities. *)
            let st' = add_ty_constraint st' loc tk (T.Arrow (t2, t_yield)) in
            add_ty_constraint st' loc t_yield u2
      in
      let st = Assoc.fold_left unify_operation st ops in
      let (valt1, valt2, st) = infer_abstraction st a_val in
      let (fint1, fint2, st) = infer_abstraction st a_fin in
      let st = add_ty_constraint st loc valt1 t_value in
      let st = add_ty_constraint st loc valt2 t_yield in
      let st = add_ty_constraint st loc fint2 t_finally in
      let st = add_ty_constraint st loc fint1 t_yield in
      (T.Handler {T.value= t_value; T.finally= t_finally}, st)
    )
    in 
    (tty, st)

(* [infer_comp ctx cstr (c,loc)] infers the type of computation [c] in context [ctx].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp st cp =

  let rec infer st' {it= c; at= loc} =
    match c with
    | Untyped.Apply (e1, e2) ->
        let (t1, st') = infer_expr st' e1 in
        let (t2, st') = infer_expr st' e2 in
        let t = T.fresh_ty () in
        (t, add_ty_constraint st' loc t1 (T.Arrow (t2, t)))
    | Untyped.Value e -> infer_expr st' e
    | Untyped.Match (e, []) ->
        let (t_in, st') = infer_expr st' e in
        let t_out = T.fresh_ty () in
        (t_out, add_ty_constraint st' loc t_in T.empty_ty) 
    | Untyped.Match (e, lst) ->
        let (t_in, st') = infer_expr st' e in
        let t_out = T.fresh_ty () in
        let infer_case st'' ((p, e') as a) =
          let t_in', t_out', st'' = infer_abstraction st'' a in
          let st'' = (add_ty_constraint st'' e.at t_in t_in') in
          add_ty_constraint st'' e'.at t_out' t_out
        in
        let st' = List.fold_left infer_case st' lst in
        (t_out, st')
    | Untyped.Handle (e1, c2) ->
        let (t1, st') = infer_expr st' e1 in
        let (t2, st') = infer st' c2 in
        let t3 = T.fresh_ty () in
        let t1' = T.Handler {T.value= t2; T.finally= t3} in
        (t3, add_ty_constraint st' loc t1' t1)
    | Untyped.Let (defs, c) ->
        let _, st' = infer_let st' loc defs in
        infer st' c
    | Untyped.LetRec (defs, c) ->
        let _, st' = infer_let_rec st' loc defs in
        infer st' c
    | Untyped.Check c ->
        let _, st' = infer st' c in
        (T.unit_ty, st')
  in
  infer st cp

let infer_top_comp st c =
  let st = empty_constraints st in
  let (ty, st) = infer_comp st c in
  let cstr = st.constraints in 
  let sbst = Unify.solve cstr in
  Exhaust.check_comp c ;
  let st = subst_ctx st sbst in
  let ty = Type.subst_ty sbst ty in
  (st, generalize st (nonexpansive c.it) ty)

let infer_top_let ~loc st defs =
  let vars, st = infer_let st Location.unknown defs in
  List.iter
    (fun (p, c) -> Exhaust.is_irrefutable p ; Exhaust.check_comp c)
    defs ;
  (vars, st)

let infer_top_let_rec ~loc st defs =
  let vars, st =
    infer_let_rec st Location.unknown defs
  in
  let exhaust_check (_, (p, c)) =
    Exhaust.is_irrefutable p ; Exhaust.check_comp c
  in
  List.iter exhaust_check defs ;
  (vars, st)
