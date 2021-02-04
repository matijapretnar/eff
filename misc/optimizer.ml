let is_relatively_pure st c h =
  match
    ( TypeChecker.check_computation st.tc_state c,
      TypeChecker.check_handler st.tc_state h )
  with
  | ( (ty, { Type.effect_set = ops; Type.row = Type.EmptyRow }),
      (_, (_, output_dirt)) ) ->
      let handled_ops =
        EffectSet.of_list
          (List.map (fun ((eff, _), _) -> eff) (Assoc.to_list h.effect_clauses))
      in
      (* Print.debug "is_relatively_pure: %t:  %t vs %t" (Term.print_computation c)
         (Type.print_effect_set handled_ops)
         (Type.print_effect_set ops); *)
      if EffectSet.is_empty (EffectSet.inter handled_ops ops) then
        match output_dirt with
        | { Type.effect_set = ops'; Type.row = Type.EmptyRow } ->
            Some
              (BangCoercion
                 ( ReflTy ty,
                   UnionDirt
                     (*( EffectSet.inter ops ops'*)
                     (ops, Empty (Type.closed_dirt (EffectSet.diff ops' ops)))
                 ))
        | { Type.effect_set = ops'; Type.row = Type.ParamRow var } ->
            Some
              (BangCoercion
                 ( ReflTy ty,
                   UnionDirt
                     (*( EffectSet.inter ops ops'*)
                     ( ops,
                       Empty
                         {
                           Type.effect_set = EffectSet.diff ops' ops;
                           Type.row = Type.ParamRow var;
                         } ) ))
      else None
  | _, _ -> None

and reduce_comp st c =
  (* Print.debug "reduce_comp: %t" (Term.print_computation c); *)
  match c with
  | Handle (Handler h, c1) -> (
          match c1 with
          | CastComp (c1', dtyco1) -> (
              match is_relatively_pure st c1' h with
              | Some dtyco ->
                  optimize_comp st
                    (Bind
                       ( CastComp (c1', dtyco),
                         Term.abstraction_with_ty_to_abstraction h.value_clause
                       ))
              | None -> c)
          | Bind (c11, a1) -> (
              match c11 with
              | CastComp (c111, _) -> (
                  match (* TODO: Fix *)
                        is_relatively_pure st c111 h with
                  | Some dtyco ->
                      let p12, c12 = a1 in
                      optimize_comp st
                        (Bind
                           ( CastComp (c111, dtyco),
                             abstraction p12 (Handle (refresh_expr e1, c12)) ))
                  | None -> c)
              | _ ->
                  let (tv, _), _ = TypeChecker.check_handler st.tc_state h in
                  let p12, c12 = a1 in
                  let c_r' = (p12, tv, Handle (e1, c12)) in
                  let h' = { h with value_clause = c_r' } in
                  optimize_comp st (Handle (Handler h', c11)))
          | Call (eff, e11, k_abs) -> (
              (* handle call(eff,e11,y:ty.c) with H@{eff xi ki -> ci}
                 >-->
                  ci [(fun y:ty -> handle c with H)/ki, e11 / xi]
              *)
              let ((k_pat, k_ty, k_c) as k_abs') = refresh_abs_with_ty k_abs in
              let handled_k =
                abstraction_with_ty k_pat k_ty
                  (reduce_comp
                     (extend_pat_type st k_pat k_ty)
                     (Handle (refresh_expr e1, k_c)))
              in
              match Assoc.lookup eff h.effect_clauses with
              | Some eff_clause ->
                  let p1, p2, c = refresh_abs2 eff_clause in
                  (* Shouldn't we check for inlinability of p1 and p2 here? *)
                  substitute_pattern_comp st
                    (Term.subst_comp (Term.pattern_match p1 e11) c)
                    p2 (Lambda handled_k)
              | None ->
                  let k_abs'' = (k_pat, k_ty, Handle (e1, k_c)) in
                  let res = Call (eff, e11, k_abs'') in
                  reduce_comp st res)
      | _ -> c)

(*
  | _ when outOfFuel st -> c

  | Handle ({term = Handler h} as handler, {term = Bind (c1, {term = (p1, c2)})})
        when (is_pure_for_handler c1 h.effect_clauses) ->
    (* Print.debug "Remove handler of outer Bind, since no effects in common with computation"; *)
    reduce_comp st (bind (reduce_comp st c1) (abstraction p1 (reduce_comp st (handle (refresh_expr handler) c2))))

  | Handle ({term = Handler h}, {term = Bind (c1, {term = (p1, c2)})})
        when (is_pure_for_handler c2 h.effect_clauses) ->
    (* Print.debug "Move inner bind into the value case"; *)
    let new_value_clause = optimize_abs st (abstraction p1 (bind (reduce_comp st c2) (refresh_abs h.value_clause))) in
    let hdlr = handler {
      effect_clauses = h.effect_clauses;
      value_clause = refresh_abs new_value_clause;
    } in
    reduce_comp st (handle (refresh_expr hdlr) c1)

    end

(*

type state = {
  inlinable : (Term.variable, unit -> Term.expression) Common.assoc;
  stack : (Term.variable, Term.expression) Common.assoc;
  letrec_memory : (Term.variable, Term.abstraction) Common.assoc;
  handlers_functions_mem : (Term.expression * Term.variable * Term.expression) list;
  handlers_functions_ref_mem : ((Term.expression * Term.variable * Term.expression) list) ref;
  handlers_functions_cont_mem : ((Term.expression * Term.variable * Term.expression) list);
  impure_wrappers : (Term.variable, Term.expression) Common.assoc;
}



let initial = {
  inlinable = [];
  stack = [];
  letrec_memory = [];
  handlers_functions_mem = [];
  impure_wrappers = [];
  handlers_functions_ref_mem = ref [];
  handlers_functions_cont_mem =[];
}

let is_pure c = false
(*   Scheme.is_surely_pure c.Term.scheme *)

let is_pure_for_handler c clauses = false
(*   Scheme.is_surely_pure_for_handler c.Term.scheme (List.map (fun ((eff, _), _) -> eff) clauses) *)

let unused x c =
  let vars = Term.free_vars_comp  c in
  let inside_occ, outside_occ = Term.occurrences x vars in
  inside_occ == 0 && outside_occ == 0


and reduce_expr st e =
  let e' = match e with
  | Var x ->
    begin match find_inlinable st x with
      | Some ({term = Handler _} as d) -> reduce_expr st (refresh_expr d)
      | Some d -> reduce_expr st d
      | _ -> e
    end


and reduce_comp st c =
  let c' = match c with

(*  
  | Handle ({term = Handler h}, c1)
        when (is_pure_for_handler c1 h.effect_clauses) ->
    (* Print.debug "Remove handler, since no effects in common with computation"; *)
    reduce_comp st (bind c1 h.value_clause)

 (*   | Apply ({term = Var v}, e2) ->
    begin match Common.lookup v st.impure_wrappers with
      | Some f ->
  
        let res =
          value (pure (apply f e2))
        in
        reduce_comp st res
      | None -> c
    end
 *)
