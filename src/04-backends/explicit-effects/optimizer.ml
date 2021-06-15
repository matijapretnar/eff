open Utils

type return_clause_kind =
  | FixedReturnClause of Term.abstraction
  | VaryingReturnClause

exception ReturnClauseNotFixed of Language.CoreTypes.Variable.t

type state = {
  declared_functions :
    (Language.CoreTypes.Variable.t, Term.abstraction) Assoc.t;
  fuel : int;
  (* Cache of already specialized functions *)
  specialized_functions :
    ( Term.EffectFingerprint.t * Language.CoreTypes.Variable.t,
      Term.variable * return_clause_kind )
    Assoc.t;
}

let initial_state =
  {
    declared_functions = Assoc.empty;
    fuel = !Config.optimization_fuel;
    specialized_functions = Assoc.empty;
  }

let reduce_if_fuel reduce_term state term =
  if state.fuel > 0 then reduce_term { state with fuel = state.fuel - 1 } term
  else term

let add_function state x abs =
  {
    state with
    declared_functions = Assoc.update x.term abs state.declared_functions;
  }

(* Optimization functions *)

(* Reductions and inlining *)

type inlinability =
  (* Pattern does not occur in in an abstraction body *)
  | NotPresent
  (* Pattern occurs, and occurs at most once in an abstraction and there is no recursion *)
  | Inlinable
  (* Pattern occurs more than once in a body of abstraction or it occurs recursively *)
  | NotInlinable

let abstraction_inlinability { term = pat, cmp; _ } =
  match pat.term with
  | Term.PVar v
    when Term.CoreTypes.Variable.fold
           (fun v _ -> String.length v >= 3 && String.sub v 0 3 = "___")
           v.term ->
      NotInlinable
  | _ ->
      let free_vars_cmp = Term.free_vars_comp cmp in
      let rec check_variables = function
        | [] -> NotPresent
        | x :: xs -> (
            let occ =
              Term.VariableMap.find_opt x free_vars_cmp
              |> Option.value ~default:0
            in
            if occ > 1 then NotInlinable
            else
              match check_variables xs with
              | NotPresent -> if occ = 0 then NotPresent else Inlinable
              | inlinability -> inlinability)
      in
      check_variables (Term.pattern_vars pat)

let keep_used_bindings defs cmp =
  (* Do proper call graph analysis *)
  let free_vars_cmp = Term.free_vars_comp cmp in
  let free_vars_defs =
    List.map (fun (_, a) -> Term.free_vars_abs a) (Assoc.to_list defs)
  in
  let free_vars = Term.concat_vars (free_vars_cmp :: free_vars_defs) in
  List.filter
    (fun (x, _) -> not (Term.does_not_occur x.term free_vars))
    (Assoc.to_list defs)

let rec extract_cast_value comp =
  match comp.term with
  | Term.Value exp -> Some exp
  | Term.CastComp (comp, { term = tcoer, _; _ }) ->
      Option.map
        (fun exp -> Term.castExp (exp, tcoer))
        (extract_cast_value comp)
  | _ -> None

let recast_computation hnd comp =
  match comp.ty with
  | ty, { Type.effect_set = effs; Type.row = EmptyRow } ->
      let handled_effs =
        Type.EffectSet.of_list
          (List.map
             (fun ((eff, _), _) -> eff)
             (Assoc.to_list hnd.term.Term.effect_clauses.effect_part))
      in
      if Type.EffectSet.disjoint effs handled_effs then
        let _, (_, drt_out) = hnd.ty in
        let drt_diff =
          {
            Type.effect_set = Type.EffectSet.diff drt_out.Type.effect_set effs;
            Type.row = drt_out.Type.row;
          }
        in
        let ty_coer = Constraint.reflTy ty
        and drt_coer = Constraint.unionDirt (effs, Constraint.empty drt_diff) in
        Some (Term.castComp (comp, Constraint.bangCoercion (ty_coer, drt_coer)))
      else None
  | _ -> None

let rec optimize_expression state exp =
  let exp' = optimize_expression' state exp in
  (* Print.debug "EXP: %t : %t" (Term.print_expression exp) (Type.print_ty exp.ty); *)
  (* Print.debug "EXP': %t : %t"
     (Term.print_expression exp')
     (Type.print_ty exp'.ty); *)
  assert (Type.equal_ty exp.ty exp'.ty);
  let exp'' = reduce_expression state exp' in
  (* Print.debug "EXP'': %t : %t"
     (Term.print_expression exp'')
     (Type.print_ty exp''.ty); *)
  assert (Type.equal_ty exp'.ty exp''.ty);
  exp''

and optimize_expression' state exp =
  match exp.term with
  | Term.Var _ | Term.Const _ -> exp
  | Term.Tuple exps -> Term.tuple (List.map (optimize_expression state) exps)
  | Term.Record flds -> Term.record (Assoc.map (optimize_expression state) flds)
  | Term.Variant (lbl, arg) ->
      Term.variant (lbl, Option.map (optimize_expression state) arg) exp.ty
  | Term.Lambda abs -> Term.lambda (optimize_abstraction state abs)
  | Term.Handler hnd -> Term.handler (optimize_handler state hnd)
  | Term.CastExp (exp, coer) ->
      Term.castExp (optimize_expression state exp, coer)

and optimize_computation state cmp =
  (* Print.debug "CMP: %t" (Term.print_computation cmp); *)
  let cmp' = optimize_computation' state cmp in
  (* Print.debug "CMP': %t" (Term.print_computation cmp'); *)
  assert (Type.equal_dirty cmp.ty cmp'.ty);
  let cmp'' = reduce_computation state cmp' in
  (* Print.debug "CMP'': %t" (Term.print_computation cmp''); *)
  assert (Type.equal_dirty cmp'.ty cmp''.ty);
  cmp''

and optimize_computation' state cmp =
  match cmp.term with
  | Term.Value exp -> Term.value (optimize_expression state exp)
  | Term.LetVal (exp, abs) ->
      Term.letVal (optimize_expression state exp, optimize_abstraction state abs)
  | Term.LetRec (defs, cmp) ->
      Term.letRec
        (optimize_rec_definitions state defs, optimize_computation state cmp)
  | Term.Match (exp, cases) ->
      Term.match_
        ( optimize_expression state exp,
          List.map (optimize_abstraction state) cases )
        cmp.ty
  | Term.Apply (exp1, exp2) ->
      Term.apply (optimize_expression state exp1, optimize_expression state exp2)
  | Term.Handle (exp, cmp) ->
      Term.handle (optimize_expression state exp, optimize_computation state cmp)
  | Term.Call (eff, exp, abs) ->
      Term.call
        (eff, optimize_expression state exp, optimize_abstraction state abs)
  | Term.Bind (cmp, abs) ->
      Term.bind (optimize_computation state cmp, optimize_abstraction state abs)
  | Term.CastComp (cmp, dtcoer) ->
      Term.castComp (optimize_computation state cmp, dtcoer)

and optimize_handler state hnd =
  {
    hnd with
    term =
      {
        Term.value_clause = optimize_abstraction state hnd.term.value_clause;
        Term.effect_clauses =
          {
            hnd.term.effect_clauses with
            effect_part =
              Assoc.map
                (optimize_abstraction2 state)
                hnd.term.effect_clauses.effect_part;
          };
      };
  }

and optimize_abstraction state abs =
  { abs with term = optimize_abstraction' state abs.term }

and optimize_abstraction' state (pat, cmp) =
  let cmp' = optimize_computation state cmp in
  match (pat.term, cmp'.term) with
  | Term.PVar v, Term.Match ({ term = Var v'; _ }, [ abs ])
  | Term.PVar v, Term.LetVal ({ term = Var v'; _ }, abs)
    when v = v' && Term.does_not_occur v.term (Term.free_vars_abs abs) ->
      abs.term
  | _ -> (pat, cmp')

and optimize_abstraction2 state abs2 =
  { abs2 with term = optimize_abstraction2' state abs2.term }

and optimize_abstraction2' state (pat1, pat2, cmp) =
  (pat1, pat2, optimize_computation state cmp)

and optimize_rec_definitions state defs =
  Assoc.map (optimize_abstraction state) defs

and cast_expression _state exp coer =
  match (exp.term, coer.term) with
  | _, _ when Constraint.is_trivial_ty_coercion coer -> exp
  | _, _ -> Term.castExp (exp, coer)

and cast_computation state comp coer =
  match (comp.term, coer.term) with
  | _, _ when Constraint.is_trivial_dirty_coercion coer -> comp
  | Term.Bind (cmp, abs), (_, dcoer) ->
      let ty1, _ = cmp.ty in
      let coer1 = Constraint.bangCoercion (Constraint.reflTy ty1, dcoer) in
      bind_computation state
        (cast_computation state cmp coer1)
        (cast_abstraction state abs coer)
  | Term.Call (eff, exp, abs), _ ->
      Term.call (eff, exp, cast_abstraction state abs coer)
  | _, _ -> Term.castComp (comp, coer)

and cast_abstraction state { term = pat, cmp; _ } coer =
  Term.abstraction (pat, cast_computation state cmp coer)

and bind_computation state comp bind =
  match comp.term with
  | Term.Bind (comp, abs) ->
      bind_computation state comp (bind_abstraction state abs bind)
  | Term.Call (eff, exp, abs) ->
      Term.call (eff, exp, bind_abstraction state abs bind)
  | _ -> (
      match extract_cast_value comp with
      | Some exp -> beta_reduce state bind exp
      | None -> Term.bind (comp, bind))

and bind_abstraction state { term = pat, cmp; _ } bind =
  Term.abstraction (pat, bind_computation state cmp bind)

and handle_computation state hnd comp =
  match comp.term with
  | Term.Match (exp, cases) ->
      let _, drty_out = hnd.ty in
      Term.match_ (exp, List.map (handle_abstraction state hnd) cases) drty_out
      |> optimize_computation state
  | LetVal (exp, abs) ->
      Term.letVal (exp, handle_abstraction state hnd abs)
      |> optimize_computation state
  | LetRec (defs, comp) ->
      Term.letRec (defs, handle_computation state hnd comp)
      |> optimize_computation state
  | Call (eff, exp, abs) -> (
      let handled_abs = handle_abstraction state hnd abs in
      match Assoc.lookup eff hnd.term.Term.effect_clauses.effect_part with
      | Some { term = p1, p2, comp; _ } ->
          let comp' =
            beta_reduce state
              (Term.abstraction (p2, comp))
              (Term.lambda handled_abs)
          in
          beta_reduce state (Term.abstraction (p1, comp')) exp
      | None -> Term.call (eff, exp, handled_abs))
  | Apply ({ term = Var f; _ }, exp)
    when Option.is_some
           (Assoc.lookup
              (hnd.term.Term.effect_clauses.fingerprint, f.term)
              state.specialized_functions) -> (
      let value_clause = hnd.term.Term.value_clause in
      match
        Assoc.lookup
          (hnd.term.Term.effect_clauses.fingerprint, f.term)
          state.specialized_functions
      with
      | Some (f', FixedReturnClause value_clause') ->
          if value_clause = value_clause' then Term.apply (Term.var f', exp)
          else raise (ReturnClauseNotFixed f.term)
      | Some (f', VaryingReturnClause) ->
          Term.apply
            ( Term.var f',
              Term.tuple [ exp; Term.lambda hnd.term.Term.value_clause ] )
      | None -> assert false)
  | Bind (cmp, abs) ->
      let hnd' =
        Term.handler_with_new_value_clause hnd
          (handle_abstraction state hnd abs)
      in
      handle_computation state hnd' cmp
  | CastComp (cmp, { term = tcoer, dcoer; _ }) ->
      let ty, _ = cmp.ty in
      let x_pat, x_var = Term.fresh_variable "x" ty in
      let hnd' =
        Term.handler_with_new_value_clause hnd
          (Term.abstraction
             ( x_pat,
               Term.letVal (Term.castExp (x_var, tcoer), hnd.term.value_clause)
             ))
      in
      let hnd'' = Term.handler_with_smaller_input_dirt hnd' dcoer in
      handle_computation state hnd'' cmp
  | _ -> (
      match recast_computation hnd comp with
      | Some comp' -> bind_computation state comp' hnd.term.Term.value_clause
      | None -> Term.handle (Term.handler hnd, comp))

and handle_abstraction state hnd { term = p, c; _ } =
  Term.abstraction (p, handle_computation state hnd c)

and beta_reduce state ({ term = _, cmp; _ } as abs) exp =
  (* Print.debug "Beta reduce: %t; %t"
     (Term.print_abstraction abs)
     (Term.print_expression exp); *)
  match (abstraction_inlinability abs, exp.term) with
  | Inlinable, _
  (* Inline constants and variables anyway *)
  | NotInlinable, (Term.Var _ | Term.Const _) -> (
      match Term.beta_reduce abs exp with
      | Some comp -> optimize_computation state comp
      | None -> Term.letVal (exp, abs))
  | NotPresent, _ -> cmp
  | NotInlinable, _ -> Term.letVal (exp, abs)

and reduce_expression state expr = reduce_if_fuel reduce_expression' state expr

and reduce_expression' state expr =
  match expr.term with
  | Term.CastExp (exp, tcoer) -> cast_expression state exp tcoer
  | _ -> expr

and reduce_computation state comp =
  reduce_if_fuel reduce_computation' state comp

and reduce_constant_match state const (abs : Term.abstraction list) =
  let rec folder : Term.abstraction list -> Term.computation option = function
    | [] -> None
    | abs :: xs -> (
        match Term.beta_reduce abs const with
        | Some cmp -> Some (optimize_computation state cmp)
        | None -> folder xs)
  in
  folder abs

and reduce_computation' state comp =
  match comp.term with
  (* TODO: matches of a constant *)
  | Term.CastComp (cmp, dtcoer) -> cast_computation state cmp dtcoer
  | Term.LetVal (e, abs) -> beta_reduce state abs e
  | Term.Apply ({ term = Term.Lambda a; _ }, e) -> beta_reduce state a e
  | Term.Apply
      ( {
          term =
            Term.CastExp
              (exp, { term = Constraint.ArrowCoercion (ty_coer, drty_coer); _ });
          _;
        },
        e ) ->
      cast_computation state
        (optimize_computation state
           (Term.apply (exp, cast_expression state e ty_coer)))
        drty_coer
  | Term.LetRec (defs, c) -> (
      let state' =
        Assoc.fold_right
          (fun (v, abs) state -> add_function state v abs)
          defs state
      in
      let c' = optimize_computation state' c in
      match keep_used_bindings defs c' with
      | [] -> c'
      | defs' -> Term.letRec (Assoc.of_list defs', c'))
  | Term.Bind (cmp, abs) -> bind_computation state cmp abs
  | Term.Handle ({ term = Term.Handler hnd; ty = hnd_ty }, cmp) -> (
      Print.debug "Handling: %t :: %t;; :: %t ::: %t"
        (Term.print_expression' (Term.Handler hnd))
        (Type.print_ty hnd_ty)
        (Term.print_computation cmp)
        (Type.print_dirty cmp.ty);
      let fingerprint = hnd.term.effect_clauses.fingerprint in
      let drty_in, _ = hnd.ty in
      Print.debug "Drty_in: %t" (Type.print_dirty drty_in);
      let unspecialized_declared_functions =
        List.filter
          (fun (f, { ty = _, drty_out; _ }) ->
            Print.debug "Drty_out: %t :~: %t"
              (Language.CoreTypes.Variable.print f)
              (Type.print_dirty drty_out);
            Type.equal_dirty drty_in drty_out
            && Option.is_none
                 (Assoc.lookup (fingerprint, f) state.specialized_functions))
          (Assoc.to_list state.declared_functions)
      in
      let attempt_specialization ret_clause_kinds =
        let add_specialized specialized (f, abs) =
          let f' = Language.CoreTypes.Variable.refresh f in
          let ret_clause_kind =
            match Assoc.lookup f ret_clause_kinds with
            | Some ret_clause_kind -> ret_clause_kind
            | None -> assert false
          in
          let (ty_arg, _), ((ty_in, _), drty_out) = (abs.ty, hnd.ty) in
          let ty' =
            match ret_clause_kind with
            | FixedReturnClause _ -> Type.Arrow (ty_arg, drty_out)
            | VaryingReturnClause ->
                Type.Arrow
                  (Type.Tuple [ ty_arg; Type.Arrow (ty_in, drty_out) ], drty_out)
          in

          Assoc.update (fingerprint, f)
            (Term.variable f' ty', ret_clause_kind)
            specialized
        in
        let specialized_functions' =
          List.fold_left add_specialized state.specialized_functions
            unspecialized_declared_functions
        in
        let state' =
          { state with specialized_functions = specialized_functions' }
        in
        (* TODO: specialize only functions that are used, not just all with matching types *)
        let spec_rec_defs =
          List.map
            (fun (f, ({ term = pat, cmp; _ } as abs)) ->
              match Assoc.lookup (fingerprint, f) specialized_functions' with
              | Some (f', FixedReturnClause _) ->
                  (f', handle_abstraction state' hnd abs)
              | Some (f', VaryingReturnClause) -> (
                  match f'.ty with
                  | Type.Arrow
                      (Type.Tuple [ _; (Type.Arrow (ty_in, _) as ty_cont) ], _)
                    ->
                      let x_pat, x_var = Term.fresh_variable "x" ty_in
                      and k_pat, k_var = Term.fresh_variable "k" ty_cont in
                      let hnd' =
                        {
                          hnd with
                          term =
                            {
                              hnd.term with
                              Term.value_clause =
                                Term.abstraction
                                  (x_pat, Term.apply (k_var, x_var));
                            };
                        }
                      in
                      let abs' =
                        Term.abstraction (Term.pTuple [ pat; k_pat ], cmp)
                      in
                      (f', handle_abstraction state' hnd' abs')
                  | _ -> assert false)
              | _ -> assert false)
            unspecialized_declared_functions
        in
        (state', spec_rec_defs)
      in
      let rec find_best_specializations ret_clause_kinds =
        try attempt_specialization ret_clause_kinds
        with ReturnClauseNotFixed f ->
          let ret_clause_kinds' =
            Assoc.update f VaryingReturnClause ret_clause_kinds
          in
          find_best_specializations ret_clause_kinds'
      in

      let state', spec_rec_defs =
        find_best_specializations
          (Assoc.map_of_list
             (fun (f, _) -> (f, FixedReturnClause hnd.term.value_clause))
             unspecialized_declared_functions)
      in
      Print.debug "Len: %d" (List.length spec_rec_defs);
      let cmp' = handle_computation state' hnd cmp in
      match keep_used_bindings (Assoc.of_list spec_rec_defs) cmp' with
      | [] -> cmp'
      | defs' ->
          Term.letRec (Assoc.of_list defs', cmp') |> optimize_computation state'
      )
  | Term.Handle
      ( {
          term =
            Term.CastExp
              ( exp,
                {
                  term = Constraint.HandlerCoercion (drty_coer1, drty_coer2);
                  _;
                } );
          _;
        },
        cmp ) ->
      cast_computation state
        (optimize_computation state
           (Term.handle (exp, cast_computation state cmp drty_coer1)))
        drty_coer2
  | Term.Match (({ term = Term.Const _; _ } as c), abs)
  | Term.Match (({ term = Term.Variant _; _ } as c), abs) -> (
      match reduce_constant_match state c abs with Some t -> t | None -> comp)
  | _ -> comp

let process_computation state comp =
  if !Config.enable_optimization then optimize_computation state comp else comp

let process_top_let state defs =
  if !Config.enable_optimization then
    let defs' = Assoc.map (optimize_expression state) defs in
    let state' =
      Assoc.fold_left
        (fun state (f, e) ->
          match e.term with
          | Term.Lambda abs -> add_function state f abs
          | _ -> state)
        state defs'
    in
    (state', defs')
  else (state, defs)

let process_top_let_rec state defs =
  if !Config.enable_optimization then
    let defs' = optimize_rec_definitions state defs in
    let state' =
      Assoc.fold_left
        (fun state (f, abs) -> add_function state f abs)
        state defs'
    in
    (state', defs')
  else (state, defs)
