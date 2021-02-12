open Utils

type recursive = TailRecursive | Recursive | NonRecursive

type state = {
  declared_functions :
    (Language.CoreTypes.Variable.t, Term.abstraction * recursive) Assoc.t;
  fuel : int;
  (* Cache of already specialized functions *)
  specialized_functions :
    ( Term.EffectFingerprint.t * Language.CoreTypes.Variable.t,
      Term.variable * recursive )
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

let add_recursive_function state x abs =
  let recursive =
    Language.CoreTypes.Variable.fold
      (fun x _ ->
        if String.length x > 2 && String.sub x 0 2 = "tr" then TailRecursive
        else Recursive)
      x.term
  in
  {
    state with
    declared_functions =
      Assoc.update x.term (abs, recursive) state.declared_functions;
  }

let add_non_recursive_function state x abs =
  {
    state with
    declared_functions =
      Assoc.update x (abs, NonRecursive) state.declared_functions;
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
  let free_vars_cmp = Term.free_vars_comp cmp in
  let rec check_variables = function
    | [] -> NotPresent
    | x :: xs -> (
        let occ =
          Term.VariableMap.find_opt x free_vars_cmp |> Option.value ~default:0
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
    (fun (x, _) ->
      match Term.VariableMap.find_opt x.term free_vars with
      | None | Some 0 -> false
      | Some _ -> true)
    (Assoc.to_list defs)

let rec extract_cast_value comp =
  match comp.term with
  | Term.Value exp -> Some exp
  | Term.CastComp (comp, { term = tcoer, _; _ }) ->
      Option.map
        (fun exp -> Term.castExp (exp, tcoer))
        (extract_cast_value comp)
  | _ -> None

let rec recast_computation hnd comp =
  match (comp.term, comp.ty) with
  | Term.CastComp (comp, { term = tcoer, _; _ }), _ ->
      Option.map
        (fun comp ->
          let _, drt = comp.ty in
          Term.castComp
            (comp, Constraint.bangCoercion (tcoer, Constraint.reflDirt drt)))
        (recast_computation hnd comp)
  | _, (ty, { Type.effect_set = effs; Type.row = EmptyRow }) ->
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
            Type.effect_set = Type.EffectSet.diff effs drt_out.Type.effect_set;
            Type.row = drt_out.Type.row;
          }
        in
        let ty_coer = Constraint.reflTy ty
        and drt_coer = Constraint.empty drt_diff in
        Some (Term.castComp (comp, Constraint.bangCoercion (ty_coer, drt_coer)))
      else None
  | _, _ -> None

let rec optimize_ty_coercion state (tcoer : Constraint.ty_coercion) =
  reduce_ty_coercion state
    { tcoer with term = optimize_ty_coercion' state tcoer.term }

and optimize_ty_coercion' state tcoer =
  match tcoer with
  | ReflTy -> tcoer
  | ArrowCoercion (tc, dc) ->
      ArrowCoercion
        (optimize_ty_coercion state tc, optimize_dirty_coercion state dc)
  | HandlerCoercion (dc1, dc2) ->
      HandlerCoercion
        (optimize_dirty_coercion state dc1, optimize_dirty_coercion state dc2)
  | TyCoercionVar _ -> tcoer
  | ApplyCoercion (v, lst) ->
      ApplyCoercion (v, List.map (optimize_ty_coercion state) lst)
  | TupleCoercion lst ->
      TupleCoercion (List.map (optimize_ty_coercion state) lst)

and optimize_dirt_coercion state (dcoer : Constraint.dirt_coercion) =
  reduce_dirt_coercion state
    { dcoer with term = optimize_dirt_coercion' state dcoer.term }

and optimize_dirt_coercion' state (dcoer : Constraint.dirt_coercion') =
  match dcoer with
  | ReflDirt | DirtCoercionVar _ | Empty -> dcoer
  | UnionDirt (s, dc) -> UnionDirt (s, optimize_dirt_coercion state dc)

and optimize_dirty_coercion state { term = tcoer, dcoer; _ } =
  Constraint.bangCoercion
    (optimize_ty_coercion state tcoer, optimize_dirt_coercion state dcoer)

and reduce_ty_coercion state ty_coer =
  { ty_coer with term = reduce_ty_coercion' state ty_coer.term }

and reduce_ty_coercion' _state = function
  (* TODO: Is it sufficient to just check if the input and output types match? *)
  | ArrowCoercion
      ( { term = ReflTy; _ },
        { term = { term = ReflTy; _ }, { term = ReflDirt; _ }; _ } ) ->
      ReflTy
  | tcoer -> tcoer

and reduce_dirt_coercion state drt_coer =
  { drt_coer with term = reduce_dirt_coercion' state drt_coer }

and reduce_dirt_coercion' _state drt_coer =
  match drt_coer.term with
  | Empty when Type.is_empty_dirt (snd drt_coer.ty) -> ReflDirt
  | UnionDirt (_, { term = ReflDirt; _ }) -> ReflDirt
  | dcoer -> dcoer

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
      Term.castExp
        (optimize_expression state exp, optimize_ty_coercion state coer)

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
      Term.castComp
        (optimize_computation state cmp, optimize_dirty_coercion state dtcoer)

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
  (pat, optimize_computation state cmp)

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
      match
        Assoc.lookup
          (hnd.term.Term.effect_clauses.fingerprint, f.term)
          state.specialized_functions
      with
      | Some (f', Recursive) ->
          Term.apply
            ( Term.var f',
              Term.tuple [ exp; Term.lambda hnd.term.Term.value_clause ] )
      | Some (f', NonRecursive) -> Term.apply (Term.var f', exp)
      | Some (f', TailRecursive) -> Term.apply (Term.var f', exp)
      | None -> assert false)
  | Bind (cmp, abs) -> (
      match recast_computation hnd cmp with
      | Some comp' ->
          bind_computation state comp' (handle_abstraction state hnd abs)
      | None ->
          let hnd' =
            Term.handler_with_new_value_clause hnd
              (handle_abstraction state hnd abs)
          in
          handle_computation state hnd' cmp)
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
          (fun (v, abs) state -> add_recursive_function state v abs)
          defs state
      in
      let c' = optimize_computation state' c in
      match keep_used_bindings defs c' with
      | [] -> c'
      | defs' -> Term.letRec (Assoc.of_list defs', c'))
  | Term.Bind (cmp, abs) -> bind_computation state cmp abs
  | Term.Handle ({ term = Term.Handler hnd; _ }, cmp) -> (
      let fingerprint = hnd.term.effect_clauses.fingerprint in
      let drty_in, _ = hnd.ty in
      let unspecialized_declared_functions =
        List.filter
          (fun (f, ({ ty = _, drty_out; _ }, _)) ->
            Type.equal_dirty drty_in drty_out
            && Option.is_none
                 (Assoc.lookup (fingerprint, f) state.specialized_functions))
          (Assoc.to_list state.declared_functions)
      in
      let add_specialized specialized (f, (abs, spec)) =
        let f' = Language.CoreTypes.Variable.refresh f in
        let (ty_arg, _), ((ty_in, _), drty_out) = (abs.ty, hnd.ty) in
        let ty' =
          match spec with
          | Recursive ->
              Type.Arrow
                (Type.Tuple [ ty_arg; Type.Arrow (ty_in, drty_out) ], drty_out)
          | NonRecursive -> Type.Arrow (ty_arg, drty_out)
          | TailRecursive -> Type.Arrow (ty_arg, drty_out)
        in
        Assoc.update (fingerprint, f) (Term.variable f' ty', spec) specialized
      in
      let specialized_functions' =
        List.fold_left add_specialized state.specialized_functions
          unspecialized_declared_functions
      in
      let state' =
        { state with specialized_functions = specialized_functions' }
      in
      let cmp' = handle_computation state' hnd cmp in
      (* TODO: specialize only functions that are used, not just all with matching types *)
      let spec_rec_defs =
        List.map
          (fun (f, (({ term = pat, cmp; _ } as abs), _)) ->
            match Assoc.lookup (fingerprint, f) specialized_functions' with
            | Some (f', Recursive) -> (
                match f'.ty with
                | Type.Arrow
                    (Type.Tuple [ _; (Type.Arrow (ty_in, _) as ty_cont) ], _) ->
                    let x_pat, x_var = Term.fresh_variable "x" ty_in
                    and k_pat, k_var = Term.fresh_variable "k" ty_cont in
                    let hnd' =
                      {
                        hnd with
                        term =
                          {
                            hnd.term with
                            Term.value_clause =
                              Term.abstraction (x_pat, Term.apply (k_var, x_var));
                          };
                      }
                    in
                    let abs' =
                      Term.abstraction (Term.pTuple [ pat; k_pat ], cmp)
                    in
                    (f', handle_abstraction state' hnd' abs')
                | _ -> assert false)
            | Some (f', NonRecursive) -> (f', handle_abstraction state' hnd abs)
            | Some (f', TailRecursive) -> (f', handle_abstraction state' hnd abs)
            | _ -> assert false)
          unspecialized_declared_functions
      in
      match keep_used_bindings (Assoc.of_list spec_rec_defs) cmp' with
      | [] -> cmp'
      | defs' -> Term.letRec (Assoc.of_list defs', cmp'))
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
  | _ -> comp

let process_computation state comp =
  if !Config.enable_optimization then optimize_computation state comp else comp

let process_top_let_rec state defs =
  if !Config.enable_optimization then
    let defs' = optimize_rec_definitions state defs in
    let state' =
      Assoc.fold_left
        (fun state (f, abs) -> add_recursive_function state f abs)
        state defs'
    in
    (state', defs')
  else (state, defs)
