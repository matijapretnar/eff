open Utils
open Language

type optimization_config = {
  specialize_functions : bool;
  eliminate_coercions : bool;
  push_coercions : bool;
  handler_reductions : bool;
  purity_aware_translation : bool;
}

type state = {
  fuel : int;
  config : optimization_config;
  rec_functions : (Term.variable, Term.abstraction) Assoc.t;
      (** The local recursive functions in scope, for With-Rec-Fun. Only groups
          with one definition: [let rec f x = M in N] is the paper's
          [let f = rec f x. M in N], and a group of several mutually recursive
          definitions has no counterpart in the paper. *)
  specialising : Term.variable list;
      (** The functions whose body With-Rec-Fun is rewriting under a handler.
          Inside, they are not specialised again, which is how the paper's
          Termination paragraph stops specialisation from diverging. *)
}

let initial_state config =
  {
    fuel = !Config.optimization_fuel;
    config;
    rec_functions = Assoc.empty;
    specialising = [];
  }

let add_rec_definitions state defs =
  match Assoc.to_list defs with
  | [ (f, abs) ] ->
      { state with rec_functions = Assoc.update f abs state.rec_functions }
  | _ -> state

let reduce_if_fuel reduce_term state term =
  if state.fuel > 0 then reduce_term { state with fuel = state.fuel - 1 } term
  else term

(* Optimization functions *)

(* Reductions and inlining *)

type inlinability =
  (* Pattern does not occur in in an abstraction body *)
  | NotPresent
  (* Pattern occurs, and occurs at most once in an abstraction and there is no recursion *)
  | Inlinable
  (* Pattern occurs more than once in a body of abstraction or it occurs recursively *)
  | NotInlinable

let abstraction_inlinability { term = pat, comp; _ } =
  match pat.term with
  | Term.PVar v
    when Term.Variable.fold
           (fun v _ -> String.length v >= 3 && String.sub v 0 3 = "___")
           v ->
      NotInlinable
  | _ ->
      let free_vars_comp = Term.free_vars_comp comp in
      let aux x _ inlinability =
        let occ =
          Term.Variable.Map.find_opt x free_vars_comp |> Option.value ~default:0
        in
        if occ > 1 then NotInlinable
        else
          match inlinability with
          | NotPresent -> if occ = 0 then NotPresent else Inlinable
          | inlinability -> inlinability
      in
      Term.Variable.Map.fold aux (Term.pattern_vars pat) NotPresent

let keep_used_bindings defs comp =
  (* Do proper call graph analysis *)
  let free_vars_comp = Term.free_vars_comp comp in
  let free_vars_defs =
    List.map (fun (_, a) -> Term.free_vars_abs a) (Assoc.to_list defs)
  in
  let free_vars = Term.concat_vars (free_vars_comp :: free_vars_defs) in
  List.filter
    (fun (x, _) -> not (Term.does_not_occur x free_vars))
    (Assoc.to_list defs)

(* [x ↦ ret x], possibly cast into a larger dirt, which elaboration gives as
   the finally clause of a handler that has none in the source *)
let is_identity_abstraction { term = pat, comp; ty = ty_in, (ty_out, _) } =
  let rec is_return_of x comp =
    match comp.term with
    | Term.Value { term = Term.Var v; _ } ->
        x = v.variable && Substitution.is_empty v.instantiation
    | Term.CastComp (comp, { term = tcoer, _; _ }) ->
        TyCoercion.is_trivial_ty_coercion tcoer && is_return_of x comp
    | _ -> false
  in
  Type.equal_ty ty_in ty_out
  && match pat.term with Term.PVar x -> is_return_of x comp | _ -> false

let rec extract_cast_value comp =
  match comp.term with
  | Term.Value expr -> Some expr
  | Term.CastComp (comp, { term = tcoer, _; _ }) ->
      Option.map
        (fun expr -> Term.castExp (expr, tcoer))
        (extract_cast_value comp)
  | _ -> None

let recast_computation hnd comp =
  match comp.ty with
  | ty, { Dirt.effect_set = effs; Dirt.row = Dirt.Row.Empty } ->
      let handled_effs =
        Effect.Set.of_list
          (List.map
             (fun (eff, _) -> eff.term)
             (Assoc.to_list hnd.term.Term.effect_clauses.effect_part))
      in
      if Effect.Set.disjoint effs handled_effs then
        let _, (_, drt_out) = hnd.ty in
        let drt_diff =
          {
            Dirt.effect_set = Effect.Set.diff drt_out.Dirt.effect_set effs;
            Dirt.row = drt_out.Dirt.row;
          }
        in
        let ty_coer = TyCoercion.reflTy ty
        and drt_coer =
          DirtCoercion.unionDirt (effs, DirtCoercion.empty drt_diff)
        in
        Some (Term.castComp (comp, TyCoercion.bangCoercion (ty_coer, drt_coer)))
      else None
  | _ -> None

(* Function specialisation, With-Rec-Fun

   For a handled call [with H handle f v] of a local recursive function
   [let rec f x = M], the rule makes a new recursive function [g'] whose body
   is [M] with the handler pushed in and rewritten. Recursive calls of [f] that
   end up under a handler with the same operation clauses are replaced by
   calls of [g'], which ties the knot. That replacement is the paper's
   [extract]. It has two modes:

   - [Fixed]: [g'] is specialised for all of [H], so it takes only [x]. It ties
     the knot only for calls under a handler with the same return clause, which
     is the case for tail calls.
   - [Varying]: [g'] is specialised for the operation clauses of [H] only, and
     takes the return clause as an extra argument [k]. It ties the knot also
     where With-Do has moved a continuation into the return clause, but [g']
     then carries [k] at run time.

   Both are correct, so choosing between them is strategy: we use [Fixed]
   unless it leaves a handled call of [f] that [Varying] would replace.

   The paper copies [rec f x. M] to the call site with Let-Val, and replaces
   calls that [extract] leaves by calls of a fresh copy [f']. We look [f] up in
   [state.rec_functions] instead, and leave such calls to [f] itself, which is
   still in scope. Both differ from the paper only in sharing, not in meaning.

   The paper defines [extract] on computations and copies values unchanged. We
   also enter values, because a handler clause that calls its continuation
   under a [fun], such as [Get] in a state handler, puts the recursive call
   inside a function body. Replacing [with H handle f w] by [g' w] is correct
   in any context where [g'] is in scope. *)

type specialisation_mode = Fixed | Varying

let extract mode hnd f g' ~left =
  let rec extract_comp comp =
    match comp.term with
    | Term.Handle
        ( { term = Term.Handler h'; _ },
          { term = Term.Apply ({ term = Term.Var { variable; _ }; _ }, w); _ }
        )
      when variable = f && Term.same_operation_clauses h' hnd -> (
        let g_arg_ty, g_out_ty =
          match g'.ty.term with
          | Type.Arrow (ty, drty) -> (ty, drty)
          | _ -> assert false
        in
        match mode with
        | Fixed
          when Term.same_return_clause h' hnd
               && Type.equal_ty w.ty g_arg_ty
               && Type.equal_dirty comp.ty g_out_ty ->
            Term.apply (g', w)
        | Varying ->
            let arg =
              Term.tuple [ Term.lambda (extract_abs h'.term.value_clause); w ]
            in
            if
              Type.equal_ty arg.ty g_arg_ty && Type.equal_dirty comp.ty g_out_ty
            then Term.apply (g', arg)
            else comp
        | Fixed ->
            left := true;
            comp)
    | Term.Value e -> { comp with term = Term.Value (extract_expr e) }
    | Term.LetVal (e, abs) -> Term.letVal (extract_expr e, extract_abs abs)
    | Term.LetRec (defs, c) ->
        Term.letRec (Assoc.map extract_abs defs, extract_comp c)
    | Term.Match (e, cases) ->
        Term.match_ (extract_expr e, List.map extract_abs cases) comp.ty
    | Term.Apply (e1, e2) -> Term.apply (extract_expr e1, extract_expr e2)
    | Term.Handle (e, c) -> Term.handle (extract_expr e, extract_comp c)
    | Term.Call (eff, e, abs) -> Term.call (eff, extract_expr e, extract_abs abs)
    | Term.Bind (c, abs) -> Term.bind (extract_comp c, extract_abs abs)
    | Term.CastComp (c, coer) -> Term.castComp (extract_comp c, coer)
    | Term.Check (loc, c) -> Term.check (loc, extract_comp c)
  and extract_expr expr =
    match expr.term with
    | Term.Var _ | Term.Const _ -> expr
    | Term.Tuple es -> Term.tuple (List.map extract_expr es)
    | Term.Record flds ->
        Term.record expr.ty (Type.Field.Map.map extract_expr flds)
    | Term.Variant (lbl, e) ->
        Term.variant (lbl, Option.map extract_expr e) expr.ty
    | Term.Lambda abs -> Term.lambda (extract_abs abs)
    | Term.Handler h -> Term.handler (extract_handler h)
    | Term.HandlerWithFinally { handler_clauses; finally_clause } ->
        Term.handlerWithFinally
          (extract_handler handler_clauses)
          (extract_abs finally_clause)
    | Term.CastExp (e, coer) -> Term.castExp (extract_expr e, coer)
  and extract_abs abs =
    let pat, comp = abs.term in
    Term.abstraction (pat, extract_comp comp)
  and extract_abs2 abs2 =
    let pat1, pat2, comp = abs2.term in
    Term.abstraction2 (pat1, pat2, extract_comp comp)
  and extract_handler h =
    {
      h with
      term =
        {
          Term.value_clause = extract_abs h.term.value_clause;
          Term.effect_clauses =
            {
              h.term.effect_clauses with
              effect_part =
                Assoc.map extract_abs2 h.term.effect_clauses.effect_part;
            };
        };
    }
  in
  extract_comp

let rec optimize_expression state expr =
  (* Print.debug "Optimizing expression: %t" (Term.print_expression expr); *)
  let expr' = optimize_expression' state expr in
  (* if expr <> expr' then
       Print.debug "Subterms optimized to: %t" (Term.print_expression expr')
     else Print.debug "No subterms optimized"; *)
  assert (Type.equal_ty expr.ty expr'.ty);
  let expr'' = reduce_expression state expr' in
  (* if expr' <> expr'' then
       Print.debug "Reduced to: %t" (Term.print_expression expr'')
     else Print.debug "No reductions"; *)
  assert (Type.equal_ty expr'.ty expr''.ty);
  (* Print.debug "Done optimizing expression: %t ~> %t"
     (Term.print_expression expr)
     (Term.print_expression expr''); *)
  expr''

and optimize_expression' state expr =
  match expr.term with
  | Term.Var _ | Term.Const _ -> expr
  | Term.Tuple exps -> Term.tuple (List.map (optimize_expression state) exps)
  | Term.Record flds ->
      Term.record expr.ty (Type.Field.Map.map (optimize_expression state) flds)
  | Term.Variant (lbl, arg) ->
      Term.variant (lbl, Option.map (optimize_expression state) arg) expr.ty
  | Term.Lambda abs -> Term.lambda (optimize_abstraction state abs)
  | Term.Handler hnd -> Term.handler (optimize_handler state hnd)
  | Term.HandlerWithFinally hnd ->
      Term.handlerWithFinally
        (optimize_handler state hnd.handler_clauses)
        (optimize_abstraction state hnd.finally_clause)
  | Term.CastExp (expr, coer) ->
      Term.castExp (optimize_expression state expr, coer)

and optimize_computation state comp =
  (* Print.debug "Optimizing computation: %t" (Term.print_computation comp); *)
  let comp' = optimize_computation' state comp in
  (* if comp <> comp' then
       Print.debug "Subterms optimized to: %t" (Term.print_computation comp')
     else Print.debug "No subterms optimized"; *)
  assert (Type.equal_dirty comp.ty comp'.ty);
  let comp'' = reduce_computation state comp' in
  (* if comp' <> comp'' then
       Print.debug "Reduced to: %t" (Term.print_computation comp'')
     else Print.debug "No reductions"; *)
  assert (Type.equal_dirty comp'.ty comp''.ty);
  (* Print.debug "Done optimizing computation: %t ~> %t"
     (Term.print_computation comp)
     (Term.print_computation comp''); *)
  comp''

and optimize_computation' state comp =
  match comp.term with
  | Term.Value expr -> Term.value (optimize_expression state expr)
  | Term.LetVal (expr, abs) ->
      Term.letVal
        (optimize_expression state expr, optimize_abstraction state abs)
  | Term.LetRec (defs, comp) ->
      let state' = add_rec_definitions state defs in
      let defs' = optimize_rec_definitions state' defs in
      Term.letRec
        (defs', optimize_computation (add_rec_definitions state defs') comp)
  | Term.Match (expr, cases) ->
      Term.match_
        ( optimize_expression state expr,
          List.map (optimize_abstraction state) cases )
        comp.ty
  | Term.Apply (expr1, expr2) ->
      Term.apply
        (optimize_expression state expr1, optimize_expression state expr2)
  | Term.Handle (expr, comp) ->
      Term.handle
        (optimize_expression state expr, optimize_computation state comp)
  | Term.Call (eff, expr, abs) ->
      Term.call
        (eff, optimize_expression state expr, optimize_abstraction state abs)
  | Term.Bind (comp, abs) ->
      Term.bind (optimize_computation state comp, optimize_abstraction state abs)
  | Term.CastComp (comp, dtcoer) ->
      Term.castComp (optimize_computation state comp, dtcoer)
  | Term.Check (loc, comp) -> Term.check (loc, optimize_computation state comp)

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

and optimize_abstraction' state (pat, comp) =
  let comp' = optimize_computation state comp in
  match (pat.term, comp'.term) with
  | Term.PVar v, Term.Match ({ term = Var v'; _ }, [ abs ])
  | Term.PVar v, Term.LetVal ({ term = Var v'; _ }, abs)
    when v = v'.variable && Term.does_not_occur v (Term.free_vars_abs abs) ->
      abs.term
  | _ -> (pat, comp')

and optimize_abstraction2 state abs2 =
  { abs2 with term = optimize_abstraction2' state abs2.term }

and optimize_abstraction2' state (pat1, pat2, comp) =
  (pat1, pat2, optimize_computation state comp)

and optimize_rec_definitions state defs =
  Assoc.map (fun abs -> optimize_abstraction state abs) defs

and cast_expression state expr coer =
  match (expr.term, coer.term) with
  | _, _
    when TyCoercion.is_trivial_ty_coercion coer
         && state.config.eliminate_coercions ->
      expr
  | _, _ -> Term.castExp (expr, coer)

and cast_computation state comp coer =
  match (comp.term, coer.term) with
  | _, _
    when TyCoercion.is_trivial_dirty_coercion coer
         && state.config.eliminate_coercions ->
      (* Elim-Co-Comp *)
      comp
  | Term.Bind (comp, abs), (_, dcoer) when state.config.push_coercions ->
      (* Push-Co-Do *)
      let ty1, _ = comp.ty in
      let coer1 = TyCoercion.bangCoercion (TyCoercion.reflTy ty1, dcoer) in
      bind_computation state
        (cast_computation state comp coer1)
        (cast_abstraction state abs coer)
  | Term.Call (eff, expr, abs), _ when state.config.push_coercions ->
      (* Push-Co-Op *)
      Term.call (eff, expr, cast_abstraction state abs coer)
  | _, _ -> Term.castComp (comp, coer)

and cast_abstraction state { term = pat, comp; _ } coer =
  Term.abstraction (pat, cast_computation state comp coer)

and bind_computation state comp bind =
  match comp.term with
  | Term.Bind (comp, abs) ->
      bind_computation state comp (bind_abstraction state abs bind)
  | Term.Call (eff, expr, abs) ->
      Term.call (eff, expr, bind_abstraction state abs bind)
  | Term.LetRec (defs, comp)
    when List.for_all
           (fun (f, _) -> Term.does_not_occur f (Term.free_vars_abs bind))
           (Assoc.to_list defs) ->
      (* Do-Rec-Fun *)
      Term.letRec (defs, bind_computation state comp bind)
  | _ -> (
      match extract_cast_value comp with
      | Some expr -> beta_reduce state bind expr
      | None -> Term.bind (comp, bind))

and bind_abstraction state { term = pat, comp; _ } bind =
  Term.abstraction (pat, bind_computation state comp bind)

and handle_computation state hnd comp =
  match comp.term with
  | Term.Apply ({ term = Term.Var { variable = f; instantiation; _ }; _ }, v)
    when state.config.specialize_functions
         && (not (List.mem f state.specialising))
         && Assoc.lookup f state.rec_functions <> None
         && Type.equal_dirty comp.ty (fst hnd.ty) -> (
      match Assoc.lookup f state.rec_functions with
      | Some abs ->
          with_rec_fun state hnd f (Term.apply_sub_abs instantiation abs) v
      | None -> assert false)
  | _ when not state.config.handler_reductions ->
      Term.handle (Term.handler hnd, comp)
  | Term.Match (expr, cases) ->
      let _, drty_out = hnd.ty in
      Term.match_ (expr, List.map (handle_abstraction state hnd) cases) drty_out
      |> optimize_computation state
  | LetVal (expr, abs) ->
      Term.letVal (expr, handle_abstraction state hnd abs)
      |> optimize_computation state
  | LetRec (defs, comp) ->
      Term.letRec
        (defs, handle_computation (add_rec_definitions state defs) hnd comp)
      |> optimize_computation state
  | Call (eff, expr, abs) -> (
      let handled_abs = handle_abstraction state hnd abs in
      match Assoc.lookup eff hnd.term.Term.effect_clauses.effect_part with
      | Some { term = p1, p2, comp; _ } ->
          let comp' =
            beta_reduce state
              (Term.abstraction (p2, comp))
              (Term.lambda handled_abs)
          in
          beta_reduce state (Term.abstraction (p1, comp')) expr
      | None -> Term.call (eff, expr, handled_abs))
  | Bind (comp, abs) ->
      let hnd' =
        Term.handler_with_new_value_clause hnd
          (handle_abstraction state hnd abs)
      in
      handle_computation state hnd' comp
  | CastComp (comp, { term = tcoer, dcoer; _ })
    when TyCoercion.is_trivial_ty_coercion tcoer ->
      let hnd' = Term.handler_with_smaller_input_dirt hnd dcoer in
      handle_computation state hnd' comp
  | CastComp (comp, { term = tcoer, dcoer; _ }) ->
      let ty, _ = comp.ty in
      let x_pat, x_var = Term.fresh_variable "x" ty in
      let hnd' =
        Term.handler_with_new_value_clause hnd
          (Term.abstraction
             ( x_pat,
               Term.letVal
                 (cast_expression state x_var tcoer, hnd.term.value_clause) ))
      in
      let hnd'' = Term.handler_with_smaller_input_dirt hnd' dcoer in
      handle_computation state hnd'' comp
  | _ -> (
      match recast_computation hnd comp with
      | Some comp' -> bind_computation state comp' hnd.term.Term.value_clause
      | None -> Term.handle (Term.handler hnd, comp))

and handle_abstraction state hnd { term = p, c; _ } =
  Term.abstraction (p, handle_computation state hnd c)

(* With-Rec-Fun; see the comment at [extract] *)
and with_rec_fun state hnd f abs v =
  let { term = pat, body; ty = ty_arg, _ } =
    Term.refresh_abstraction Assoc.empty abs
  in
  let (ty_in, _), drty_out = hnd.ty in
  let state' = { state with specialising = f :: state.specialising } in
  let attempt mode =
    let g_arg_ty, hnd_m, g_pat, g_arg =
      match mode with
      | Fixed -> (ty_arg, hnd, pat, v)
      | Varying ->
          let k_ty = Type.arrow (ty_in, drty_out) in
          let k_pat, k_var = Term.fresh_variable "k" k_ty in
          let y_pat, y_var = Term.fresh_variable "y" ty_in in
          let hnd_k =
            Term.handler_with_new_value_clause hnd
              (Term.abstraction (y_pat, Term.apply (k_var, y_var)))
          in
          ( Type.tuple [ k_ty; ty_arg ],
            hnd_k,
            Term.pTuple [ k_pat; pat ],
            Term.tuple [ Term.lambda hnd.term.value_clause; v ] )
    in
    let g = Term.Variable.refresh f in
    let g_var = Term.mono_var g (Type.arrow (g_arg_ty, drty_out)) in
    let left = ref false in
    let body' =
      extract mode hnd f g_var ~left (handle_computation state' hnd_m body)
    in
    let comp =
      Term.letRec
        ( Assoc.of_list [ (g, Term.abstraction (g_pat, body')) ],
          Term.apply (g_var, g_arg) )
    in
    (comp, !left)
  in
  let comp =
    match attempt Fixed with
    | comp, false -> comp
    | _, true -> fst (attempt Varying)
  in
  (* Still with [f] in [specialising]: calls of [f] that [extract] has left
     are not specialised again. *)
  optimize_computation state' comp

and beta_reduce state ({ term = _, comp; _ } as abs) expr =
  (* Print.debug "Beta reduce: %t; %t"
     (Term.print_abstraction abs)
     (Term.print_expression expr); *)
  match (abstraction_inlinability abs, expr.term) with
  | Inlinable, _
  (* Inline constants and variables anyway *)
  | NotInlinable, (Term.Var _ | Term.Const _) -> (
      match Term.beta_reduce abs expr with
      | Some comp -> optimize_computation state comp
      | None -> Term.letVal (expr, abs))
  | NotPresent, _ -> comp
  | NotInlinable, _ -> Term.letVal (expr, abs)

and reduce_expression state expr = reduce_if_fuel reduce_expression' state expr

and reduce_expression' state expr =
  match expr.term with
  | Term.CastExp (expr, tcoer) -> cast_expression state expr tcoer
  | _ -> expr

and reduce_computation state comp =
  reduce_if_fuel reduce_computation' state comp

and reduce_constant_match state const (abs : Term.abstraction list) =
  let rec folder : Term.abstraction list -> Term.computation option = function
    | [] -> None
    | abs :: xs -> (
        match Term.beta_reduce abs const with
        | Some comp -> Some (optimize_computation state comp)
        | None -> folder xs)
  in
  folder abs

and reduce_computation' state comp =
  match comp.term with
  (* TODO: matches of a constant *)
  | Term.CastComp (comp, dtcoer) -> cast_computation state comp dtcoer
  | Term.LetVal (e, abs) -> beta_reduce state abs e
  | Term.Apply ({ term = Term.Lambda a; _ }, e) -> beta_reduce state a e
  | Term.Apply
      ( {
          term =
            Term.CastExp
              (expr, { term = TyCoercion.ArrowCoercion (ty_coer, drty_coer); _ });
          _;
        },
        e )
    when state.config.push_coercions ->
      (* Push-Co-App *)
      cast_computation state
        (optimize_computation state
           (Term.apply (expr, cast_expression state e ty_coer)))
        drty_coer
  | Term.LetRec (defs, c) -> (
      let c' = optimize_computation state c in
      match keep_used_bindings defs c' with
      | [] -> c'
      | defs' -> Term.letRec (Assoc.of_list defs', c'))
  | Term.Bind (comp, abs) -> bind_computation state comp abs
  | Term.Handle ({ term = Term.Handler hnd; _ }, comp) ->
      handle_computation state hnd comp
  | Term.Handle
      ( { term = Term.HandlerWithFinally { handler_clauses; finally_clause }; _ },
        comp ) ->
      (* The paper's handlers have no finally clause, and
         [with {H; finally f} handle M] means [do x <- with H handle M in f x],
         so we expand it before the handler rules apply. *)
      let comp' = handle_computation state handler_clauses comp in
      if is_identity_abstraction finally_clause then comp'
      else bind_computation state comp' finally_clause
  | Term.Handle
      ( {
          term =
            Term.CastExp
              ( expr,
                {
                  term = TyCoercion.HandlerCoercion (drty_coer1, drty_coer2);
                  _;
                } );
          _;
        },
        comp )
    when state.config.push_coercions ->
      (* Push-Co-Handle *)
      cast_computation state
        (optimize_computation state
           (Term.handle (expr, cast_computation state comp drty_coer1)))
        drty_coer2
  | Term.Match (expr, [ abs ]) -> beta_reduce state abs expr
  | Term.Match (({ term = Term.Const _; _ } as c), abs)
  | Term.Match (({ term = Term.Variant _; _ } as c), abs) -> (
      match reduce_constant_match state c abs with Some t -> t | None -> comp)
  | _ -> comp

let process_computation state ((params, comp, constraints) as top_comp) =
  if !Config.enable_optimization then
    (params, optimize_computation state comp, constraints)
  else top_comp

let process_top_let state defs =
  if !Config.enable_optimization then
    let defs' =
      List.map
        (fun (pat, params, cnstrs, comp) ->
          (pat, params, cnstrs, optimize_computation state comp))
        defs
    in
    (state, defs')
  else (state, defs)

let optimize_top_rec_definitions state defs =
  Assoc.map
    (fun (params, cnstrs, abs) ->
      (params, cnstrs, optimize_abstraction state abs))
    defs

let process_top_let_rec state defs =
  if !Config.enable_optimization then
    let defs' = optimize_top_rec_definitions state defs in
    (state, defs')
  else (state, defs)
