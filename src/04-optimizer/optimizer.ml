open Utils
open Language

type optimization_config = {
  specialize_functions : bool;
  eliminate_coercions : bool;
  push_coercions : bool;
  handler_reductions : bool;
  purity_aware_translation : bool;
}

(* A top-level definition, as the paper's Inline-Top sees it. A [let rec] with
   one definition is the paper's [let f = rec f x. M]. Each member of a group
   of several is recorded on its own: the other members are top-level names
   in its body. The paper has no mutual recursion. *)
type top_definition = TopValue of Term.expression | TopRec of Term.abstraction
type specialisation_mode = Fixed | Varying

(* A specialisation of a top-level recursive function under a handler, made
   by With-Rec-Fun and kept so that it is made only once. If it mentions only
   top-level names, it becomes a new top-level definition, emitted before the
   first top-level definition that uses it. *)
type cached_specialisation = {
  original : Term.variable;
  instantiation : Substitution.t;
  mode : specialisation_mode;
  handler : Term.handler_clauses;
      (** In [Varying] mode, only its operation clauses are compared. *)
  result : specialisation_result;
}

and specialisation_result =
  | Building of { name_var : Term.expression; mutable left : int }
      (** Being built. A handled call of [original] inside it, possibly in the
          body of another top-level function, goes to [name_var], which ties the
          knot through mutually recursive top-level functions. In [Fixed] mode,
          [left] counts the handled calls that could not go there. *)
  | Built of {
      name : Term.variable;
      name_var : Term.expression;
      definition : Term.abstraction;
      group : Term.Variable.Set.t;
          (** The names of the specialisations made together with it, which are
              emitted together as one recursive definition *)
      mutable emitted : bool;
    }
  | FixedFails
      (** The [Fixed] mode leaves a handled call, so [Varying] is used. *)

(* The specialisation of a group of top-level recursive functions under one
   handler, being built. A handled call of another member under the same
   operation clauses joins it: the member gets an entry that is being built,
   so that all its calls go there, and its body is built after the current
   one, in [pending]. *)
type group_build = {
  members : Term.Variable.Set.t;
  group_handler : Term.handler_clauses;
  group_mode : specialisation_mode;
  group_instantiation : Substitution.t;
  root : cached_specialisation;
  pending :
    (Term.variable * Term.abstraction * Term.variable * Term.expression) Queue.t;
}

type state = {
  fuel : int;
  config : optimization_config;
  rec_functions : (Term.variable, Term.abstraction) Assoc.t;
      (** The local recursive functions in scope, for With-Rec-Fun. Only groups
          with one definition: [let rec f x = M in N] is the paper's
          [let f = rec f x. M in N], and a group of several mutually recursive
          definitions has no counterpart in the paper. *)
  specialising : (Term.variable * Term.effect_fingerprint) list;
      (** The functions whose body With-Rec-Fun is rewriting under a handler, as
          the source function and the fingerprint of the handler. Inside, a
          function is not specialised again under a handler with the same
          fingerprint, which comes from the same source handler. Under other
          handlers it is. There are finitely many source functions and
          fingerprints, so specialisations nest only finitely deep. The paper's
          Termination paragraph does not specialise a specialised function at
          all. *)
  origins : Term.variable Term.Variable.Map.t ref;
      (** The source function of each specialisation *)
  top_definitions : (Term.variable, top_definition) Assoc.t;
      (** The top-level definitions before the current one: the paper's [D],
          which only Inline-Top reads. *)
  top_names : Term.Variable.Set.t ref;
      (** All top-level names, including primitives and the names of shared
          specialisations. A term whose free variables are among them can be a
          top-level definition. Mutable, because specialisations made deep
          inside a term must be visible after it. *)
  specialisations : cached_specialisation list ref;
      (** The cache of specialisations, newest first *)
  groups : Term.Variable.Set.t Term.Variable.Map.t ref;
      (** The members of the recursive group of each top-level function,
          including the groups of shared specialisations *)
  building_group : group_build option;
}

let initial_state config =
  {
    fuel = !Config.optimization_fuel;
    config;
    rec_functions = Assoc.empty;
    specialising = [];
    origins = ref Term.Variable.Map.empty;
    top_definitions = Assoc.empty;
    top_names = ref Term.Variable.Set.empty;
    specialisations = ref [];
    groups = ref Term.Variable.Map.empty;
    building_group = None;
  }

let add_top_name state x =
  state.top_names := Term.Variable.Set.add x !(state.top_names)

let load_primitive_value state x =
  add_top_name state x;
  state

(* The single definition of a [let rec] that does not mention itself, which
   is just a function *)
let non_recursive defs =
  match Assoc.to_list defs with
  | [ (f, abs) ] when Term.does_not_occur f (Term.free_vars_abs abs) ->
      Some (f, abs)
  | _ -> None

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

(* The definitions of a [let rec] that its body [comp] calls, directly or
   through each other. A definition that only calls itself is not used. *)
let keep_used_bindings defs comp =
  let defs = Assoc.to_list defs in
  let rec reach used fvs =
    let used' =
      List.filter
        (fun (x, _) -> List.mem x used || not (Term.does_not_occur x fvs))
        defs
      |> List.map fst
    in
    if List.length used' = List.length used then used
    else
      reach used'
        (Term.concat_vars
           (fvs
           :: List.filter_map
                (fun (x, abs) ->
                  if List.mem x used' && not (List.mem x used) then
                    Some (Term.free_vars_abs abs)
                  else None)
                defs))
  in
  let used = reach [] (Term.free_vars_comp comp) in
  List.filter (fun (x, _) -> List.mem x used) defs

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

(* Inline-Top, applied only on demand: where a rule applies right after it.
   The paper's rule replaces [x η] by the innermost value of [x]'s
   definition, instantiated at [η]. *)
let inline_top_value state (x : Term.variable) instantiation =
  match Assoc.lookup x state.top_definitions with
  | Some (TopValue e) ->
      Some
        (Term.refresh_expression Assoc.empty
           (Term.apply_sub_exp instantiation e))
  | _ -> None

(* Inline-Top for an application [x η v] of a non-recursive [x], followed by
   β. A recursive [x] goes to With-Rec-Fun directly; see [with_rec_fun]. *)
let expand_top_application state (x : Term.variable) instantiation v =
  Option.map
    (fun e -> Term.apply (e, v))
    (inline_top_value state x instantiation)

let rec is_handler_value (e : Term.expression) =
  match e.term with
  | Term.Handler _ | Term.HandlerWithFinally _ -> true
  | Term.CastExp (e, _) -> is_handler_value e
  | Term.Tuple es -> List.exists is_handler_value es
  | _ -> false

(* With-Rec-Fun needs a handler with operation clauses. Under one without,
   which With-Cast leaves when it drops them all, the specialisation would
   only unfold the function once, and With-Fwd gives the same sequence
   directly. *)
let handles_operations (hnd : Term.handler_clauses) =
  not (Assoc.is_empty hnd.term.effect_clauses.effect_part)

let rec strip_casts_comp comp =
  match comp.term with Term.CastComp (c, _) -> strip_casts_comp c | _ -> comp

let rec strip_casts_expr expr =
  match expr.term with Term.CastExp (e, _) -> strip_casts_expr e | _ -> expr

(* [fun b -> b v], possibly with casts, where [v] does not mention [b] *)
let is_application_abs (abs : Term.abstraction) =
  let pat, comp = abs.term in
  match (pat.term, (strip_casts_comp comp).term) with
  | Term.PVar b, Term.Apply (e, v) -> (
      match (strip_casts_expr e).term with
      | Term.Var { variable; _ } ->
          variable = b && Term.does_not_occur b (Term.free_vars_expr v)
      | _ -> false)
  | _ -> false

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
     then carries [k] at run time. [g'] takes [k] after [x], curried, so that
     with a return clause that gives a function, as in a state handler, the
     generated OCaml function takes all its arguments at once.

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

(* A full call [f v1 ... vn] of a curried function. It is [f v1], or
   [do b <- c in b' vn] where [c] is a call [f v1 ... vn-1] and [b'] is [b],
   possibly with casts; the calls before the last are pure, so they are cast to
   the dirt of the sequence. It gives [f] and the arguments. *)
let rec curried_call comp =
  match comp.term with
  | Term.Apply (({ term = Term.Var _; _ } as f), v) -> Some (f, [ v ])
  | Term.Bind (c1, { term = { term = Term.PVar b; _ }, c2; _ }) -> (
      match (curried_call (strip_casts_comp c1), curried_call c2) with
      | Some (f, vs1), Some (h, vs2)
        when (match (strip_casts_expr h).term with
               | Term.Var { variable; _ } -> variable = b
               | _ -> false)
             && List.for_all
                  (fun v -> Term.does_not_occur b (Term.free_vars_expr v))
                  vs2 ->
          Some (f, vs1 @ vs2)
      | _ -> None)
  | _ -> None

(* The parameters of a curried function [rec f x1. ret λx2. ... ret λxn. M] and
   its body [M] *)
let rec curried_params (abs : Term.abstraction) =
  let pat, body = abs.term in
  match body.term with
  | Term.Value { term = Term.Lambda abs'; _ } ->
      let pats, body' = curried_params abs' in
      (pat :: pats, body')
  | _ -> ([ pat ], body)

(* [rec g p1. ret λp2. ... ret λpn. M] *)
let rec curried_abstraction pats body =
  match pats with
  | [ pat ] -> Term.abstraction (pat, body)
  | pat :: pats ->
      Term.abstraction
        (pat, Term.value (Term.lambda (curried_abstraction pats body)))
  | [] -> assert false

(* The type of a specialisation of a function with argument types [tys] under
   a handler of type [hnd_ty]. It is curried, and in [Varying] mode it also
   takes the return clause as its last argument. *)
let specialisation_ty mode hnd_ty tys =
  let (ty_in, _), drty_out = hnd_ty in
  let tys =
    match mode with
    | Fixed -> tys
    | Varying -> tys @ [ Type.arrow (ty_in, drty_out) ]
  in
  let rec curried = function
    | [ ty ] -> Type.arrow (ty, drty_out)
    | ty :: tys -> Type.arrow (ty, Type.pure_ty (curried tys))
    | [] -> assert false
  in
  curried tys

(* The call [g' a1 ... an] of a curried specialisation. The calls before the
   last are pure, so they get the dirt of the last before the sequence. *)
let curried_apply g' args =
  let rec result_dirt ty = function
    | [ _ ] -> (
        match (ty : Type.ty).term with
        | Type.Arrow (_, (_, drt)) -> drt
        | _ -> assert false)
    | _ :: args -> (
        match ty.term with
        | Type.Arrow (_, (ty', _)) -> result_dirt ty' args
        | _ -> assert false)
    | [] -> assert false
  in
  let drt = result_dirt g'.ty args in
  let rec go comp = function
    | [] -> comp
    | arg :: args ->
        let ty_h, _ = comp.ty in
        let h_pat, h_var = Term.fresh_variable "h" ty_h in
        let coer =
          TyCoercion.bangCoercion
            (TyCoercion.reflTy ty_h, DirtCoercion.empty drt)
        in
        Term.bind
          ( Term.castComp (comp, coer),
            Term.abstraction (h_pat, go (Term.apply (h_var, arg)) args) )
  in
  match args with
  | arg :: args -> go (Term.apply (g', arg)) args
  | [] -> assert false

(* The call of a specialisation [g'] in [mode] with the arguments [vs] and, in
   [Varying] mode, the return clause [k] *)
let specialised_call mode g' vs k =
  match mode with
  | Fixed -> curried_apply g' vs
  | Varying -> curried_apply g' (vs @ [ k ])

let extract mode hnd f g' ~left =
  let call_of_f comp =
    match curried_call comp with
    | Some ({ term = Term.Var { variable; _ }; _ }, ws) when variable = f ->
        Some ws
    | _ -> None
  in
  let rec extract_comp comp =
    match comp.term with
    | Term.Handle ({ term = Term.Handler h'; _ }, c)
      when Term.same_operation_clauses h' hnd && call_of_f c <> None -> (
        let ws = Option.get (call_of_f c) in
        let fits mode =
          Type.equal_ty g'.ty
            (specialisation_ty mode h'.ty
               (List.map (fun (w : Term.expression) -> w.ty) ws))
        in
        match mode with
        | Fixed when Term.same_return_clause h' hnd && fits Fixed ->
            specialised_call Fixed g' ws g'
        | Varying ->
            if fits Varying then
              specialised_call Varying g' ws
                (Term.lambda (extract_abs h'.term.value_clause))
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

let origin state f =
  Term.Variable.Map.find_opt f !(state.origins) |> Option.value ~default:f

let may_specialise state f (hnd : Term.handler_clauses) =
  not
    (List.mem
       (origin state f, hnd.term.effect_clauses.fingerprint)
       state.specialising)

let specialising_under state f (hnd : Term.handler_clauses) =
  {
    state with
    specialising =
      (origin state f, hnd.term.effect_clauses.fingerprint)
      :: state.specialising;
  }

(* A top-level definition: a source one, or a shared specialisation, which
   Inline-Top sees like any other. *)
let top_definition state x =
  match Assoc.lookup x state.top_definitions with
  | Some def -> Some def
  | None ->
      List.find_map
        (fun entry ->
          match entry.result with
          | Built { name; definition; _ } when name = x ->
              Some (TopRec definition)
          | _ -> None)
        !(state.specialisations)

(* The newest specialisation of the top-level [x] at [instantiation] that is
   being built for a handler with the operation clauses of [hnd], if a handled
   call [with hnd handle x v1 ... vn] can go to it. A call that could go to a [Fixed]
   one only with another return clause marks it as [left] instead. *)
let building_specialisation state hnd x instantiation vs =
  let matching entry =
    entry.original = x
    && entry.instantiation = instantiation
    && Term.same_operation_clauses entry.handler hnd
    && match entry.result with Building _ -> true | _ -> false
  in
  match List.find_opt matching !(state.specialisations) with
  | Some { mode; result = Building b; handler; _ } -> (
      let tys = List.map (fun (v : Term.expression) -> v.ty) vs in
      let fits mode =
        Type.equal_ty b.name_var.ty (specialisation_ty mode hnd.ty tys)
      in
      match mode with
      | Fixed when Term.same_return_clause handler hnd ->
          if fits Fixed then Some (Fixed, b.name_var) else None
      | Fixed ->
          b.left <- b.left + 1;
          None
      | Varying -> if fits Varying then Some (Varying, b.name_var) else None)
  | _ -> None

(* A specialisation [rec g p. M] in a group with [names] is closed if [M]
   mentions only [names] and top-level names, and no type, dirt or skeleton
   parameters of the enclosing
   definition. Coercion parameters have types, so they are covered too. *)
let is_closed state names abs =
  Term.Variable.Map.for_all
    (fun x n ->
      n = 0
      || Term.Variable.Set.mem x names
      || Term.Variable.Set.mem x !(state.top_names))
    (Term.free_vars_abs abs)
  && Type.Params.subset (Term.free_params_abstraction abs) Type.Params.empty

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
      (* Elim-Co-Val *)
      expr
  | Term.Tuple exprs, TyCoercion.TupleCoercion coers
    when state.config.push_coercions && List.length exprs = List.length coers ->
      (* Push-Co-Pair, for tuples of any length. Push-Co-Inl and Push-Co-Inr
         have no counterpart yet: Eff's variants belong to named types, and the
         coercion on a constructor's argument needs the type definition. *)
      Term.tuple (List.map2 (cast_expression state) exprs coers)
  | ( (Term.Handler _ | Term.HandlerWithFinally _),
      TyCoercion.HandlerCoercion
        (({ term = tcoer, dcoer; _ } as dtcoer1), dtcoer2) )
    when state.config.push_coercions
         && Dirt.is_closed (fst dcoer.ty)
         && not (TyCoercion.is_trivial_dirty_coercion dtcoer1) ->
      (* Handler-Subsume. The input part of the coercion moves into the
         handler: the type coercion into the return clause, and the dirt
         coercion narrows the input dirt, which drops the clauses for the
         operations outside it (see With-Cast). The output part stays. The
         finally clause is outside the paper and stays as it is. *)
      let subsume hnd =
        let hnd' =
          if TyCoercion.is_trivial_ty_coercion tcoer then hnd
          else
            let ty, _ = tcoer.ty in
            let x_pat, x_var = Term.fresh_variable "x" ty in
            Term.handler_with_new_value_clause hnd
              (Term.abstraction
                 ( x_pat,
                   Term.letVal
                     (cast_expression state x_var tcoer, hnd.term.value_clause)
                 ))
        in
        match Term.handler_with_smaller_input_dirt hnd' dcoer with
        | Some hnd'' -> hnd''
        | None -> assert false
      in
      let expr' =
        match expr.term with
        | Term.Handler hnd -> Term.handler (subsume hnd)
        | Term.HandlerWithFinally { handler_clauses; finally_clause } ->
            Term.handlerWithFinally (subsume handler_clauses) finally_clause
        | _ -> assert false
      in
      let drty_in, _ = dtcoer1.ty in
      cast_expression state expr'
        (TyCoercion.handlerCoercion (TyCoercion.reflDirty drty_in, dtcoer2))
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
  | Term.LetRec (defs, comp), _ when state.config.push_coercions ->
      (* Push-Co-Rec-Fun *)
      Term.letRec (defs, cast_computation state comp coer)
  | Term.Match (expr, cases), _ when state.config.push_coercions ->
      (* Push-Co-Match, which the paper does not have *)
      let _, drty = coer.ty in
      Term.match_
        (expr, List.map (fun abs -> cast_abstraction state abs coer) cases)
        drty
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
  | Term.LetVal (expr, ({ term = pat, _; _ } as abs))
    when Term.Variable.Map.for_all
           (fun x _ -> Term.does_not_occur x (Term.free_vars_abs bind))
           (Term.pattern_vars pat) ->
      (* A sequence into a let, which copies nothing *)
      Term.letVal (expr, bind_abstraction state abs bind)
  | Term.Match (expr, cases)
    when List.length cases <= 1 || is_application_abs bind ->
      (* A sequence into a match. It copies the continuation into each
         branch, so only if there is at most one, or if the continuation is
         the small [fun b -> b v], where the branches often give the
         function that [b] applies. *)
      let _, drty = bind.ty in
      Term.match_
        (expr, List.map (fun abs -> bind_abstraction state abs bind) cases)
        drty
  | _ -> (
      match extract_cast_value comp with
      | Some expr -> beta_reduce state bind expr
      | None -> Term.bind (comp, bind))

and bind_abstraction state { term = pat, comp; _ } bind =
  Term.abstraction (pat, bind_computation state comp bind)

and handle_computation state hnd comp =
  match handle_call state hnd comp with
  | Some comp' -> comp'
  | None -> handle_other state hnd comp

(* Inline-Top and With-Rec-Fun for a handled full call [x v1 ... vn] of a
   function, curried if [n > 1]. The specialisation of a curried function is
   curried too, and it takes the arguments of the whole call, so that its body
   is the body of the function after all the [fun]s. These rules come before
   With-Do, which would move the pure calls of a curried call out of the
   handler. For the same reason, a full curried call of a recursive function
   that is not specialised stays under the handler: [extract] replaces it
   later, when it is a recursive call in a specialisation being built. *)
and handle_call state hnd comp =
  let arity abs = List.length (fst (curried_params abs)) in
  let kept vs =
    if List.length vs > 1 then Some (Term.handle (Term.handler hnd, comp))
    else None
  in
  match curried_call comp with
  | Some ({ term = Term.Var { variable = x; instantiation; _ }; _ }, vs) -> (
      match building_specialisation state hnd x instantiation vs with
      | Some (mode, name_var) ->
          Some
            (specialised_call mode name_var vs
               (Term.lambda hnd.term.value_clause))
      | None -> (
          match (top_definition state x, vs) with
          | Some (TopValue _), [ v ]
            when state.fuel > 0 && may_specialise state x hnd
                 && state.config.handler_reductions -> (
              (* Inline-Top, so that With-Fun or With-Rec-Fun applies. The
                 guard is that of With-Rec-Fun, also for a non-recursive [x],
                 so that it stops a cycle through top-level definitions, such
                 as [many1] calling [many many1]. *)
              let state' = specialising_under state x hnd in
              match expand_top_application state x instantiation v with
              | Some comp' ->
                  Some
                    (handle_computation state' hnd
                       (optimize_computation state' comp'))
              | None -> assert false)
          | Some (TopRec abs), _
            when state.fuel > 0 && may_specialise state x hnd
                 && state.config.specialize_functions && handles_operations hnd
                 && Type.equal_dirty comp.ty (fst hnd.ty)
                 && arity abs = List.length vs -> (
              match join_group state hnd x instantiation abs vs with
              | `Joined -> Some (handle_computation state hnd comp)
              | `Abandoned -> Some (Term.handle (Term.handler hnd, comp))
              | `Other ->
                  Some
                    (with_rec_fun
                       (specialising_under state x hnd)
                       hnd x
                       (Term.apply_sub_abs instantiation abs)
                       vs ~top:(Some instantiation)))
          | Some (TopRec abs), _ when arity abs = List.length vs -> kept vs
          | None, _ -> (
              match Assoc.lookup x state.rec_functions with
              | Some abs
                when state.config.specialize_functions && handles_operations hnd
                     && may_specialise state x hnd
                     && Type.equal_dirty comp.ty (fst hnd.ty)
                     && arity abs = List.length vs ->
                  Some
                    (with_rec_fun
                       (specialising_under state x hnd)
                       hnd x
                       (Term.apply_sub_abs instantiation abs)
                       vs ~top:None)
              | Some abs when arity abs = List.length vs -> kept vs
              | _ -> None)
          | _ -> None))
  | _ -> None

and handle_other state hnd comp =
  match comp.term with
  | _ when not state.config.handler_reductions ->
      Term.handle (Term.handler hnd, comp)
  | CastComp (comp', { term = tcoer, dcoer; _ })
    when Dirt.is_closed (fst dcoer.ty) -> (
      (* With-Cast. The type coercion moves into the return clause, and the
         dirt coercion narrows the handler, which drops the clauses for the
         operations that [comp'] does not call. It comes before With-Fwd, so
         that a cast does not hide [comp'] from the rules above, such as
         Inline-Top for a handled call of a top-level function. *)
      let hnd' =
        if TyCoercion.is_trivial_ty_coercion tcoer then hnd
        else
          let ty, _ = comp'.ty in
          let x_pat, x_var = Term.fresh_variable "x" ty in
          Term.handler_with_new_value_clause hnd
            (Term.abstraction
               ( x_pat,
                 Term.letVal
                   (cast_expression state x_var tcoer, hnd.term.value_clause) ))
      in
      match Term.handler_with_smaller_input_dirt hnd' dcoer with
      | Some hnd'' -> handle_computation state hnd'' comp'
      | None -> assert false)
  | _ when Assoc.is_empty hnd.term.Term.effect_clauses.effect_part ->
      (* With-Fwd: a handler with no operation clauses only forwards, so it
         becomes a sequence with its return clause. *)
      let ty, drt_in = comp.ty and _, (_, drt_out) = hnd.ty in
      let coer =
        TyCoercion.bangCoercion
          (TyCoercion.reflTy ty, DirtCoercion.subset drt_in drt_out)
      in
      bind_computation state
        (cast_computation state comp coer)
        hnd.term.Term.value_clause
  | Term.Value expr ->
      (* With-Ret *)
      beta_reduce state hnd.term.Term.value_clause expr
  (* With-Match-Pair and With-Match-Sum, With-Let-Val, and the push into a
     [let rec]. The branches are results of handler rules, which are already
     optimised, so only the root of the new term is reduced: handling can make
     Let-Val apply, or leave a recursive function unused. A full pass would
     rewrite the handled calls left in the branches again, with this state,
     where the guards of the rules that left them no longer hold. *)
  | Term.Match (expr, cases) ->
      let _, drty_out = hnd.ty in
      Term.match_ (expr, List.map (handle_abstraction state hnd) cases) drty_out
      |> reduce_computation state
  | LetVal (expr, abs) ->
      Term.letVal (expr, handle_abstraction state hnd abs)
      |> reduce_computation state
  | LetRec (defs, comp) ->
      Term.letRec
        (defs, handle_computation (add_rec_definitions state defs) hnd comp)
      |> reduce_computation state
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
  | _ -> Term.handle (Term.handler hnd, comp)

and handle_abstraction state hnd { term = p, c; _ } =
  Term.abstraction (p, handle_computation state hnd c)

(* A handled call [with hnd handle x v] of a member [x] of the group whose
   specialisation is being built joins it, if the operation clauses and the
   instantiation are the same: [x] gets an entry that is being built, so that
   the call, and all later ones, go to it, and its body is built later. In
   [Fixed] mode, a call under another return clause cannot go to the group,
   so the attempt fails. *)
and join_group state hnd x instantiation abs vs =
  match state.building_group with
  | Some gb
    when Term.Variable.Set.mem x gb.members
         && gb.group_instantiation = instantiation
         && Term.same_operation_clauses gb.group_handler hnd ->
      if
        gb.group_mode = Fixed
        && not (Term.same_return_clause gb.group_handler hnd)
      then (
        (match gb.root.result with
        | Building b -> b.left <- b.left + 1
        | _ -> ());
        `Abandoned)
      else
        let abs = Term.apply_sub_abs instantiation abs in
        let tys =
          List.map (fun (p : Term.pattern) -> p.ty) (fst (curried_params abs))
        in
        let g = specialisation_name state x ~top:true in
        let g_var =
          Term.mono_var g
            (specialisation_ty gb.group_mode gb.group_handler.ty tys)
        in
        let entry =
          {
            original = x;
            instantiation;
            mode = gb.group_mode;
            handler = gb.group_handler;
            result = Building { name_var = g_var; left = 0 };
          }
        in
        state.specialisations := entry :: !(state.specialisations);
        if building_specialisation state hnd x instantiation vs <> None then (
          Queue.add (x, abs, g, g_var) gb.pending;
          `Joined)
        else (
          state.specialisations :=
            List.filter (fun e -> e != entry) !(state.specialisations);
          `Other)
  | _ -> `Other

(* A fresh name for a specialisation of [f]. A top-level one may become a
   top-level definition, which needs a name that no source definition has. *)
and specialisation_name state f ~top =
  let g =
    if top then
      Term.Variable.fresh
        ("$handled_" ^ Term.Variable.fold (fun desc _ -> desc) (origin state f))
    else Term.Variable.refresh f
  in
  state.origins := Term.Variable.Map.add g (origin state f) !(state.origins);
  g

(* With-Rec-Fun; see the comment at [extract]. [f] is already in
   [state.specialising] with the fingerprint of [hnd].

   For a top-level [f] at the instantiation [top], the paper first applies
   Inline-Top, which gives a local copy [rec f' x. M[η]]. We specialise [f]
   itself: the calls that [extract] leaves go to [f η], which Inline-Top would
   turn into [f'] anyway. If [f] belongs to a group of mutually recursive
   top-level functions, the members that are called under the same operation
   clauses are specialised together with it, one specialisation each, and the
   group is specialised in one mode. Then the specialisations are closed if
   the handler mentions only top-level names, which is always the case for the
   operation clauses in the tests, and the return clause too in [Fixed] mode.
   Closed specialisations become new top-level definitions, emitted together,
   and are cached, so the next call of a member under an equal handler reuses
   them. *)
and with_rec_fun state hnd f abs vs ~top =
  let (ty_in, _), drty_out = hnd.ty in
  let k_ty = Type.arrow (ty_in, drty_out) in
  let g_ty mode tys = specialisation_ty mode hnd.ty tys in
  let f_tys =
    List.map (fun (p : Term.pattern) -> p.ty) (fst (curried_params abs))
  in
  let call mode g_var =
    specialised_call mode g_var vs (Term.lambda hnd.term.value_clause)
  in
  (* The body of the specialisation [g] of a member with [abs], and how to
     make the definition of [g] from the body once [extract] has rewritten
     it *)
  let build_member state mode abs =
    let pats, body =
      curried_params (Term.refresh_abstraction Assoc.empty abs)
    in
    let hnd_m, define =
      match mode with
      | Fixed -> (hnd, fun body -> curried_abstraction pats body)
      | Varying ->
          let k_pat, k_var = Term.fresh_variable "k" k_ty in
          let y_pat, y_var = Term.fresh_variable "y" ty_in in
          let hnd_k =
            Term.handler_with_new_value_clause hnd
              (Term.abstraction (y_pat, Term.apply (k_var, y_var)))
          in
          (hnd_k, fun body -> curried_abstraction (pats @ [ k_pat ]) body)
    in
    (define, handle_computation state hnd_m body)
  in
  let build mode =
    let g = specialisation_name state f ~top:(top <> None) in
    let g_var = Term.mono_var g (g_ty mode f_tys) in
    let left = ref false in
    match top with
    | None ->
        let define, body = build_member state mode abs in
        let body' = extract mode hnd f g_var ~left body in
        ([ (f, g, g_var, define body') ], !left)
    | Some instantiation ->
        let root =
          {
            original = f;
            instantiation;
            mode;
            handler = hnd;
            result = Building { name_var = g_var; left = 0 };
          }
        in
        state.specialisations := root :: !(state.specialisations);
        let gb =
          {
            members =
              Term.Variable.Map.find_opt f !(state.groups)
              |> Option.value ~default:(Term.Variable.Set.singleton f);
            group_handler = hnd;
            group_mode = mode;
            group_instantiation = instantiation;
            root;
            pending = Queue.create ();
          }
        in
        let state_g = { state with building_group = Some gb } in
        let first = (f, g, g_var, build_member state_g mode abs) in
        let rec rest built =
          match Queue.take_opt gb.pending with
          | None -> List.rev built
          | Some (x, abs_x, g_x, g_var_x) ->
              rest ((x, g_x, g_var_x, build_member state_g mode abs_x) :: built)
        in
        let members = first :: rest [] in
        let names =
          List.fold_left
            (fun names (_, g, _, _) -> Term.Variable.Set.add g names)
            Term.Variable.Set.empty members
        in
        let extract_all body =
          List.fold_left
            (fun body (x, _, g_var, _) -> extract mode hnd x g_var ~left body)
            body members
        in
        let entries =
          List.filter
            (fun e ->
              match e.result with
              | Building
                  { name_var = { term = Term.Var { variable; _ }; _ }; _ } ->
                  Term.Variable.Set.mem variable names
              | _ -> false)
            !(state.specialisations)
        in
        List.iter
          (fun e ->
            match e.result with
            | Building b when b.left > 0 -> left := true
            | _ -> ())
          entries;
        state.specialisations :=
          List.filter
            (fun e -> not (List.memq e entries))
            !(state.specialisations);
        ( List.map
            (fun (x, g, g_var, (define, body)) ->
              (x, g, g_var, define (extract_all body)))
            members,
          !left )
  in
  let lookup mode =
    match top with
    | None -> None
    | Some instantiation ->
        List.find_opt
          (fun entry ->
            entry.original = f && entry.mode = mode
            && entry.instantiation = instantiation
            && Term.same_operation_clauses entry.handler hnd
            && (mode = Varying || Term.same_return_clause entry.handler hnd)
            &&
            match entry.result with
            | Built { name_var; _ } ->
                Type.equal_ty name_var.ty (g_ty mode f_tys)
            | FixedFails -> true
            | Building _ -> false)
          !(state.specialisations)
  in
  let store mode original result =
    match top with
    | None -> ()
    | Some instantiation ->
        state.specialisations :=
          { original; instantiation; mode; handler = hnd; result }
          :: !(state.specialisations)
  in
  let specialise mode =
    match lookup mode with
    | Some { result = Built { name_var; _ }; _ } -> `Shared name_var
    | Some { result = FixedFails; _ } -> `Fails
    | Some { result = Building _; _ } | None ->
        (* If building leaves a handled call that an enclosing [Fixed]
           attempt could not take, that attempt is discarded, and this
           specialisation has a handled call that the next attempt would
           replace. So it is not cached. *)
        let enclosing = !(state.specialisations) in
        let enclosing_left () =
          List.fold_left
            (fun n e -> match e.result with Building b -> n + b.left | _ -> n)
            0 enclosing
        in
        let left_before = enclosing_left () in
        let members, left = build mode in
        let names =
          List.fold_left
            (fun names (_, g, _, _) -> Term.Variable.Set.add g names)
            Term.Variable.Set.empty members
        in
        let closed =
          top <> None
          && enclosing_left () = left_before
          && List.for_all
               (fun (_, _, _, g_abs) -> is_closed state names g_abs)
               members
        in
        let _, _, root_var, _ = List.hd members in
        if left then (
          if closed then store mode f FixedFails;
          `Fails)
        else if closed then (
          Term.Variable.Set.iter (add_top_name state) names;
          List.iter
            (fun (_, g, _, _) ->
              state.groups := Term.Variable.Map.add g names !(state.groups))
            members;
          List.iter
            (fun (x, g, g_var, g_abs) ->
              let definition = optimize_abstraction state g_abs in
              store mode x
                (Built
                   {
                     name = g;
                     name_var = g_var;
                     definition;
                     group = names;
                     emitted = false;
                   }))
            members;
          `Shared root_var)
        else `Local (members, root_var)
  in
  let finish mode = function
    | `Shared g_var -> call mode g_var
    | `Local (members, root_var) ->
        (* Still with [f] in [specialising]: calls of [f] that [extract] has
           left are not specialised again under the same handler. *)
        optimize_computation state
          (Term.letRec
             ( Assoc.of_list
                 (List.map (fun (_, g, _, g_abs) -> (g, g_abs)) members),
               call mode root_var ))
    | `Fails -> assert false
  in
  (* For a top-level [f], a [Fixed] specialisation can be shared only if the
     return clause is closed, and a [Varying] one if the operation clauses
     are. If only the latter holds, we use [Varying], which is slower at run
     time but made once, instead of a local [Fixed] copy at every call. *)
  let share_varying =
    let top_only fvs =
      Term.Variable.Map.for_all
        (fun x n -> n = 0 || Term.Variable.Set.mem x !(state.top_names))
        fvs
    in
    Term.Variable.Map.empty
    |> Assoc.fold_right
         (fun (_, abs2) fvs -> Term.( @@@ ) fvs (Term.free_vars_abs2 abs2))
         hnd.term.effect_clauses.effect_part
    |> top_only
    && Type.Params.subset
         (Term.free_params_handler_clauses hnd)
         Type.Params.empty
    && not (top_only (Term.free_vars_abs hnd.term.value_clause))
  in
  match top with
  | Some _ when share_varying -> finish Varying (specialise Varying)
  | _ -> (
      match specialise Fixed with
      | `Fails -> finish Varying (specialise Varying)
      | result -> finish Fixed result)

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
  | Term.Var { variable; instantiation; _ } -> (
      (* Inline-Top for a top-level variable or constant, which copies
         nothing, as the local Let-Val does *)
      match inline_top_value state variable instantiation with
      | Some ({ term = Term.Var _ | Term.Const _; _ } as e) -> e
      | _ -> expr)
  | Term.Lambda
      {
        term =
          ( { term = Term.PVar x; _ },
            {
              term =
                Term.Apply
                  ( ({ term = Term.Var { variable = f; _ }; _ } as f_var),
                    { term = Term.Var { variable = x'; _ }; _ } );
              _;
            } );
        _;
      }
    when x = x' && f <> x && Type.equal_ty f_var.ty expr.ty ->
      (* Eta: [fun x -> f x] is [f], as [f] is a variable, so a value. Varying
         specialisations pass their continuation on in this form. *)
      f_var
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
  | Term.Apply ({ term = Term.Var { variable = x; instantiation; _ }; _ }, v)
    when is_handler_value v
         &&
         match Assoc.lookup x state.top_definitions with
         | Some (TopValue _) -> true
         | _ -> false -> (
      (* Inline-Top for a function applied to a handler, so that the handler
         reaches the [with] that installs it *)
      match expand_top_application state x instantiation v with
      | Some comp' -> optimize_computation state comp'
      | None -> comp)
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
  | Term.LetRec (defs, c) when non_recursive defs <> None -> (
      (* [let rec f x = M in N] where [M] does not mention [f] is
         [let f = fun x -> M in N], which the other rules then reduce. *)
      match non_recursive defs with
      | Some (f, abs) ->
          let fn = Term.lambda abs in
          reduce_computation state
            (Term.letVal (fn, Term.abstraction (Term.pVar f fn.ty, c)))
      | None -> assert false)
  | Term.LetRec (defs, c) -> (
      let c' = optimize_computation state c in
      match keep_used_bindings defs c' with
      | [] -> c'
      | defs' -> Term.letRec (Assoc.of_list defs', c'))
  | Term.Bind (comp, abs) -> bind_computation state comp abs
  | Term.Handle ({ term = Term.Var { variable; instantiation; _ }; _ }, comp')
    when state.config.handler_reductions
         && inline_top_value state variable instantiation <> None -> (
      (* Inline-Top for a top-level handler, so that the handler rules see
         its clauses *)
      match inline_top_value state variable instantiation with
      | Some e -> reduce_computation state (Term.handle (e, comp'))
      | None -> comp)
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

(* The shared specialisations that the terms with free variables [fvs] use,
   directly or through each other, and that are not emitted yet. A
   specialisation uses only older ones, so one pass from newest to oldest
   finds them all, and the result is in the order of definition. *)
let new_top_definitions state fvs =
  let used = ref fvs in
  let is_used x = not (Term.does_not_occur x !used) in
  List.fold_left
    (fun defs entry ->
      match entry.result with
      | Built { name; group; emitted = false; _ } when is_used name ->
          (* The whole group of [name], as one recursive definition *)
          let members =
            List.filter_map
              (fun e ->
                match e.result with
                | Built ({ name; emitted = false; _ } as b)
                  when Term.Variable.Set.mem name group ->
                    b.emitted <- true;
                    used := Term.( @@@ ) !used (Term.free_vars_abs b.definition);
                    Some
                      ( name,
                        (Type.Params.empty, Constraints.empty, b.definition) )
                | _ -> None)
              !(state.specialisations)
          in
          Assoc.of_list (List.rev members) :: defs
      | _ -> defs)
    [] !(state.specialisations)

let process_computation state ((params, comp, constraints) as top_comp) =
  if !Config.enable_optimization then
    let comp' = optimize_computation state comp in
    ( new_top_definitions state (Term.free_vars_comp comp'),
      (params, comp', constraints) )
  else ([], top_comp)

(* Record a top-level definition for Inline-Top: the paper's [D]. *)
let add_top_definition state x def =
  { state with top_definitions = Assoc.update x def state.top_definitions }

let process_top_let state defs =
  if !Config.enable_optimization then (
    let defs' =
      List.map
        (fun (pat, params, cnstrs, comp) ->
          (pat, params, cnstrs, optimize_computation state comp))
        defs
    in
    let state' =
      List.fold_left
        (fun state (pat, _, _, comp) ->
          match (pat.term, comp.term) with
          | Term.PVar x, Term.Value e -> add_top_definition state x (TopValue e)
          | _ -> state)
        state defs'
    in
    List.iter
      (fun (pat, _, _, _) ->
        Term.Variable.Map.iter
          (fun x _ -> add_top_name state x)
          (Term.pattern_vars pat))
      defs;
    let fvs =
      Term.concat_vars
        (List.map (fun (_, _, _, c) -> Term.free_vars_comp c) defs')
    in
    (state', new_top_definitions state fvs, defs'))
  else (state, [], defs)

let optimize_top_rec_definitions state defs =
  Assoc.map
    (fun (params, cnstrs, abs) ->
      (params, cnstrs, optimize_abstraction state abs))
    defs

let process_top_let_rec state defs =
  if !Config.enable_optimization then (
    let members =
      Assoc.to_list defs |> List.map fst |> Term.Variable.Set.of_list
    in
    Term.Variable.Set.iter
      (fun f -> state.groups := Term.Variable.Map.add f members !(state.groups))
      members;
    let defs' = optimize_top_rec_definitions state defs in
    (* A definition that does not mention itself is just a function, which
       Inline-Top can inline. *)
    let function_only =
      non_recursive (Assoc.map (fun (_, _, abs) -> abs) defs')
    in
    let state' =
      Assoc.fold_left
        (fun state (f, (_, _, abs)) ->
          add_top_definition state f
            (match function_only with
            | Some _ -> TopValue (Term.lambda abs)
            | None -> TopRec abs))
        state defs'
    in
    List.iter (fun (f, _) -> add_top_name state f) (Assoc.to_list defs);
    let fvs =
      Term.concat_vars
        (List.map
           (fun (_, (_, _, abs)) -> Term.free_vars_abs abs)
           (Assoc.to_list defs'))
    in
    (state', new_top_definitions state fvs, defs'))
  else (state, [], defs)
