(** Desugaring of syntax into the core language. *)

open CoreUtils
module T = Type
module Sugared = SugaredSyntax
module Untyped = UntypedSyntax

type constructor_kind = Variant of bool | Effect of bool

(* This is so OCaml doesn't complain about:
    Error (warning 37): constructor Effect is never used to build values. *)

let _ = Effect true

type state = {
  context : (string, CoreTypes.Variable.t) Assoc.t;
  effect_symbols : (string, CoreTypes.Effect.t) Assoc.t;
  field_symbols : (string, CoreTypes.Field.t) Assoc.t;
  tyname_symbols : (string, CoreTypes.TyName.t) Assoc.t;
  constructors : (string, CoreTypes.Label.t * constructor_kind) Assoc.t;
  local_type_annotations : (string, CoreTypes.TyParam.t) Assoc.t;
}

let initial_state =
  let list_cons = (CoreTypes.cons_annot, (CoreTypes.cons, Variant true)) in
  let list_nil = (CoreTypes.nil_annot, (CoreTypes.nil, Variant false)) in
  let initial_types =
    Assoc.of_list
      [
        ("bool", CoreTypes.bool_tyname);
        ("int", CoreTypes.int_tyname);
        ("unit", CoreTypes.unit_tyname);
        ("string", CoreTypes.string_tyname);
        ("float", CoreTypes.float_tyname);
        ("list", CoreTypes.list_tyname);
        ("empty", CoreTypes.empty_tyname);
      ]
  in
  {
    context = Assoc.empty;
    effect_symbols = Assoc.empty;
    field_symbols = Assoc.empty;
    tyname_symbols = initial_types;
    constructors = Assoc.of_list [ list_cons; list_nil ];
    local_type_annotations = Assoc.empty;
  }

let add_loc t loc = { it = t; at = loc }

let effect_to_symbol state name =
  match Assoc.lookup name state.effect_symbols with
  | Some sym -> (state, sym)
  | None ->
      let sym = CoreTypes.Effect.fresh name in
      let effect_symbols' = Assoc.update name sym state.effect_symbols in
      ({ state with effect_symbols = effect_symbols' }, sym)

let field_to_symbol state name =
  match Assoc.lookup name state.field_symbols with
  | Some sym -> (state, sym)
  | None ->
      let sym = CoreTypes.Field.fresh name in
      let field_symbols' = Assoc.update name sym state.field_symbols in
      ({ state with field_symbols = field_symbols' }, sym)

let tyname_to_symbol state name =
  match Assoc.lookup name state.tyname_symbols with
  | Some sym -> (state, sym)
  | None ->
      let sym = CoreTypes.TyName.fresh name in
      let tyname_symbols' = Assoc.update name sym state.tyname_symbols in
      ({ state with tyname_symbols = tyname_symbols' }, sym)

(* ***** Desugaring of types. ***** *)
(* Desugar a type, where only the given type, dirt and region parameters may appear.
   If a type application with missing dirt and region parameters is encountered,
   it uses [ds] and [rs] instead. This is used in desugaring of recursive type definitions
   where we need to figure out which type and dirt parameters are missing in a type defnition.
   Also, it relies on the optional region parameter in [T.Apply] to figure out whether
   an application applies to an effect type. So, it is prudent to call [fill_args] before
   calling [ty].
*)
let desugar_type type_sbst state =
  let rec desugar_type state { it = t; at = loc } =
    match t with
    | Sugared.TyApply (t, tys) ->
        let state', t' = tyname_to_symbol state t in
        let state'', tys' = fold_map desugar_type state' tys in
        (state'', T.Apply (t', tys'))
    | Sugared.TyParam t -> (
        match Assoc.lookup t type_sbst with
        | None -> Error.syntax ~loc "Unbound type parameter '%s" t
        | Some p -> (state, T.TyParam p))
    | Sugared.TyArrow (t1, t2) ->
        let state', t1' = desugar_type state t1 in
        let state'', t2' = desugar_type state' t2 in
        (state'', T.Arrow (t1', t2'))
    | Sugared.TyTuple lst ->
        let state', lst' = fold_map desugar_type state lst in
        (state', T.Tuple lst')
    | Sugared.TyHandler (t1, t2) ->
        let state', t1' = desugar_type state t1 in
        let state'', t2' = desugar_type state' t2 in
        (state'', T.Handler { T.value = t1'; T.finally = t2' })
  in
  desugar_type state

(** [free_type_params t] returns all free type params in [t]. *)
let free_type_params t =
  let rec ty_params { it = t; at = _loc } =
    match t with
    | Sugared.TyApply (_, tys) -> List.map ty_params tys |> List.flatten
    | Sugared.TyParam s -> [ s ]
    | Sugared.TyArrow (t1, t2) -> ty_params t1 @ ty_params t2
    | Sugared.TyTuple lst -> List.map ty_params lst |> List.flatten
    | Sugared.TyHandler (t1, t2) -> ty_params t1 @ ty_params t2
  in
  unique_elements (ty_params t)

let syntax_to_core_params ts =
  Assoc.map_of_list (fun p -> (p, Type.fresh_ty_param ())) ts

(** [desugar_tydef state params def] desugars the type definition with parameters
    [params] and definition [def]. *)
let desugar_tydef state params def =
  let ty_sbst = syntax_to_core_params params in
  let state', def' =
    match def with
    | Sugared.TyRecord flds ->
        let field_desugar st (f, t) =
          let st', f' = field_to_symbol st f in
          let st'', t' = desugar_type ty_sbst st' t in
          (st'', (f', t'))
        in
        let state', flds' = Assoc.kfold_map field_desugar state flds in
        (state', TypeContext.Record flds')
    | Sugared.TySum assoc ->
        let aux_desug st (lbl, cons) =
          let unsugared_lbl =
            match Assoc.lookup lbl st.constructors with
            | None -> failwith "unreachable"
            | Some (lbl', _cons_kind) -> lbl'
          in
          match cons with
          | None -> (st, (unsugared_lbl, None))
          | Some t ->
              let st', t' = desugar_type ty_sbst st t in
              (st', (unsugared_lbl, Some t'))
        in
        let constructors =
          (* desugar constructor names to Symbol  and add to state *)
          let aux (lbl, cons) =
            let unsugared_lbl =
              match Assoc.lookup lbl state.constructors with
              | None -> CoreTypes.Label.fresh lbl
              | Some (lbl, _) -> lbl
              (* Caught by inference for better error *)
            in
            match cons with
            | None -> (lbl, (unsugared_lbl, Variant false))
            | Some _ -> (lbl, (unsugared_lbl, Variant true))
          in
          let new_cons = Assoc.kmap aux assoc in
          Assoc.concat new_cons state.constructors
        in
        (* desugar and rename constructors in type *)
        let state', assoc' =
          Assoc.kfold_map aux_desug { state with constructors } assoc
        in
        (state', TypeContext.Sum assoc')
    | Sugared.TyInline t ->
        let state', t' = desugar_type ty_sbst state t in
        (state', TypeContext.Inline t')
  in
  (state', (Assoc.values_of ty_sbst, def'))

(** [desugar_tydefs defs] desugars the simultaneous type definitions [defs]. *)
let desugar_tydefs state sugared_defs =
  let desugar_fold st (name, (params, def)) =
    (* First desugar the type names *)
    let st', sym = tyname_to_symbol st name in
    (* Then the types themselves *)
    let st'', (params', def') = desugar_tydef st' params def in
    (st'', (sym, (params', def')))
  in
  Assoc.kfold_map desugar_fold state sugared_defs

(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_var opt] creates a fresh variable on each call *)
let fresh_var = function
  | None -> CoreTypes.Variable.fresh "$anon"
  | Some x -> CoreTypes.Variable.fresh x

let id_abstraction loc =
  let x = fresh_var (Some "$id_par") in
  ( add_loc (Untyped.PVar x) loc,
    add_loc (Untyped.Value (add_loc (Untyped.Var x) loc)) loc )

let desugar_pattern state ?(initial_forbidden = []) p =
  let vars = ref Assoc.empty in
  let forbidden = ref initial_forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~loc:p.at "Variable %s occurs more than once in a pattern" x
    else
      let var = fresh_var (Some x) in
      vars := Assoc.update x var !vars;
      forbidden := x :: !forbidden;
      var
  in
  let rec desugar_pattern state { it = p; at = loc } =
    let state', p' =
      match p with
      | Sugared.PVar x ->
          let x = new_var x in
          (state, Untyped.PVar x)
      | Sugared.PAnnotated (p, t) ->
          let bind bound_ps p =
            match Assoc.lookup p bound_ps with
            | Some _ty_param -> bound_ps
            | None -> Assoc.update p (Type.fresh_ty_param ()) bound_ps
          in
          let free_params = free_type_params t in
          let bound_params = state.local_type_annotations in
          let bound_params' = List.fold_left bind bound_params free_params in
          let state' = { state with local_type_annotations = bound_params' } in
          let state'', p' = desugar_pattern state' p in
          let state''', t' = desugar_type bound_params' state'' t in
          (state''', Untyped.PAnnotated (p', t'))
      | Sugared.PAs (p, x) ->
          let x = new_var x in
          let state', p' = desugar_pattern state p in
          (state', Untyped.PAs (p', x))
      | Sugared.PTuple ps ->
          let state', ps' = fold_map desugar_pattern state ps in
          (state', Untyped.PTuple ps')
      | Sugared.PRecord flds ->
          let field_desugar st (f, p) =
            let st', f' = field_to_symbol st f in
            let st'', p' = desugar_pattern st' p in
            (st'', (f', p'))
          in
          let state', flds' = Assoc.kfold_map field_desugar state flds in
          (state', Untyped.PRecord flds')
      | Sugared.PVariant (lbl, p) -> (
          match Assoc.lookup lbl state.constructors with
          | None -> Error.typing ~loc "Unbound constructor %s" lbl
          | Some (cons_lbl, Variant var) -> (
              match (var, p) with
              | true, Some p ->
                  let state', p' = desugar_pattern state p in
                  (state', Untyped.PVariant (cons_lbl, Some p'))
              | false, None -> (state, Untyped.PVariant (cons_lbl, None))
              | true, None ->
                  Error.typing ~loc
                    "Constructor %s should be applied to an argument." lbl
              | false, Some _ ->
                  Error.typing ~loc
                    "Constructor %s cannot be applied to an argument." lbl)
          | Some (_cons_lbl, Effect _eff) ->
              Error.typing ~loc
                "Constructor %s should not be an effect constructor." lbl)
      | Sugared.PConst c -> (state, Untyped.PConst c)
      | Sugared.PNonbinding -> (state, Untyped.PNonbinding)
    in
    (state', add_loc p' loc)
  in
  let state', p' = desugar_pattern state p in
  (state', !vars, p')

(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec desugar_expression state { it = t; at = loc } =
  let state', w, e =
    match t with
    | Sugared.Var x -> (
        match Assoc.lookup x state.context with
        | Some n -> (state, [], Untyped.Var n)
        | None -> Error.typing ~loc "Unknown variable %s" x)
    | Sugared.Const k -> (state, [], Untyped.Const k)
    | Sugared.Annotated (t, ty) ->
        let bind bound_ps p =
          match Assoc.lookup p bound_ps with
          | Some _ty_param -> bound_ps
          | None -> Assoc.update p (Type.fresh_ty_param ()) bound_ps
        in
        let free_params = free_type_params ty in
        let bound_params = state.local_type_annotations in
        let bound_params' = List.fold_left bind bound_params free_params in
        let state' = { state with local_type_annotations = bound_params' } in
        let state'', w, e = desugar_expression state' t in
        let state''', ty' = desugar_type bound_params' state'' ty in
        (state''', w, Untyped.Annotated (e, ty'))
    | Sugared.Lambda a ->
        let state', a' = desugar_abstraction state a in
        (state', [], Untyped.Lambda a')
    | Sugared.Function cs ->
        let x = fresh_var (Some "$function") in
        let state', cs' = fold_map desugar_abstraction state cs in
        ( state',
          [],
          Untyped.Lambda
            ( add_loc (Untyped.PVar x) loc,
              add_loc (Untyped.Match (add_loc (Untyped.Var x) loc, cs')) loc )
        )
    | Sugared.Handler cs ->
        let state', h' = desugar_handler loc state cs in
        (state', [], Untyped.Handler h')
    | Sugared.Tuple ts ->
        let state', w, es = desugar_expressions state ts in
        (state', w, Untyped.Tuple es)
    | Sugared.Record ts ->
        if not (CoreUtils.no_duplicates (Assoc.keys_of ts)) then
          Error.syntax ~loc "Fields in a record must be distinct";
        let state', w, es = desugar_record_fields state ts in
        (state', w, Untyped.Record es)
    | Sugared.Variant (lbl, t) -> (
        match Assoc.lookup lbl state.constructors with
        | None -> Error.typing ~loc "Unbound constructor %s" lbl
        | Some (cons_lbl, Variant var) -> (
            match (var, t) with
            | true, Some t ->
                let state', w, e = desugar_expression state t in
                (state', w, Untyped.Variant (cons_lbl, Some e))
            | false, None -> (state, [], Untyped.Variant (cons_lbl, None))
            | true, None ->
                Error.typing ~loc
                  "Constructor %s should be applied to an argument." lbl
            | false, Some _ ->
                Error.typing ~loc
                  "Constructor %s cannot be applied to an argument." lbl)
        | Some (_cons_lbl, Effect _eff) ->
            Error.typing ~loc
              "Constructor %s should not be an effect constructor." lbl)
    (* Terms that are desugared into computations. We list them explicitly in
       order to catch any future constructs. *)
    | Sugared.Apply _ | Sugared.Match _ | Sugared.Let _ | Sugared.LetRec _
    | Sugared.Handle _ | Sugared.Conditional _ | Sugared.Check _
    | Sugared.Effect _ ->
        let x = fresh_var (Some "$bind") in
        let state', c = desugar_computation state { it = t; at = loc } in
        let w = [ (add_loc (Untyped.PVar x) loc, c) ] in
        (state', w, Untyped.Var x)
  in
  (state', w, add_loc e loc)

and desugar_computation state { it = t; at = loc } =
  let if_then_else e c1 c2 =
    let true_p = add_loc (Untyped.PConst Const.of_true) c1.at in
    let false_p = add_loc (Untyped.PConst Const.of_false) c2.at in
    Untyped.Match (e, [ (true_p, c1); (false_p, c2) ])
  in
  let state', w, c =
    match t with
    | Sugared.Apply
        ( {
            it = Sugared.Apply ({ it = Sugared.Var "&&"; at = _loc1 }, t1);
            at = loc2;
          },
          t2 ) ->
        let state', w1, e1 = desugar_expression state t1 in
        let untyped_false loc = add_loc (Untyped.Const Const.of_false) loc in
        let state'', c1 = desugar_computation state' t2 in
        let c2 = add_loc (Untyped.Value (untyped_false loc2)) loc2 in
        (state'', w1, if_then_else e1 c1 c2)
    | Sugared.Apply
        ( {
            it = Sugared.Apply ({ it = Sugared.Var "||"; at = _loc1 }, t1);
            at = loc2;
          },
          t2 ) ->
        let state', w1, e1 = desugar_expression state t1 in
        let untyped_true loc = add_loc (Untyped.Const Const.of_true) loc in
        let c1 = add_loc (Untyped.Value (untyped_true loc2)) loc2 in
        let state'', c2 = desugar_computation state' t2 in
        (state'', w1, if_then_else e1 c1 c2)
    | Sugared.Apply (t1, t2) ->
        let state', w1, e1 = desugar_expression state t1 in
        let state'', w2, e2 = desugar_expression state' t2 in
        (state'', w1 @ w2, Untyped.Apply (e1, e2))
    | Sugared.Effect (eff, t) -> (
        match Assoc.lookup eff state.effect_symbols with
        | Some eff' ->
            let state', w, e = desugar_expression state t in
            let loc_eff = add_loc (Untyped.Effect eff') loc in
            (state', w, Untyped.Apply (loc_eff, e))
        | None -> Error.typing ~loc "Unknown operation %s" eff)
    | Sugared.Match (t, cs) -> match_constructor state loc t cs
    | Sugared.Handle (t1, t2) ->
        let state', w1, e1 = desugar_expression state t1 in
        let state'', c2 = desugar_computation state' t2 in
        (state'', w1, Untyped.Handle (e1, c2))
    | Sugared.Conditional (t, t1, t2) ->
        let state', w, e = desugar_expression state t in
        let state'', c1 = desugar_computation state' t1 in
        let state''', c2 = desugar_computation state'' t2 in
        (state''', w, if_then_else e c1 c2)
    | Sugared.Check t ->
        let state', c = desugar_computation state t in
        (state', [], Untyped.Check c)
    | Sugared.Let (defs, t) ->
        let aux_desugar (p, c) (fold_state, defs, forbidden) =
          let check_forbidden (x, _) =
            if List.mem x forbidden then
              Error.syntax ~loc:p.at "Several definitions of %s" x
          in
          let state', p_vars, p' = desugar_pattern state p in
          Assoc.iter check_forbidden p_vars;
          let _, c' = desugar_computation state' c in
          ( { state with context = Assoc.concat p_vars fold_state.context },
            (p', c') :: defs,
            Assoc.keys_of p_vars @ forbidden )
        in
        let state', defs', _ =
          List.fold_right aux_desugar defs (state, [], [])
        in
        let _, c = desugar_computation state' t in
        (state, [], Untyped.Let (defs', c))
    | Sugared.LetRec (defs, t) ->
        let aux_desugar (x, t) (fold_state, ns, forbidden) =
          if List.mem x forbidden then
            Error.syntax ~loc:t.at "Several definitions of %s" x;
          let n = fresh_var (Some x) in
          ( { state with context = Assoc.update x n fold_state.context },
            n :: ns,
            x :: forbidden )
        in
        let state', ns, _ = List.fold_right aux_desugar defs (state, [], []) in
        let desugar_defs (p, (_, c)) defs =
          let _, c = desugar_let_rec state' c in
          (p, c) :: defs
        in
        let defs' = List.fold_right desugar_defs (List.combine ns defs) [] in
        let _, c = desugar_computation state' t in
        (state, [], Untyped.LetRec (defs', c))
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | Sugared.Var _ | Sugared.Const _ | Sugared.Annotated _ | Sugared.Tuple _
    | Sugared.Record _ | Sugared.Variant _ | Sugared.Lambda _
    | Sugared.Function _ | Sugared.Handler _ ->
        let state', w, e = desugar_expression state { it = t; at = loc } in
        (state', w, Untyped.Value e)
  in
  match w with
  | [] -> (state', add_loc c loc)
  | _ :: _ -> (state', add_loc (Untyped.Let (w, add_loc c loc)) loc)

and desugar_abstraction state (p, t) =
  let old_context = state.context in
  let state', p_vars, p' = desugar_pattern state p in
  let new_context = Assoc.concat p_vars state'.context in
  let state'', c =
    desugar_computation { state' with context = new_context } t
  in
  ({ state'' with context = old_context }, (p', c))

and desugar_abstraction2 state (p1, p2, t) =
  let old_context = state.context in
  let state', p_vars1, p1' = desugar_pattern state p1 in
  let state'', p_vars2, p2' = desugar_pattern state' p2 in
  let new_context =
    Assoc.concat (Assoc.concat p_vars1 p_vars2) state''.context
  in
  let state''', t' =
    desugar_computation { state'' with context = new_context } t
  in
  ({ state''' with context = old_context }, (p1', p2', t'))

and desugar_let_rec state { it = exp; at = loc } =
  match exp with
  | Sugared.Lambda a -> desugar_abstraction state a
  | Sugared.Function cs ->
      let x = fresh_var (Some "$let_rec_function") in
      let state', cs = fold_map desugar_abstraction state cs in
      let new_match = Untyped.Match (add_loc (Untyped.Var x) loc, cs) in
      (state', (add_loc (Untyped.PVar x) loc, add_loc new_match loc))
  | _ ->
      Error.syntax ~loc
        "This kind of expression is not allowed in a recursive definition"

and desugar_expressions state = function
  | [] -> (state, [], [])
  | t :: ts ->
      let state', w, e = desugar_expression state t in
      let state'', ws, es = desugar_expressions state' ts in
      (state'', w @ ws, e :: es)

and desugar_record_fields state flds =
  match Assoc.pop flds with
  | None -> (state, [], Assoc.empty)
  | Some ((fld, t), flds') ->
      let state', fld' = field_to_symbol state fld in
      let state'', w, e = desugar_expression state' t in
      let state''', ws, es = desugar_record_fields state'' flds' in
      (state''', w @ ws, Assoc.update fld' e es)

and desugar_handler loc state
    {
      Sugared.effect_clauses = eff_cs;
      Sugared.value_clause = val_cs;
      Sugared.finally_clause = fin_cs;
    } =
  (* Construct a desugared handler with match statements. *)
  let group_eff_cs (eff, a2) assoc =
    match Assoc.lookup eff assoc with
    | None -> Assoc.update eff [ a2 ] assoc
    | Some a2s -> Assoc.replace eff (a2 :: a2s) assoc
  in
  let construct_eff_clause state (eff, eff_cs_lst) =
    (* transform string name to CoreTypes.Effect.t *)
    let state', eff' = effect_to_symbol state eff in
    match eff_cs_lst with
    | [] -> assert false
    | [ a2 ] ->
        let state'', a2' = desugar_abstraction2 state' a2 in
        (state'', (eff', a2'))
    | a2s ->
        let x = fresh_var (Some "$eff_param") in
        let k = fresh_var (Some "$continuation") in
        let x_k_vars =
          Untyped.Tuple
            [ add_loc (Untyped.Var x) loc; add_loc (Untyped.Var k) loc ]
        in
        let match_term_fun state =
          let aux st a2 =
            let st', (p1', p2', t') = desugar_abstraction2 st a2 in
            (st', (add_loc (Untyped.PTuple [ p1'; p2' ]) loc, t'))
          in
          let state', a2s' = fold_map aux state a2s in
          (state', add_loc (Untyped.Match (add_loc x_k_vars loc, a2s')) loc)
        in
        let p1, p2 = (Untyped.PVar x, Untyped.PVar k) in
        let state'', match_term = match_term_fun state' in
        let new_eff_cs = (eff', (add_loc p1 loc, add_loc p2 loc, match_term)) in
        (state'', new_eff_cs)
  in
  (* group eff cases by effects into lumps to transform into matches *)
  let collected_eff_cs = Assoc.fold_right group_eff_cs eff_cs Assoc.empty in
  (* construct match cases for effects with more than one pattern *)
  let state', untyped_eff_cs =
    Assoc.kfold_map construct_eff_clause state collected_eff_cs
  in
  (* construct match case for value *)
  let state'', untyped_val_a =
    match val_cs with
    | [] -> (state', id_abstraction loc)
    | cs ->
        let v = fresh_var (Some "$val_param") in
        let v_var = add_loc (Untyped.Var v) loc in
        let state'', cs = fold_map desugar_abstraction state' cs in
        ( state'',
          (add_loc (Untyped.PVar v) loc, add_loc (Untyped.Match (v_var, cs)) loc)
        )
  in
  (* construct match case for finally clause *)
  let state''', untyped_fin_a =
    match fin_cs with
    | [] -> (state'', id_abstraction loc)
    | cs ->
        let fin = fresh_var (Some "$fin_param") in
        let fin_var = add_loc (Untyped.Var fin) loc in
        let state''', cs' = fold_map desugar_abstraction state cs in
        ( state''',
          ( add_loc (Untyped.PVar fin) loc,
            add_loc (Untyped.Match (fin_var, cs')) loc ) )
  in
  ( state''',
    {
      Untyped.effect_clauses = untyped_eff_cs;
      Untyped.value_clause = untyped_val_a;
      Untyped.finally_clause = untyped_fin_a;
    } )

and match_constructor state loc t cs =
  (* Separate value and effect cases. *)
  let val_cs, eff_cs = separate_match_cases cs in
  match eff_cs with
  | [] ->
      let state', w, e = desugar_expression state t in
      let state'', val_cs' = fold_map desugar_abstraction state' val_cs in
      (state'', w, Untyped.Match (e, val_cs'))
  | _ ->
      let val_cs = List.map (fun cs -> Sugared.Val_match cs) val_cs in
      let x = "$id_par" in
      let value_match =
        add_loc (Sugared.Match (add_loc (Sugared.Var x) loc, val_cs)) loc
      in
      let h_value_clause = (add_loc (Sugared.PVar x) loc, value_match) in
      let sugared_h =
        {
          Sugared.effect_clauses = Assoc.of_list eff_cs;
          Sugared.value_clause = [ h_value_clause ];
          Sugared.finally_clause = [];
        }
      in
      let state', c = desugar_computation state t in
      let state'', h = desugar_handler loc state' sugared_h in
      let loc_h = { it = Untyped.Handler h; at = loc } in
      (state'', [], Untyped.Handle (loc_h, c))

and separate_match_cases cs =
  let separator case (val_cs, eff_cs) =
    match case with
    | Sugared.Val_match v_cs -> (v_cs :: val_cs, eff_cs)
    | Sugared.Eff_match e_cs -> (val_cs, e_cs :: eff_cs)
  in
  List.fold_right separator cs ([], [])

let desugar_top_let state defs =
  let aux_desugar (p, c) (fold_state, defs, forbidden) =
    let check_forbidden (x, _) =
      if List.mem x forbidden then
        Error.syntax ~loc:p.at "Several definitions of %s" x
    in
    let state', p_vars, p' = desugar_pattern state p in
    Assoc.iter check_forbidden p_vars;
    let _, c' = desugar_computation state' c in
    ( { state with context = Assoc.concat p_vars fold_state.context },
      (p', c') :: defs,
      Assoc.keys_of p_vars @ forbidden )
  in
  let state', defs', _ = List.fold_right aux_desugar defs (state, [], []) in
  (state', defs')

let desugar_top_let_rec state defs =
  let aux_desugar (x, t) (fold_state, ns, forbidden) =
    if List.mem x forbidden then
      Error.syntax ~loc:t.at "Several definitions of %s" x;
    let n = fresh_var (Some x) in
    ( { state with context = Assoc.update x n fold_state.context },
      n :: ns,
      x :: forbidden )
  in
  let state', ns, _ = List.fold_right aux_desugar defs (state, [], []) in
  let desugar_defs (p, (_, c)) defs =
    let _, c = desugar_let_rec state' c in
    (p, c) :: defs
  in
  let defs' = List.fold_right desugar_defs (List.combine ns defs) [] in
  (state', defs')

let desugar_external state (x, t, f) =
  let n = fresh_var (Some x) in
  let ts = syntax_to_core_params (free_type_params t) in
  let _state', t' = desugar_type ts state t in
  ({ state with context = Assoc.update x n state.context }, (n, t', f))

let desugar_def_effect state (eff, (ty1, ty2)) =
  let state', eff' = effect_to_symbol state eff in
  let state'', ty1' = desugar_type Assoc.empty state' ty1 in
  let state''', ty2' = desugar_type Assoc.empty state'' ty2 in
  (state''', (eff', (ty1', ty2')))
