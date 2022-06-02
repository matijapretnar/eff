(** Desugaring of syntax into the core language. *)

open Utils
open Language
module Sugared = SugaredSyntax
module Untyped = UntypedSyntax
module T = Type

type constructor_kind = Variant of bool | Effect of bool

(* This is so OCaml doesn't complain about:
    Error (warning 37): constructor Effect is never used to build values. *)

let _ = Effect true

module StringMap = Map.Make (String)

let add_unique ~loc kind str symb string_map =
  StringMap.update str
    (function
      | None -> Some symb
      | Some _ -> Error.syntax ~loc "%s %s defined multiple times." kind str)
    string_map

type state = {
  context : Term.Variable.t StringMap.t;
  effect_symbols : Effect.t StringMap.t;
  field_symbols : Type.Field.t StringMap.t;
  tyname_symbols : (TyName.t * (Type.TyParam.t * variance) list) StringMap.t;
  constructors : (Type.Label.t * constructor_kind) StringMap.t;
  local_type_annotations : (Type.TyParam.t * Type.ty) StringMap.t;
  inlined_types : Type.ty StringMap.t;
}

let initial_state =
  let constructors =
    StringMap.empty
    |> StringMap.add Type.cons_annot (Type.cons, Variant true)
    |> StringMap.add Type.nil_annot (Type.nil, Variant false)
  and tyname_symbols =
    StringMap.empty
    |> StringMap.add "bool" (Type.bool_tyname, [])
    |> StringMap.add "int" (Type.int_tyname, [])
    |> StringMap.add "unit" (Type.unit_tyname, [])
    |> StringMap.add "string" (Type.string_tyname, [])
    |> StringMap.add "float" (Type.float_tyname, [])
    |> StringMap.add "list"
         (Type.list_tyname, [ (Type.list_ty_param, Covariant) ])
    |> StringMap.add "empty" (Type.empty_tyname, [])
  and inlined_types =
    StringMap.empty
    |> StringMap.add "bool" Type.bool_ty
    |> StringMap.add "int" Type.int_ty
    |> StringMap.add "unit" Type.unit_ty
    |> StringMap.add "string" Type.string_ty
    |> StringMap.add "float" Type.float_ty
  in
  {
    context = StringMap.empty;
    effect_symbols = StringMap.empty;
    field_symbols = StringMap.empty;
    tyname_symbols;
    constructors;
    local_type_annotations = StringMap.empty;
    inlined_types;
  }

let add_variables vars state =
  let context' = StringMap.fold StringMap.add vars state.context in
  { state with context = context' }

let add_unique_variables ~loc vars context =
  StringMap.fold (add_unique ~loc "Variable") vars context

let add_loc t loc = { it = t; at = loc }

let effect_to_symbol ~loc state name =
  match StringMap.find_opt name state.effect_symbols with
  | Some sym -> (state, sym)
  | None -> Error.syntax ~loc "Unknown effect %s" name

let field_to_symbol ~loc state name =
  match StringMap.find_opt name state.field_symbols with
  | Some sym -> (state, sym)
  | None -> Error.syntax ~loc "Unknown field %s" name

let tyname_to_symbol ~loc state name =
  match StringMap.find_opt name state.tyname_symbols with
  | Some sym -> sym
  | None -> Error.syntax ~loc "Unknown type %s" name

let force_param ty =
  match ty.term with Type.TyParam t -> t | _ -> failwith "Cant get param"

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
    | Sugared.TyApply (t, tys) -> (
        let t', lst = tyname_to_symbol ~loc state t in
        let n = List.length lst in
        if List.length tys <> n then
          Error.syntax ~loc "Type %t expects %d arguments" (TyName.print t') n;
        match StringMap.find_opt t state.inlined_types with
        | Some ty -> (state, ty)
        | None ->
            let t', lst = tyname_to_symbol ~loc state t in
            let n = List.length lst in
            if List.length tys <> n then
              Error.syntax ~loc "Type %t expects %d arguments" (TyName.print t')
                n
            else
              let state', tys' = List.fold_map desugar_type state tys in
              let type_info =
                lst
                |> List.map2
                     (fun ty (param, variance) -> (param, (ty, variance)))
                     tys'
              in
              (state', T.apply (t', Type.TyParam.Map.of_bindings type_info)))
    | Sugared.TyParam t -> (
        match StringMap.find_opt t type_sbst with
        | None -> Error.syntax ~loc "Unbound type parameter '%s" t
        | Some (_, ty, _) -> (state, ty))
    | Sugared.TyArrow (t1, t2) ->
        let state', t1' = desugar_type state t1 in
        let state'', t2' = desugar_dirty_type state' t2 in
        (state'', T.arrow (t1', t2'))
    | Sugared.TyTuple lst ->
        let state', lst' = List.fold_map desugar_type state lst in
        (state', T.tuple lst')
    | Sugared.TyHandler (t1, t2) ->
        let state', t1' = desugar_dirty_type state t1 in
        let state'', t2' = desugar_dirty_type state' t2 in
        (state'', T.handler (t1', t2'))
  and desugar_dirty_type state ty =
    let state', ty' = desugar_type state ty in
    (state', T.make_dirty ty')
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
  List.unique_elements (ty_params t)

let fresh_ty_param () =
  let ty = Type.fresh_ty_with_fresh_skel () in
  let param = force_param ty in
  (param, ty)

let syntax_to_core_params ts =
  let core_params =
    ts
    |> List.map (fun (p, variance) ->
           let param, ty = fresh_ty_param () in
           (p, (param, ty, variance)))
  in
  core_params |> List.to_seq |> StringMap.of_seq

(** [desugar_tydef state params def] desugars the type definition with parameters
    [params] and definition [def]. *)
let desugar_tydef ~loc state
    (ty_sbst : (T.TyParam.t * T.ty * variance) StringMap.t) ty_name def =
  let state', def' =
    match def with
    | Sugared.TyRecord flds ->
        let field_desugar st (f, t) =
          let f' = Type.Field.fresh f in
          let st', t' = desugar_type ty_sbst st t in
          let st'' =
            {
              st' with
              field_symbols = add_unique ~loc "Field" f f' st'.field_symbols;
            }
          in
          (st'', (f', t'))
        in
        let state', flds' = Assoc.kfold_map field_desugar state flds in
        let flds' = Type.Field.Map.of_bindings (Assoc.to_list flds') in
        (state', Type.Record flds')
    | Sugared.TySum assoc ->
        let aux (st, sum_def) (lbl, ty) =
          let lbl' = Type.Label.fresh lbl in
          let st', ty', kind =
            match ty with
            | None -> (st, None, Variant false)
            | Some ty ->
                let st, ty = desugar_type ty_sbst st ty in
                (st, Some ty, Variant true)
          in
          let st'' =
            {
              st' with
              constructors =
                add_unique ~loc "Constructor" lbl (lbl', kind) st'.constructors;
            }
          in
          let sum_def' = Type.Field.Map.add lbl' ty' sum_def in
          (st'', sum_def')
        in
        let state', sum_def' =
          Assoc.fold_left aux (state, Type.Field.Map.empty) assoc
        in
        (state', Type.Sum sum_def')
    | Sugared.TyInline t ->
        let state', t' = desugar_type ty_sbst state t in
        let state'' =
          {
            state' with
            inlined_types = StringMap.add ty_name t' state'.inlined_types;
          }
        in
        (state'', Type.Inline t')
  in
  let ty_params =
    ty_sbst |> StringMap.bindings
    |> List.map (fun (_, (param, ty, variance)) -> (param, (ty.ty, variance)))
    |> Type.TyParam.Map.of_bindings
  in
  let ty_params =
    {
      Type.type_params = ty_params;
      dirt_params = Dirt.Param.Set.empty;
      skel_params =
        Type.TyParam.Map.fold
          (fun _ (skeleton, _) skels ->
            Skeleton.Param.Set.union
              (skeleton |> Type.free_params_skeleton).skel_params skels)
          ty_params Skeleton.Param.Set.empty;
    }
  in
  (state', { Type.params = ty_params; type_def = def' })

(** [desugar_tydefs defs] desugars the simultaneous type definitions [defs]. *)
let desugar_tydefs ~loc (state : state) sugared_defs =
  let add_ty_names
      (tyname_symbols :
        (TyName.t * (Type.TyParam.t * variance) list) StringMap.t)
      (name, (params, tydef)) =
    let sym = TyName.fresh name in

    let ty_sbst = syntax_to_core_params params in
    let ty_param_subs =
      params
      |> List.map (fun (pname, _) ->
             ty_sbst |> StringMap.find pname |> fun (_, ty, variance) ->
             (force_param ty, variance))
    in
    ( add_unique ~loc "Type" name (sym, ty_param_subs) tyname_symbols,
      (name, (ty_sbst, tydef)) )
  in
  let tyname_symbols, sugared_defs =
    Assoc.kfold_map add_ty_names state.tyname_symbols sugared_defs
  in
  let state' = { state with tyname_symbols } in
  let desugar_fold st (name, (params, def)) =
    (* First desugar the type names *)
    let sym, _ = StringMap.find name st.tyname_symbols in
    (* Then the types themselves *)
    let st', tydef = desugar_tydef ~loc st params name def in
    (st', (sym, tydef))
  in
  Assoc.kfold_map desugar_fold state' sugared_defs

(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_var opt] creates a fresh variable on each call *)
let fresh_var = function
  | None -> Term.Variable.fresh "$anon"
  | Some x -> Term.Variable.fresh x

let id_abstraction loc =
  let x = fresh_var (Some "$id_par") in
  ( add_loc (Untyped.PVar x) loc,
    add_loc (Untyped.Value (add_loc (Untyped.Var x) loc)) loc )

let desugar_pattern state p =
  let vars = ref StringMap.empty in
  let rec desugar_pattern state { it = p; at = loc } =
    let state', p' =
      match p with
      | Sugared.PVar x ->
          let x' = fresh_var (Some x) in
          let state' =
            { state with context = StringMap.add x x' state.context }
          in
          vars := add_unique ~loc "Variable" x x' !vars;
          (state', Untyped.PVar x')
      | Sugared.PAnnotated (p, t) ->
          let bind bound_ps p =
            match StringMap.find_opt p bound_ps with
            | Some _ty_param -> bound_ps
            | None -> StringMap.add p (fresh_ty_param ()) bound_ps
          in
          let free_params = free_type_params t in
          let bound_params = state.local_type_annotations in
          let bound_params' = List.fold_left bind bound_params free_params in
          let state' = { state with local_type_annotations = bound_params' } in
          let state'', p' = desugar_pattern state' p in
          let state''', t' =
            desugar_type
              (bound_params' |> StringMap.map (fun (p, t) -> (p, t, Invariant)))
              state'' t
          in
          (state''', Untyped.PAnnotated (p', t'))
      | Sugared.PAs (p, x) ->
          let x' = fresh_var (Some x) in
          let state' =
            { state with context = StringMap.add x x' state.context }
          in
          vars := add_unique ~loc "Variable" x x' !vars;
          let state'', p' = desugar_pattern state' p in
          (state'', Untyped.PAs (p', x'))
      | Sugared.PTuple ps ->
          let state', ps' = List.fold_map desugar_pattern state ps in
          (state', Untyped.PTuple ps')
      | Sugared.PRecord flds ->
          let field_desugar st (f, p) =
            let st', f' = field_to_symbol ~loc st f in
            let st'', p' = desugar_pattern st' p in
            (st'', (f', p'))
          in
          let state', flds' = Assoc.kfold_map field_desugar state flds in
          let flds' = flds' |> Assoc.to_list |> Type.Field.Map.of_bindings in
          (state', Untyped.PRecord flds')
      | Sugared.PVariant (lbl, p) -> (
          match StringMap.find_opt lbl state.constructors with
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
        match StringMap.find_opt x state.context with
        | Some n -> (state, [], Untyped.Var n)
        | None -> Error.typing ~loc "Unknown variable %s" x)
    | Sugared.Const k -> (state, [], Untyped.Const k)
    | Sugared.Annotated (t, ty) ->
        let bind bound_ps p =
          match StringMap.find_opt p bound_ps with
          | Some _ty_param -> bound_ps
          | None -> StringMap.add p (fresh_ty_param ()) bound_ps
        in
        let free_params = free_type_params ty in
        let bound_params = state.local_type_annotations in
        let bound_params' = List.fold_left bind bound_params free_params in
        let state' = { state with local_type_annotations = bound_params' } in
        let state'', w, e = desugar_expression state' t in
        let state''', ty' =
          desugar_type
            (bound_params' |> StringMap.map (fun (p, t) -> (p, t, Invariant)))
            state'' ty
        in
        (state''', w, Untyped.Annotated (e, ty'))
    | Sugared.Lambda a ->
        let state', a' = desugar_abstraction state a in
        (state', [], Untyped.Lambda a')
    | Sugared.Function cs ->
        let x = fresh_var (Some "$function") in
        let state', cs' = List.fold_map desugar_abstraction state cs in
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
        if not (List.no_duplicates (Assoc.keys_of ts)) then
          Error.syntax ~loc "Fields in a record must be distinct";
        let state', w, es = desugar_record_fields ~loc state ts in
        (state', w, Untyped.Record es)
    | Sugared.Variant (lbl, t) -> (
        match StringMap.find_opt lbl state.constructors with
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
        match StringMap.find_opt eff state.effect_symbols with
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
        let aux_desugar (p, c) (new_vars, defs) =
          let state', p_vars, p' = desugar_pattern state p in
          let _, c' =
            desugar_computation { state' with context = state.context } c
          in
          (add_unique_variables ~loc p_vars new_vars, (p', c') :: defs)
        in
        let new_vars, defs' =
          List.fold_right aux_desugar defs (StringMap.empty, [])
        in
        let _, c = desugar_computation (add_variables new_vars state) t in
        (state, [], Untyped.Let (defs', c))
    | Sugared.LetRec (defs, t) ->
        let aux_desugar (x, _) (fold_state, ns) =
          let n = fresh_var (Some x) in
          ( { state with context = StringMap.add x n fold_state.context },
            n :: ns )
        in
        let state', ns = List.fold_right aux_desugar defs (state, []) in
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
  let state'' = add_variables p_vars state' in
  let state''', c = desugar_computation state'' t in
  ({ state''' with context = old_context }, (p', c))

and desugar_abstraction2 state (p1, p2, t) =
  let old_context = state.context in
  let state', p_vars1, p1' = desugar_pattern state p1 in
  let state'', p_vars2, p2' = desugar_pattern state' p2 in
  let state''' = state'' |> add_variables p_vars1 |> add_variables p_vars2 in
  let state'''', t' = desugar_computation state''' t in
  ({ state'''' with context = old_context }, (p1', p2', t'))

and desugar_let_rec state { it = exp; at = loc } =
  match exp with
  | Sugared.Lambda a -> desugar_abstraction state a
  | Sugared.Function cs ->
      let x = fresh_var (Some "$let_rec_function") in
      let state', cs = List.fold_map desugar_abstraction state cs in
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

and desugar_record_fields ~loc state flds =
  Assoc.fold_right
    (fun (fld, t) (st, ws, mp) ->
      let state', fld' = field_to_symbol ~loc st fld in
      let state'', w, e = desugar_expression state' t in
      (state'', w @ ws, Type.Field.Map.add fld' e mp))
    flds
    (state, [], Type.Field.Map.empty)

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
    (* transform string name to Effect.t *)
    let state', eff' = effect_to_symbol ~loc state eff in
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
          let state', a2s' = List.fold_map aux state a2s in
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
        let state'', cs = List.fold_map desugar_abstraction state' cs in
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
        let state''', cs' = List.fold_map desugar_abstraction state cs in
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
      let state'', val_cs' = List.fold_map desugar_abstraction state' val_cs in
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

let desugar_top_let ~loc state defs =
  let aux_desugar (p, c) (new_vars, defs) =
    let state', p_vars, p' = desugar_pattern state p in
    let _, c' = desugar_computation { state' with context = state.context } c in
    (add_unique_variables ~loc p_vars new_vars, (p', c') :: defs)
  in
  let new_vars, defs' =
    List.fold_right aux_desugar defs (StringMap.empty, [])
  in
  (add_variables new_vars state, defs')

let desugar_top_let_rec state defs =
  let aux_desugar (x, t) (vars, ns) =
    let n = fresh_var (Some x) in
    (add_unique ~loc:t.at "Variable" x n vars, n :: ns)
  in
  let vars, ns = List.fold_right aux_desugar defs (StringMap.empty, []) in
  let state' = add_variables vars state in
  let desugar_defs (p, (_, c)) defs =
    let _, c = desugar_let_rec state' c in
    (p, c) :: defs
  in
  let defs' = List.fold_right desugar_defs (List.combine ns defs) [] in
  (state', defs')

let load_primitive_value state x prim =
  {
    state with
    context =
      StringMap.add (Primitives.primitive_value_name prim) x state.context;
  }

let load_primitive_effect state eff prim =
  {
    state with
    effect_symbols =
      StringMap.add
        (Primitives.primitive_effect_name prim)
        eff state.effect_symbols;
  }

let desugar_def_effect ~loc state (eff, (ty1, ty2)) =
  let eff' = Effect.fresh eff in
  let state' =
    {
      state with
      effect_symbols = add_unique ~loc "Effect" eff eff' state.effect_symbols;
    }
  in
  let state'', ty1' = desugar_type StringMap.empty state' ty1 in
  let state''', ty2' = desugar_type StringMap.empty state'' ty2 in
  (state''', (eff', (ty1', ty2')))
