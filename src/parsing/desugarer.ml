(** Desugaring of syntax into the core language. *)

module CU = CoreUtils
module Utils = OldUtils
module T = Type
module Sugared = SugaredSyntax
module Untyped = UntypedSyntax

type constructor_kind = Variant of bool | Effect of bool

type state =
  { context: (string, Untyped.variable) Assoc.t
  ; constructors: (string, constructor_kind) Assoc.t }

let initial_state =
  let init_cons = [(Utils.cons, Variant true); (Utils.nil, Variant false)] in
  {context= Assoc.empty; constructors= Assoc.of_list init_cons}

let add_loc t loc = {CU.it= t; CU.at= loc}
let loc_of loc_t = loc_t.CU.at
let term_of loc_t = loc_t.CU.it

(* ***** Desugaring of types. ***** *)
(* Desugar a type, where only the given type, dirt and region parameters may appear.
   If a type application with missing dirt and region parameters is encountered,
   it uses [ds] and [rs] instead. This is used in desugaring of recursive type definitions
   where we need to figure out which type and dirt parameters are missing in a type defnition.
   Also, it relies on the optional region parameter in [T.Apply] to figure out whether
   an application applies to an effect type. So, it is prudent to call [fill_args] before
   calling [ty].
*)
let desugar_type type_sbst =
  let rec desugar_type {CU.it=t; CU.at=loc} =
    match t with
    | Sugared.TyApply (t, tys) ->
        let tys' = List.map desugar_type tys in
        T.Apply (t, tys')
    | Sugared.TyParam t -> (
      match Assoc.lookup t type_sbst with
      | None -> Error.syntax ~loc "Unbound type parameter '%s" t
      | Some p -> T.TyParam p )
    | Sugared.TyArrow (t1, t2) -> T.Arrow (desugar_type t1, desugar_type t2)
    | Sugared.TyTuple lst -> T.Tuple (List.map desugar_type lst)
    | Sugared.TyHandler (t1, t2) ->
        T.Handler {T.value= desugar_type t1; T.finally= desugar_type t2}
  in
  desugar_type


(** [free_type_params t] returns all free type params in [t]. *)
let free_type_params t =
  let rec ty_params {CU.it=t; CU.at=loc} =
    match t with
    | Sugared.TyApply (_, tys) -> OldUtils.flatten_map ty_params tys
    | Sugared.TyParam s -> [s]
    | Sugared.TyArrow (t1, t2) -> ty_params t1 @ ty_params t2
    | Sugared.TyTuple lst -> OldUtils.flatten_map ty_params lst
    | Sugared.TyHandler (t1, t2) -> ty_params t1 @ ty_params t2
  in
  OldUtils.uniq (ty_params t)


let syntax_to_core_params ts =
  Assoc.map_of_list (fun p -> (p, Type.fresh_ty_param ())) ts


(** [desugar_tydef state params def] desugars the type definition with parameters
    [params] and definition [def]. *)
let desugar_tydef state params def =
  let ty_sbst = syntax_to_core_params params in
  let state', def' =
    match def with
    | Sugared.TyRecord flds ->
        (state, Tctx.Record (Assoc.map (fun t -> desugar_type ty_sbst t) flds))
    | Sugared.TySum lst ->
        let aux_desugar t = Utils.option_map (desugar_type ty_sbst) t in
        let new_constructors =
          Assoc.map
            (function None -> Variant false | Some _ -> Variant true)
            lst
        in
        ( { state with
            constructors= Assoc.concat new_constructors state.constructors }
        , Tctx.Sum (Assoc.map aux_desugar lst) )
    | Sugared.TyInline t -> (state, Tctx.Inline (desugar_type ty_sbst t))
  in
  (state', (Assoc.values_of ty_sbst, def'))


(** [desugar_tydefs defs] desugars the simultaneous type definitions [defs]. *)
let desugar_tydefs state sugared_defs =
  let desugar_fold state (tyname, (params, def)) =
    let state', tydef' = desugar_tydef state params def in
    (state', (tyname, tydef'))
  in
  Assoc.fold_map desugar_fold state sugared_defs


(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_var opt] creates a fresh variable on each call *)
let fresh_var = function
  | None -> Untyped.Variable.fresh "anon"
  | Some x -> Untyped.Variable.fresh x


let id_abstraction loc =
  let x = fresh_var (Some "$id_par") in
  ( add_loc (Untyped.PVar x) loc
  , add_loc (Untyped.Value (add_loc (Untyped.Var x) loc)) loc )


let desugar_pattern state ?(initial_forbidden= []) p =
  let vars = ref Assoc.empty in
  let forbidden = ref initial_forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~loc:(loc_of p) "Variable %s occurs more than once in a pattern" x
    else
      let var = fresh_var (Some x) in
      vars := Assoc.update x var !vars ;
      forbidden := x :: !forbidden ;
      var
  in
  let rec desugar_pattern state {CU.it=p; CU.at=loc} =
    let p' =
      match p with
      | Sugared.PVar x ->
          let x = new_var x in
          Untyped.PVar x
      | Sugared.PAs (p, x) ->
          let x = new_var x in
          let p' = desugar_pattern state p in
          Untyped.PAs (p', x)
      | Sugared.PTuple ps ->
          Untyped.PTuple (List.map (desugar_pattern state) ps)
      | Sugared.PRecord flds ->
          Untyped.PRecord (Assoc.map (desugar_pattern state) flds)
      | Sugared.PVariant (lbl, p) -> (
        match Assoc.lookup lbl state.constructors with
        | None -> Error.typing ~loc "Unbound constructor %s" lbl
        | Some Variant var ->
          match (var, p) with
          | true, Some p ->
              Untyped.PVariant (lbl, Some (desugar_pattern state p))
          | false, None -> Untyped.PVariant (lbl, None)
          | true, None ->
              Error.typing ~loc
                "Constructor %s should be applied to an argument." lbl
          | false, Some _ ->
              Error.typing ~loc
                "Constructor %s cannot be applied to an argument." lbl )
      | Sugared.PConst c -> Untyped.PConst c
      | Sugared.PNonbinding -> Untyped.PNonbinding
    in
    add_loc p' loc
  in
  let p' = desugar_pattern state p in
  (!vars, p')


(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec desugar_expression state {CU.it=t; CU.at=loc} =
  let w, e =
    match t with
    | Sugared.Var x -> (
      match Assoc.lookup x state.context with
      | Some n -> ([], Untyped.Var n)
      | None -> Error.typing ~loc "Unknown variable %s" x )
    | Sugared.Const k -> ([], Untyped.Const k)
    | Sugared.Lambda a ->
        let a = desugar_abstraction state a in
        ([], Untyped.Lambda a)
    | Sugared.Function cs ->
        let x = fresh_var (Some "$function") in
        let cs = List.map (desugar_abstraction state) cs in
        ( []
        , Untyped.Lambda
            ( add_loc (Untyped.PVar x) loc
            , add_loc (Untyped.Match (add_loc (Untyped.Var x) loc, cs)) loc )
        )
    | Sugared.Handler cs ->
        let w, h = desugar_handler loc state cs in
        (w, Untyped.Handler h)
    | Sugared.Tuple ts ->
        let w, es = desugar_expressions state ts in
        (w, Untyped.Tuple es)
    | Sugared.Record ts ->
        if not (Utils.injective (fun x -> x) (Assoc.keys_of ts)) then
          Error.syntax ~loc "Fields in a record must be distinct" ;
        let w, es = desugar_record_fields state ts in
        (w, Untyped.Record es)
    | Sugared.Variant (lbl, t) -> (
      match Assoc.lookup lbl state.constructors with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some Variant var ->
        match (var, t) with
        | true, Some t ->
            let w, e = desugar_expression state t in
            (w, Untyped.Variant (lbl, Some e))
        | false, None -> ([], Untyped.Variant (lbl, None))
        | true, None ->
            Error.typing ~loc
              "Constructor %s should be applied to an argument." lbl
        | false, Some _ ->
            Error.typing ~loc
              "Constructor %s cannot be applied to an argument." lbl )
    (* Terms that are desugared into computations. We list them explicitly in
       order to catch any future constructs. *)
    | Sugared.Apply _ | Sugared.Match _ | Sugared.Let _ | Sugared.LetRec _
     |Sugared.Handle _ | Sugared.Conditional _ | Sugared.Check _
     |Sugared.Effect _ ->
        let x = fresh_var (Some "$bind") in
        let c = desugar_computation state {CU.it=t; CU.at=loc} in
        let w = [(add_loc (Untyped.PVar x) loc, c)] in
        (w, Untyped.Var x)
  in
  (w, add_loc e loc)


and desugar_computation state {CU.it=t; CU.at=loc} =
  let if_then_else e c1 c2 =
    let true_p = add_loc (Untyped.PConst Const.of_true) (loc_of c1) in
    let false_p =
      add_loc (Untyped.PConst Const.of_false) (loc_of c2)
    in
    Untyped.Match (e, [(true_p, c1); (false_p, c2)])
  in
  let w, c =
    match t with
    | Sugared.Apply ({CU.it=Sugared.Apply ({CU.it=Sugared.Var "&&"; CU.at=loc1}, t1); CU.at=loc2}, t2) ->
        let w1, e1 = desugar_expression state t1 in
        let untyped_false loc = add_loc (Untyped.Const Const.of_false) loc in
        let c1 = desugar_computation state t2 in
        let c2 = add_loc (Untyped.Value (untyped_false loc2)) loc2 in
        (w1, if_then_else e1 c1 c2)
    | Sugared.Apply ({CU.it=Sugared.Apply ({CU.it=Sugared.Var "||"; CU.at=loc1}, t1); CU.at=loc2}, t2) ->
        let w1, e1 = desugar_expression state t1 in
        let untyped_true loc = add_loc (Untyped.Const Const.of_true) loc in
        let c1 = add_loc (Untyped.Value (untyped_true loc2)) loc2 in
        let c2 = desugar_computation state t2 in
        (w1, if_then_else e1 c1 c2)
    | Sugared.Apply (t1, t2) ->
        let w1, e1 = desugar_expression state t1 in
        let w2, e2 = desugar_expression state t2 in
        (w1 @ w2, Untyped.Apply (e1, e2))
    | Sugared.Effect (eff, t) ->
        let w, e = desugar_expression state t in
        let loc_eff = add_loc (Untyped.Effect eff) loc in
        (w, Untyped.Apply (loc_eff, e))
    | Sugared.Match (t, cs) -> match_constructor state loc t cs
    | Sugared.Handle (t1, t2) ->
        let w1, e1 = desugar_expression state t1 in
        let c2 = desugar_computation state t2 in
        (w1, Untyped.Handle (e1, c2))
    | Sugared.Conditional (t, t1, t2) ->
        let w, e = desugar_expression state t in
        let c1 = desugar_computation state t1 in
        let c2 = desugar_computation state t2 in
        (w, if_then_else e c1 c2)
    | Sugared.Check t -> ([], Untyped.Check (desugar_computation state t))
    | Sugared.Let (defs, t) ->
        let aux_desugar (p, c) (fold_state, defs, forbidden) =
          let check_forbidden (x, _) =
            if List.mem x forbidden then
              Error.syntax ~loc:(loc_of p) "Several definitions of %s" x
          in
          let p_vars, p' = desugar_pattern state p in
          Assoc.iter check_forbidden p_vars ;
          let c' = desugar_computation state c in
          ( {state with context= Assoc.concat p_vars fold_state.context}
          , (p', c') :: defs
          , Assoc.keys_of p_vars @ forbidden )
        in
        let state', defs', _ =
          List.fold_right aux_desugar defs (state, [], [])
        in
        let c = desugar_computation state' t in
        ([], Untyped.Let (defs', c))
    | Sugared.LetRec (defs, t) ->
        let aux_desugar (x, t) (fold_state, ns, forbidden) =
          if List.mem x forbidden then
            Error.syntax ~loc:(loc_of t) "Several definitions of %s" x ;
          let n = fresh_var (Some x) in
          ( {state with context= Assoc.update x n fold_state.context}
          , n :: ns
          , x :: forbidden )
        in
        let state', ns, _ = List.fold_right aux_desugar defs (state, [], []) in
        let desugar_defs (p, (_, c)) defs =
          let c = desugar_let_rec state' c in
          (p, c) :: defs
        in
        let defs' = List.fold_right desugar_defs (List.combine ns defs) [] in
        let c = desugar_computation state' t in
        ([], Untyped.LetRec (defs', c))
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | Sugared.Var _ | Sugared.Const _ | Sugared.Tuple _ | Sugared.Record _
     |Sugared.Variant _ | Sugared.Lambda _ | Sugared.Function _
     |Sugared.Handler _ ->
        let w, e = desugar_expression state {CU.it=t; CU.at=loc} in
        (w, Untyped.Value e)
  in
  match w with
  | [] -> add_loc c loc
  | _ :: _ -> add_loc (Untyped.Let (w, add_loc c loc)) loc


and desugar_abstraction state (p, t) =
  let p_vars, p' = desugar_pattern state p in
  let context' = Assoc.concat p_vars state.context in
  (p', desugar_computation {state with context= context'} t)


and desugar_abstraction2 state (p1, p2, t) =
  let p_vars1, p1' = desugar_pattern state p1 in
  let p_vars2, p2' = desugar_pattern state p2 in
  let context' = Assoc.concat (Assoc.concat p_vars1 p_vars2) state.context in
  let t' = desugar_computation {state with context= context'} t in
  (p1', p2', t')


and desugar_let_rec state exp =
  let loc = loc_of exp in
  match term_of exp with
  | Sugared.Lambda a -> desugar_abstraction state a
  | Sugared.Function cs ->
      let x = fresh_var (Some "$let_rec_function") in
      let cs = List.map (desugar_abstraction state) cs in
      let new_match = Untyped.Match (add_loc (Untyped.Var x) loc, cs) in
      (add_loc (Untyped.PVar x) loc, add_loc new_match loc)
  | _ ->
      Error.syntax ~loc
        "This kind of expression is not allowed in a recursive definition"


and desugar_expressions state = function
  | [] -> ([], [])
  | t :: ts ->
      let w, e = desugar_expression state t in
      let ws, es = desugar_expressions state ts in
      (w @ ws, e :: es)


and desugar_record_fields state flds =
  match Assoc.pop flds with
  | None, _ -> ([], Assoc.empty)
  | Some (fld, t), flds' ->
      let w, e = desugar_expression state t in
      let ws, es = desugar_record_fields state flds' in
      (w @ ws, Assoc.update fld e es)


and desugar_handler loc state
    { Sugared.effect_clauses= eff_cs
    ; Sugared.value_clause= val_cs
    ; Sugared.finally_clause= fin_cs } =
  (* Construct a desugared handler with match statements. *)
  let rec group_eff_cs (eff, a2) assoc =
    match Assoc.lookup eff assoc with
    | None -> Assoc.update eff [a2] assoc
    | Some a2s -> Assoc.replace eff (a2 :: a2s) assoc
  in
  let rec construct_eff_clause eff_cs_lst =
    match eff_cs_lst with
    | [] -> assert false
    | [a2] -> desugar_abstraction2 state a2
    | a2s ->
        let x = fresh_var (Some "$eff_param") in
        let k = fresh_var (Some "$continuation") in
        let x_k_vars =
          Untyped.Tuple
            [add_loc (Untyped.Var x) loc; add_loc (Untyped.Var k) loc]
        in
        let match_term =
          let aux a2 =
            let p1', p2', t' = desugar_abstraction2 state a2 in
            (add_loc (Untyped.PTuple [p1'; p2']) loc, t')
          in
          add_loc (Untyped.Match (add_loc x_k_vars loc, List.map aux a2s)) loc
        in
        let p1, p2 = (Untyped.PVar x, Untyped.PVar k) in
        (add_loc p1 loc, add_loc p2 loc, match_term)
  in
  let collected_eff_cs = Assoc.fold_right group_eff_cs eff_cs Assoc.empty in
  let untyped_eff_cs = Assoc.map construct_eff_clause collected_eff_cs in
  let untyped_val_a =
    match val_cs with
    | [] -> id_abstraction loc
    | cs ->
        let v = fresh_var (Some "$val_param") in
        let v_var = add_loc (Untyped.Var v) loc in
        let cs = List.map (desugar_abstraction state) cs in
        (add_loc (Untyped.PVar v) loc, add_loc (Untyped.Match (v_var, cs)) loc)
  in
  let untyped_fin_a =
    match fin_cs with
    | [] -> id_abstraction loc
    | cs ->
        let fin = fresh_var (Some "$fin_param") in
        let fin_var = add_loc (Untyped.Var fin) loc in
        let cs = List.map (desugar_abstraction state) cs in
        ( add_loc (Untyped.PVar fin) loc
        , add_loc (Untyped.Match (fin_var, cs)) loc )
  in
  ( []
  , { Untyped.effect_clauses= untyped_eff_cs
    ; Untyped.value_clause= untyped_val_a
    ; Untyped.finally_clause= untyped_fin_a } )


and match_constructor st loc t cs =
  (* Separate value and effect cases. *)
  let val_cs, eff_cs = separate_match_cases cs in
  match eff_cs with
  | [] ->
      let val_cs = List.map (desugar_abstraction st) val_cs in
      let w, e = desugar_expression st t in
      (w, Untyped.Match (e, val_cs))
  | _ ->
      let val_cs = List.map (fun cs -> Sugared.Val_match cs) val_cs in
      let x = "$id_par" in
      let value_match = add_loc (Sugared.Match (add_loc (Sugared.Var x) loc, val_cs)) loc in
      let h_value_clause = (add_loc (Sugared.PVar x) loc, value_match) in
      let sugared_h =
        { Sugared.effect_clauses= Assoc.of_list eff_cs
        ; Sugared.value_clause= [h_value_clause]
        ; Sugared.finally_clause= [] }
      in
      let w, h = desugar_handler loc st sugared_h in
      let c = desugar_computation st t in
      let loc_h = Untyped.add_loc (Untyped.Handler h) loc in
      (w, Untyped.Handle (loc_h, c))


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
        Error.syntax ~loc:(loc_of p) "Several definitions of %s" x
    in
    let p_vars, p' = desugar_pattern state p in
    Assoc.iter check_forbidden p_vars ;
    let c' = desugar_computation state c in
    ( {state with context= Assoc.concat p_vars fold_state.context}
    , (p', c') :: defs
    , Assoc.keys_of p_vars @ forbidden )
  in
  let state', defs', _ = List.fold_right aux_desugar defs (state, [], []) in
  (state', defs')


let desugar_top_let_rec state defs =
  let aux_desugar (x, t) (fold_state, ns, forbidden) =
    if List.mem x forbidden then
      Error.syntax ~loc:(loc_of t) "Several definitions of %s" x ;
    let n = fresh_var (Some x) in
    ( {state with context= Assoc.update x n fold_state.context}
    , n :: ns
    , x :: forbidden )
  in
  let state', ns, _ = List.fold_right aux_desugar defs (state, [], []) in
  let desugar_defs (p, (_, c)) defs =
    let c = desugar_let_rec state' c in
    (p, c) :: defs
  in
  let defs' = List.fold_right desugar_defs (List.combine ns defs) [] in
  (state', defs')


let desugar_external state (x, t, f) =
  let n = fresh_var (Some x) in
  let ts = syntax_to_core_params (free_type_params t) in
  ( {state with context= Assoc.update x n state.context}
  , (n, desugar_type ts t, f) )


let desugar_def_effect state (eff, (ty1, ty2)) =
  (eff, (desugar_type Assoc.empty ty1, desugar_type Assoc.empty ty2))
