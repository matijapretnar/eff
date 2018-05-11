(** Desugaring of syntax into the core language. *)

module Utils = OldUtils
module T = Type
module Sugared = SugaredSyntax
module Untyped = CoreSyntax

type constructor_kind = Variant of bool | Effect of bool

type state =
  { context: (string, Untyped.variable) Utils.assoc
  ; constructors: (string, constructor_kind) Utils.assoc }

let initial_state =
  {context= []; constructors= [(Utils.cons, Variant true); (Utils.nil, Variant false)]}

let add_loc = Untyped.add_loc

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
  let rec desugar_type (t, loc) =
    match t with
    | Sugared.TyApply (t, tys) ->
        let tys' = List.map desugar_type tys in
        T.Apply (t, tys')
    | Sugared.TyParam t -> (
      match Utils.lookup t type_sbst with
      | None -> Error.syntax ~loc "Unbound type parameter '%s" t
      | Some p -> T.TyParam p )
    | Sugared.TyArrow (t1, t2) -> T.Arrow (desugar_type t1, desugar_type t2)
    | Sugared.TyTuple lst -> T.Tuple (List.map desugar_type lst)
    | Sugared.TyHandler (t1, t2) -> T.Handler {T.value= desugar_type t1; T.finally= desugar_type t2}
  in
  desugar_type


(** [free_type_params t] returns all free type params in [t]. *)
let free_type_params t =
  let rec ty_params (t, loc) =
    match t with
    | Sugared.TyApply (_, tys) -> OldUtils.flatten_map ty_params tys
    | Sugared.TyParam s -> [s]
    | Sugared.TyArrow (t1, t2) -> ty_params t1 @ ty_params t2
    | Sugared.TyTuple lst -> OldUtils.flatten_map ty_params lst
    | Sugared.TyHandler (t1, t2) -> ty_params t1 @ ty_params t2
  in
  OldUtils.uniq (ty_params t)


let syntax_to_core_params ts =
  List.map (fun p -> (p, Type.fresh_ty_param ())) ts


(** [desugar_tydef state params def] desugars the type definition with parameters
    [params] and definition [def]. *)
let desugar_tydef state params def =
  let ty_sbst = syntax_to_core_params params in
  let state', def' =
    match def with
    | Sugared.TyRecord lst ->
        (state, Tctx.Record (List.map (fun (f, t) -> (f, desugar_type ty_sbst t)) lst))
    | Sugared.TySum lst ->
        let lbl_desugar (lbl, t) = (lbl, Utils.option_map (desugar_type ty_sbst) t) in
        let new_constructors =
          Utils.assoc_map (function None -> Variant false | Some _ -> Variant true) lst
        in
        ( { state with constructors= new_constructors @ state.constructors }
        , Tctx.Sum (List.map lbl_desugar lst) )
    | Sugared.TyInline t -> (state, Tctx.Inline (desugar_type ty_sbst t))
  in
  (state', (List.map snd ty_sbst, def'))


(** [desugar_tydefs defs] desugars the simultaneous type definitions [defs]. *)
let desugar_tydefs state sugared_defs =
  let desugar_fold (state, defs) (tyname, (params, def)) =
    let state', tydef' = desugar_tydef state params def in
    (state', (tyname, tydef') :: defs)
  in
  let state', defs' = List.fold_left desugar_fold (state, []) sugared_defs in
  (state', List.rev defs')


(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_var opt] creates a fresh variable on each call *)
let fresh_var = function
  | None -> Untyped.Variable.fresh "anon"
  | Some x -> Untyped.Variable.fresh x


let id_abstraction loc =
  let x = fresh_var (Some "$id_par") in
  ( add_loc (Untyped.PVar x) loc
  , add_loc (Untyped.Value (add_loc (Untyped.Var x) loc)) loc)


let pvars_desugar_pattern state ?(initial_forbidden= []) (p, loc) =
  let vars = ref [] in
  let forbidden = ref initial_forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~loc "Variable %s occurs more than once in a pattern" x
    else
      let var = fresh_var (Some x) in
      vars := (x, var) :: !vars ;
      forbidden := x :: !forbidden ;
      var
  in
  let rec desugar_pattern state (p, loc) =
    let p =
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
          Untyped.PRecord (OldUtils.assoc_map (desugar_pattern state) flds)
      | Sugared.PVariant (lbl, p) -> (
        match Utils.lookup lbl state.constructors with
        | None -> Error.typing ~loc "Unbound constructor %s" lbl
        | Some Variant var ->
          match (var, p) with
          | true, Some p ->
              Untyped.PVariant (lbl, Some (desugar_pattern state p))
          | false, None ->
              Untyped.PVariant (lbl, None)
          | true, None ->
              Error.typing ~loc
                "Constructor %s should be applied to an argument." lbl
          | false, Some _ ->
              Error.typing ~loc
                "Constructor %s cannot be applied to an argument." lbl )
      | Sugared.PConst c -> Untyped.PConst c
      | Sugared.PNonbinding -> Untyped.PNonbinding
    in
    add_loc p loc
  in
  let p = desugar_pattern state (p, loc) in
  (!vars, p)


(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec desugar_expression state (t, loc) =
  let w, e =
    match t with
    | Sugared.Var x -> (
      match OldUtils.lookup x state.context with
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
            , add_loc (Untyped.Match (add_loc (Untyped.Var x) loc, cs)) loc)
         )
    | Sugared.Handler cs ->
        let w, h = desugar_handler loc state cs in
        (w, Untyped.Handler h)
    | Sugared.Tuple ts ->
        let w, es = desugar_expressions state ts in
        (w, Untyped.Tuple es)
    | Sugared.Record ts ->
        if not (Utils.injective fst ts) then
          Error.syntax ~loc "Fields in a record must be distinct" ;
        let w, es = desugar_record_expressions state ts in
        (w, Untyped.Record es)
    | Sugared.Variant (lbl, t) -> (
      match Utils.lookup lbl state.constructors with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some (Variant var) ->
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
        let c = desugar_computation state (t, loc) in
        let w = [(add_loc (Untyped.PVar x) loc, c)] in
        (w, Untyped.Var x)
  in
  (w, add_loc e loc)


and desugar_computation state (t, loc) =
  let if_then_else e c1 c2 =
    let true_p = add_loc (Untyped.PConst Const.of_true) c1.Untyped.location in
    let false_p = add_loc (Untyped.PConst Const.of_false) c2.Untyped.location in
    Untyped.Match (e, [(true_p, c1); (false_p, c2 )])
  in
  let w, c =
    match t with
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "&&", loc1), t1), loc2), t2) ->
        let w1, e1 = desugar_expression state t1 in
        let untyped_false loc = add_loc (Untyped.Const Const.of_false) loc in
        let c1 = desugar_computation state t2 in
        let c2 = (add_loc (Untyped.Value (untyped_false loc2)) loc2) in
        (w1, if_then_else e1 c1 c2)
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "||", loc1), t1), loc2), t2) ->
        let w1, e1 = desugar_expression state t1 in
        let untyped_true loc = add_loc (Untyped.Const Const.of_true) loc in
        let c1 = (add_loc (Untyped.Value (untyped_true loc2)) loc2) in
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
        let check_and_desugar (p, c) (fold_state, defs, forbidden) =
          let check_forbidden (x, _) =
            if List.mem x forbidden then
              Error.syntax ~loc:(snd p) "Several definitions of %s" x
          in
          let p_vars, p' = pvars_desugar_pattern state p in
          List.iter check_forbidden p_vars ;
          let c' = desugar_computation state c in
          ( {state with context= p_vars @ fold_state.context}
          , (p', c') :: defs
          , List.map fst p_vars @ forbidden )
        in
        let state', defs', _ =
          List.fold_right check_and_desugar defs (state, [], [])
        in
        let c = desugar_computation state' t in
        ([], Untyped.Let (defs', c))
    | Sugared.LetRec (defs, t) ->
        let check_and_desugar (x, t) (fold_state, ns, forbidden) =
          if List.mem x forbidden then
            Error.syntax ~loc:(snd t) "Several definitions of %s" x ;
          let n = fresh_var (Some x) in
          ( {state with context= (x, n) :: fold_state.context}
          , n :: ns
          , x :: forbidden )
        in
        let state', ns, _ =
          List.fold_right check_and_desugar defs (state, [], [])
        in
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
        let w, e = desugar_expression state (t, loc) in
        (w, Untyped.Value e)
  in
  match w with
  | [] -> add_loc c loc
  | _ :: _ -> add_loc (Untyped.Let (w, add_loc c loc)) loc


and desugar_abstraction st (p, t) =
  let vars, p = pvars_desugar_pattern st p in
  (p, desugar_computation {st with context= vars @ st.context} t)


and abstraction2 st (p1, p2, t) =
  let vars1, p1 = pvars_desugar_pattern st p1 in
  let vars2, p2 = pvars_desugar_pattern st p2 in
  (p1, p2, desugar_computation {st with context= vars1 @ vars2 @ st.context} t)


and desugar_let_rec st (e, loc) =
  match e with
  | Sugared.Lambda a -> desugar_abstraction st a
  | Sugared.Function cs ->
      let x = fresh_var (Some "$let_rec_function") in
      let cs = List.map (desugar_abstraction st) cs in
      ( Untyped.add_loc (Untyped.PVar x) loc
      , Untyped.add_loc
          (Untyped.Match (Untyped.add_loc (Untyped.Var x) loc, cs)) loc )
  | _ ->
      Error.syntax ~loc
        "This kind of expression is not allowed in a recursive definition"


and desugar_expressions st = function
  | [] -> ([], [])
  | t :: ts ->
      let w, e = desugar_expression st t in
      let ws, es = desugar_expressions st ts in
      (w @ ws, e :: es)


and desugar_record_expressions st = function
  | [] -> ([], [])
  | (f, t) :: ts ->
      let w, e = desugar_expression st t in
      let ws, es = desugar_record_expressions st ts in
      (w @ ws, (f, e) :: es)


and desugar_handler loc st
    { Sugared.effect_clauses= eff_cs
    ; Sugared.value_clause= val_cs
    ; Sugared.finally_clause= fin_cs } =
  (* Construct a desugared handler with match statements. *)
  let rec group_eff_cs (eff, a2) = function
    | [] -> [(eff, [a2])]
    | (e, a2s) :: tl ->
        if e = eff then (e, a2 :: a2s) :: tl
        else (e, a2s) :: group_eff_cs (eff, a2) tl
  in
  let rec construct_eff_clause (eff, eff_cs_lst) =
    match eff_cs_lst with
    | [] -> assert false
    | [a2] -> (eff, abstraction2 st a2)
    | a2s ->
        let x = fresh_var (Some "$eff_param") in
        let x_var = Untyped.add_loc (Untyped.Var x) loc in
        let k = fresh_var (Some "$continuation") in
        let k_var = Untyped.add_loc (Untyped.Var k) loc in
        let match_cs =
          List.map
            (fun (p1, p2, t) ->
              let vars1, p1 = pvars_desugar_pattern st p1 in
              let vars2, p2 = pvars_desugar_pattern st p2 in
              let t =
                desugar_computation {st with context= vars1 @ vars2 @ st.context} t
              in
              (Untyped.add_loc (Untyped.PTuple [p1; p2]) loc, t) )
            a2s
        in
        let match_term =
          Untyped.add_loc
            (Untyped.Match
               (Untyped.add_loc (Untyped.Tuple [x_var; k_var]) loc, match_cs))
            loc
        in
        ( eff
        , ( Untyped.add_loc (Untyped.PVar x) loc
          , Untyped.add_loc (Untyped.PVar k) loc
          , match_term ) )
  in
  let collected_eff_cs = List.fold_right group_eff_cs eff_cs [] in
  let untyped_eff_cs = List.map construct_eff_clause collected_eff_cs in
  let untyped_val_a =
    match val_cs with
    | [] -> id_abstraction loc
    | cs ->
        let v = fresh_var (Some "$val_param") in
        let v_var = Untyped.add_loc (Untyped.Var v) loc in
        let cs = List.map (desugar_abstraction st) cs in
        ( Untyped.add_loc (Untyped.PVar v) loc
        , Untyped.add_loc (Untyped.Match (v_var, cs)) loc )
  in
  let untyped_fin_a =
    match fin_cs with
    | [] -> id_abstraction loc
    | cs ->
        let fin = fresh_var (Some "$fin_param") in
        let fin_var = Untyped.add_loc (Untyped.Var fin) loc in
        let cs = List.map (desugar_abstraction st) cs in
        ( Untyped.add_loc (Untyped.PVar fin) loc
        , Untyped.add_loc (Untyped.Match (fin_var, cs)) loc )
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
      let value_match = (Sugared.Match ((Sugared.Var x, loc), val_cs), loc) in
      let h_value_clause = ((Sugared.PVar x, loc), value_match) in
      let sugared_h =
        { Sugared.effect_clauses= eff_cs
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


let top_let st defs =
  let st', defs, _ =
    List.fold_right
      (fun (p, c) (st', defs, forbidden) ->
        let check_forbidden (x, _) =
          if List.mem x forbidden then
            Error.syntax ~loc:(snd p) "Several definitions of %s" x
        in
        let p_vars, p = pvars_desugar_pattern st p in
        List.iter check_forbidden p_vars ;
        let c = desugar_computation st c in
        ( {st with context= p_vars @ st'.context}
        , (p, c) :: defs
        , List.map fst p_vars @ forbidden ) )
      defs (st, [], [])
  in
  (st', defs)


let top_let_rec st defs =
  let st', ns, _ =
    List.fold_right
      (fun (x, t) (st', ns, forbidden) ->
        if List.mem x forbidden then
          Error.syntax ~loc:(snd t) "Several definitions of %s" x ;
        let n = fresh_var (Some x) in
        ({st with context= (x, n) :: st'.context}, n :: ns, x :: forbidden) )
      defs (st, [], [])
  in
  let defs =
    List.fold_right
      (fun (p, (_, c)) defs ->
        let c = desugar_let_rec st' c in
        (p, c) :: defs )
      (List.combine ns defs) []
  in
  (st', defs)


let external_ty st x t =
  let n = fresh_var (Some x) in
  let ts = syntax_to_core_params (free_type_params t) in
  ({st with context= (x, n) :: st.context}, (n, desugar_type ts t))


let rec toplevel st (cmd, loc) =
  let st', cmd = plain_toplevel st cmd in
  (st', {Untyped.term= cmd; Untyped.location= loc})


and plain_toplevel st = function
  | Sugared.Tydef defs ->
      let st, defs = desugar_tydefs st defs in
      (st, Untyped.Tydef defs)
  | Sugared.TopLet defs ->
      let st, defs = top_let st defs in
      (st, Untyped.TopLet defs)
  | Sugared.TopLetRec defs ->
      let st, defs = top_let_rec st defs in
      (st, Untyped.TopLetRec defs)
  | Sugared.External (x, ty, y) ->
      let st, (x, ty) = external_ty st x ty in
      (st, Untyped.External (x, ty, y))
  | Sugared.DefEffect (eff, (ty1, ty2)) ->
      (st, Untyped.DefEffect (eff, (desugar_type [] ty1, desugar_type [] ty2)))
  | Sugared.Term t ->
      let c = desugar_computation st t in
      (st, Untyped.Computation c)
  | Sugared.Use filename -> (st, Untyped.Use filename)
  | Sugared.Reset -> (st, Untyped.Reset)
  | Sugared.Help -> (st, Untyped.Help)
  | Sugared.Quit -> (st, Untyped.Quit)
  | Sugared.TypeOf t ->
      let c = desugar_computation st t in
      (st, Untyped.TypeOf c)


let desugar_commands state sugared_cmds =
  CoreUtils.fold_map toplevel state sugared_cmds
