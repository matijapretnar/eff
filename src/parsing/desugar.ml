(** Desugaring of syntax into the core language. *)

module C = OldUtils
module T = Type
module Sugared = SugaredSyntax
module Untyped = CoreSyntax

type constructor_kind = Variant of bool | Effect of bool

type state =
  { context: (string, Untyped.variable) C.assoc
  ; constructors: (string, constructor_kind) C.assoc }

let initial =
  {context= []; constructors= [(C.cons, Variant true); (C.nil, Variant false)]}


(* ***** Desugaring of types. ***** *)
(* Desugar a type, where only the given type, dirt and region parameters may appear.
   If a type application with missing dirt and region parameters is encountered,
   it uses [ds] and [rs] instead. This is used in desugaring of recursive type definitions
   where we need to figure out which type and dirt parameters are missing in a type defnition.
   Also, it relies on the optional region parameter in [T.Apply] to figure out whether
   an application applies to an effect type. So, it is prudent to call [fill_args] before
   calling [ty].
*)
let ty ts =
  let rec ty (t, loc) =
    match t with
    | Sugared.TyApply (t, tys) ->
        let tys = List.map ty tys in
        T.Apply (t, tys)
    | Sugared.TyParam t -> (
      match C.lookup t ts with
      | None -> Error.syntax ~loc "Unbound type parameter '%s" t
      | Some p -> T.TyParam p )
    | Sugared.TyArrow (t1, t2) -> T.Arrow (ty t1, ty t2)
    | Sugared.TyTuple lst -> T.Tuple (List.map ty lst)
    | Sugared.TyHandler (t1, t2) -> T.Handler {T.value= ty t1; T.finally= ty t2}
  in
  ty


(** [free_params t] returns a triple of all free type, dirt, and region params in [t]. *)
let free_params t =
  let rec ty (t, loc) =
    match t with
    | Sugared.TyApply (_, tys) -> OldUtils.flatten_map ty tys
    | Sugared.TyParam s -> [s]
    | Sugared.TyArrow (t1, t2) -> ty t1 @ ty t2
    | Sugared.TyTuple lst -> OldUtils.flatten_map ty lst
    | Sugared.TyHandler (t1, t2) -> ty t1 @ ty t2
  in
  OldUtils.uniq (ty t)


let syntax_to_core_params ts =
  List.map (fun p -> (p, Type.fresh_ty_param ())) ts


(** [tydef params d] desugars the type definition with parameters [params] and definition [d]. *)
let tydef st params d =
  let sbst = syntax_to_core_params params in
  let st, def =
    match d with
    | Sugared.TyRecord lst ->
        (st, Tctx.Record (List.map (fun (f, t) -> (f, ty sbst t)) lst))
    | Sugared.TySum lst ->
        ( { st with
            constructors=
              C.assoc_map
                (function None -> Variant false | Some _ -> Variant true)
                lst
              @ st.constructors }
        , Tctx.Sum
            (List.map (fun (lbl, t) -> (lbl, C.option_map (ty sbst) t)) lst) )
    | Sugared.TyInline t -> (st, Tctx.Inline (ty sbst t))
  in
  (st, (List.map snd sbst, def))


(** [tydefs defs] desugars the simultaneous type definitions [defs]. *)
let tydefs st defs =
  let st, defs =
    List.fold_left
      (fun (st, defs) (tyname, (ts, def)) ->
        let st, tydef = tydef st ts def in
        (st, (tyname, tydef) :: defs) )
      (st, []) defs
  in
  (st, List.rev defs)


(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_variable ()] creates a fresh variable ["$gen1"], ["$gen2"], ... on
    each call *)
let fresh_variable = function
  | None -> Untyped.Variable.fresh "anon"
  | Some x -> Untyped.Variable.fresh x


let id_abstraction loc =
  let x = fresh_variable (Some "$id_par") in
  ( Untyped.add_loc (Untyped.PVar x) loc
  , Untyped.add_loc (Untyped.Value (Untyped.add_loc (Untyped.Var x) loc)) loc
  )


let pattern st ?(forbidden= []) (p, loc) =
  let vars = ref [] in
  let forbidden = ref forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~loc "Variable %s occurs more than once in a pattern" x
    else
      let var = fresh_variable (Some x) in
      vars := (x, var) :: !vars ;
      forbidden := x :: !forbidden ;
      var
  in
  let rec pattern st (p, loc) =
    let p =
      match p with
      | Sugared.PVar x ->
          let x = new_var x in
          Untyped.PVar x
      | Sugared.PAs (p, x) ->
          let x = new_var x in
          let p' = pattern st p in
          Untyped.PAs (p', x)
      | Sugared.PTuple ps -> Untyped.PTuple (List.map (pattern st) ps)
      | Sugared.PRecord flds ->
          Untyped.PRecord (OldUtils.assoc_map (pattern st) flds)
      | Sugared.PVariant (lbl, p) -> (
        match C.lookup lbl st.constructors with
        | None -> Error.typing ~loc "Unbound constructor %s" lbl
        | Some Variant var ->
          match (var, p) with
          | true, Some p -> Untyped.PVariant (lbl, Some (pattern st p))
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
    {Untyped.term= p; Untyped.location= loc}
  in
  let p = pattern st (p, loc) in
  (!vars, p)


(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec expression st (t, loc) =
  let w, e =
    match t with
    | Sugared.Var x -> (
      match OldUtils.lookup x st.context with
      | Some n -> ([], Untyped.Var n)
      | None -> Error.typing ~loc "Unknown variable %s" x )
    | Sugared.Const k -> ([], Untyped.Const k)
    | Sugared.Lambda a ->
        let a = abstraction st a in
        ([], Untyped.Lambda a)
    | Sugared.Function cs ->
        let x = fresh_variable (Some "$function") in
        let cs = List.map (abstraction st) cs in
        ( []
        , Untyped.Lambda
            ( Untyped.add_loc (Untyped.PVar x) loc
            , Untyped.add_loc
                (Untyped.Match (Untyped.add_loc (Untyped.Var x) loc, cs)) loc
            ) )
    | Sugared.Handler cs ->
        let w, h = handler loc st cs in
        (w, Untyped.Handler h)
    | Sugared.Tuple ts ->
        let w, es = expressions st ts in
        (w, Untyped.Tuple es)
    | Sugared.Record ts ->
        if not (C.injective fst ts) then
          Error.syntax ~loc "Fields in a record must be distinct" ;
        let w, es = record_expressions st ts in
        (w, Untyped.Record es)
    | Sugared.Variant (lbl, t) -> (
      match C.lookup lbl st.constructors with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some Variant var ->
        match (var, t) with
        | true, Some t ->
            let w, e = expression st t in
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
        let x = fresh_variable (Some "$bind") in
        let c = computation st (t, loc) in
        let w = [(Untyped.add_loc (Untyped.PVar x) loc, c)] in
        (w, Untyped.Var x)
  in
  (w, Untyped.add_loc e loc)


and computation st (t, loc) =
  let if_then_else e c1 c2 =
    Untyped.Match
      ( e
      , [ ( Untyped.add_loc (Untyped.PConst Const.of_true) c1.Untyped.location
          , c1 )
        ; ( Untyped.add_loc (Untyped.PConst Const.of_false) c2.Untyped.location
          , c2 ) ] )
  in
  let w, c =
    match t with
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "&&", loc1), t1), loc2), t2) ->
        let w1, e1 = expression st t1 in
        let c2 = computation st t2 in
        ( w1
        , if_then_else e1 c2
            (Untyped.add_loc
               (Untyped.Value
                  (Untyped.add_loc (Untyped.Const Const.of_false) loc2))
               loc2) )
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "||", loc1), t1), loc2), t2) ->
        let w1, e1 = expression st t1 in
        let c2 = computation st t2 in
        ( w1
        , if_then_else e1
            (Untyped.add_loc
               (Untyped.Value
                  (Untyped.add_loc (Untyped.Const Const.of_true) loc2))
               loc2)
            c2 )
    | Sugared.Apply (t1, t2) ->
        let w1, e1 = expression st t1 in
        let w2, e2 = expression st t2 in
        (w1 @ w2, Untyped.Apply (e1, e2))
    | Sugared.Effect (eff, t) ->
        let w, e = expression st t in
        let loc_eff = Untyped.add_loc (Untyped.Effect eff) loc in
        (w, Untyped.Apply (loc_eff, e))
    | Sugared.Match (t, cs) -> match_constructor st loc t cs
    | Sugared.Handle (t1, t2) ->
        let w1, e1 = expression st t1 in
        let c2 = computation st t2 in
        (w1, Untyped.Handle (e1, c2))
    | Sugared.Conditional (t, t1, t2) ->
        let w, e = expression st t in
        let c1 = computation st t1 in
        let c2 = computation st t2 in
        (w, if_then_else e c1 c2)
    | Sugared.Check t -> ([], Untyped.Check (computation st t))
    | Sugared.Let (defs, t) ->
        let st', defs, _ =
          List.fold_right
            (fun (p, c) (st', defs, forbidden) ->
              let check_forbidden (x, _) =
                if List.mem x forbidden then
                  Error.syntax ~loc:(snd p) "Several definitions of %s" x
              in
              let p_vars, p = pattern st p in
              List.iter check_forbidden p_vars ;
              let c = computation st c in
              ( {st with context= p_vars @ st'.context}
              , (p, c) :: defs
              , List.map fst p_vars @ forbidden ) )
            defs (st, [], [])
        in
        let c = computation st' t in
        ([], Untyped.Let (defs, c))
    | Sugared.LetRec (defs, t) ->
        let st', ns, _ =
          List.fold_right
            (fun (x, t) (st', ns, forbidden) ->
              if List.mem x forbidden then
                Error.syntax ~loc:(snd t) "Several definitions of %s" x ;
              let n = fresh_variable (Some x) in
              ( {st with context= (x, n) :: st'.context}
              , n :: ns
              , x :: forbidden ) )
            defs (st, [], [])
        in
        let defs =
          List.fold_right
            (fun (p, (_, c)) defs ->
              let c = let_rec st' c in
              (p, c) :: defs )
            (List.combine ns defs) []
        in
        let c = computation st' t in
        ([], Untyped.LetRec (defs, c))
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | Sugared.Var _ | Sugared.Const _ | Sugared.Tuple _ | Sugared.Record _
     |Sugared.Variant _ | Sugared.Lambda _ | Sugared.Function _
     |Sugared.Handler _ ->
        let w, e = expression st (t, loc) in
        (w, Untyped.Value e)
  in
  match w with
  | [] -> Untyped.add_loc c loc
  | _ :: _ -> Untyped.add_loc (Untyped.Let (w, Untyped.add_loc c loc)) loc


and abstraction st (p, t) =
  let vars, p = pattern st p in
  (p, computation {st with context= vars @ st.context} t)


and abstraction2 st (p1, p2, t) =
  let vars1, p1 = pattern st p1 in
  let vars2, p2 = pattern st p2 in
  (p1, p2, computation {st with context= vars1 @ vars2 @ st.context} t)


and let_rec st (e, loc) =
  match e with
  | Sugared.Lambda a -> abstraction st a
  | Sugared.Function cs ->
      let x = fresh_variable (Some "$let_rec_function") in
      let cs = List.map (abstraction st) cs in
      ( Untyped.add_loc (Untyped.PVar x) loc
      , Untyped.add_loc
          (Untyped.Match (Untyped.add_loc (Untyped.Var x) loc, cs)) loc )
  | _ ->
      Error.syntax ~loc
        "This kind of expression is not allowed in a recursive definition"


and expressions st = function
  | [] -> ([], [])
  | t :: ts ->
      let w, e = expression st t in
      let ws, es = expressions st ts in
      (w @ ws, e :: es)


and record_expressions st = function
  | [] -> ([], [])
  | (f, t) :: ts ->
      let w, e = expression st t in
      let ws, es = record_expressions st ts in
      (w @ ws, (f, e) :: es)


and handler loc st
    { Sugared.effect_clauses= eff_cs
    ; Sugared.value_clause= val_cs
    ; Sugared.finally_clause= fin_cs } =
  (* Construct a handler with match statements. *)
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
        let x = fresh_variable (Some "$eff_param") in
        let x_var = Untyped.add_loc (Untyped.Var x) loc in
        let k = fresh_variable (Some "$continuation") in
        let k_var = Untyped.add_loc (Untyped.Var k) loc in
        let match_cs =
          List.map
            (fun (p1, p2, t) ->
              let vars1, p1 = pattern st p1 in
              let vars2, p2 = pattern st p2 in
              let t =
                computation {st with context= vars1 @ vars2 @ st.context} t
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
        let v = fresh_variable (Some "$val_param") in
        let v_var = Untyped.add_loc (Untyped.Var v) loc in
        let cs = List.map (abstraction st) cs in
        ( Untyped.add_loc (Untyped.PVar v) loc
        , Untyped.add_loc (Untyped.Match (v_var, cs)) loc )
  in
  let untyped_fin_a =
    match fin_cs with
    | [] -> id_abstraction loc
    | cs ->
        let fin = fresh_variable (Some "$fin_param") in
        let fin_var = Untyped.add_loc (Untyped.Var fin) loc in
        let cs = List.map (abstraction st) cs in
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
      let val_cs = List.map (abstraction st) val_cs in
      let w, e = expression st t in
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
      let w, h = handler loc st sugared_h in
      let c = computation st t in
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
        let p_vars, p = pattern st p in
        List.iter check_forbidden p_vars ;
        let c = computation st c in
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
        let n = fresh_variable (Some x) in
        ({st with context= (x, n) :: st'.context}, n :: ns, x :: forbidden) )
      defs (st, [], [])
  in
  let defs =
    List.fold_right
      (fun (p, (_, c)) defs ->
        let c = let_rec st' c in
        (p, c) :: defs )
      (List.combine ns defs) []
  in
  (st', defs)


let external_ty st x t =
  let n = fresh_variable (Some x) in
  let ts = syntax_to_core_params (free_params t) in
  ({st with context= (x, n) :: st.context}, (n, ty ts t))


let rec toplevel st (cmd, loc) =
  let st', cmd = plain_toplevel st cmd in
  (st', {Untyped.term= cmd; Untyped.location= loc})

and plain_toplevel st = function
  | Sugared.Tydef defs ->
      let st, defs = tydefs st defs in
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
      (st, Untyped.DefEffect (eff, (ty [] ty1, ty [] ty2)))
  | Sugared.Term t ->
      let c = computation st t in
      (st, Untyped.Computation c)
  | Sugared.Use filename -> (st, Untyped.Use filename)
  | Sugared.Reset -> (st, Untyped.Reset)
  | Sugared.Help -> (st, Untyped.Help)
  | Sugared.Quit -> (st, Untyped.Quit)
  | Sugared.TypeOf t ->
      let c = computation st t in
      (st, Untyped.TypeOf c)
