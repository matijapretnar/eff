(** Desugaring of syntax into the core language. *)

module C = OldUtils
module T = Type
module Sugared = SugaredSyntax
module Untyped = CoreSyntax

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
let tydef params d =
  let sbst = syntax_to_core_params params in
  ( List.map snd sbst
  , match d with
    | Sugared.TyRecord lst ->
        Tctx.Record (List.map (fun (f, t) -> (f, ty sbst t)) lst)
    | Sugared.TySum lst ->
        Tctx.Sum
          (List.map (fun (lbl, t) -> (lbl, C.option_map (ty sbst) t)) lst)
    | Sugared.TyInline t -> Tctx.Inline (ty sbst t) )


(** [tydefs defs] desugars the simultaneous type definitions [defs]. *)
let tydefs defs =
  List.map (fun (tyname, (ts, def)) -> (tyname, tydef ts def)) defs


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


let pattern ?(forbidden= []) (p, loc) =
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
  let rec pattern (p, loc) =
    let p =
      match p with
      | Sugared.PVar x ->
          let x = new_var x in
          Untyped.PVar x
      | Sugared.PAs (p, x) ->
          let x = new_var x in
          let p' = pattern p in
          Untyped.PAs (p', x)
      | Sugared.PTuple ps -> Untyped.PTuple (List.map pattern ps)
      | Sugared.PRecord flds ->
          Untyped.PRecord (OldUtils.assoc_map pattern flds)
      | Sugared.PVariant (lbl, p) ->
          Untyped.PVariant (lbl, OldUtils.option_map pattern p)
      | Sugared.PConst c -> Untyped.PConst c
      | Sugared.PNonbinding -> Untyped.PNonbinding
    in
    {Untyped.term= p; Untyped.location= loc}
  in
  let p = pattern (p, loc) in
  (!vars, p)


(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec expression ctx (t, loc) =
  let w, e =
    match t with
    | Sugared.Var x -> (
      match OldUtils.lookup x ctx with
      | Some n -> ([], Untyped.Var n)
      | None -> Error.typing ~loc "Unknown variable %s" x )
    | Sugared.Const k -> ([], Untyped.Const k)
    | Sugared.Lambda a ->
        let a = abstraction ctx a in
        ([], Untyped.Lambda a)
    | Sugared.Function cs ->
        let x = fresh_variable (Some "$function") in
        let cs = List.map (abstraction ctx) cs in
        ( []
        , Untyped.Lambda
            ( Untyped.add_loc (Untyped.PVar x) loc
            , Untyped.add_loc
                (Untyped.Match (Untyped.add_loc (Untyped.Var x) loc, cs)) loc
            ) )
    | Sugared.Handler cs ->
        let w, h = handler loc ctx cs in
        (w, Untyped.Handler h)
    | Sugared.Tuple ts ->
        let w, es = expressions ctx ts in
        (w, Untyped.Tuple es)
    | Sugared.Record ts ->
        if not (C.injective fst ts) then
          Error.syntax ~loc "Fields in a record must be distinct" ;
        let w, es = record_expressions ctx ts in
        (w, Untyped.Record es)
    | Sugared.Variant (lbl, None) -> ([], Untyped.Variant (lbl, None))
    | Sugared.Variant (lbl, Some t) ->
        let w, e = expression ctx t in
        (w, Untyped.Variant (lbl, Some e))
    | Sugared.Effect eff -> ([], Untyped.Effect eff)
    (* Terms that are desugared into computations. We list them explicitly in
     order to catch any future constructs. *)
    | Sugared.Apply _ | Sugared.Match _ | Sugared.Let _ | Sugared.LetRec _
     |Sugared.Handle _ | Sugared.Conditional _ | Sugared.Check _ ->
        let x = fresh_variable (Some "$bind") in
        let c = computation ctx (t, loc) in
        let w = [(Untyped.add_loc (Untyped.PVar x) loc, c)] in
        (w, Untyped.Var x)
  in
  (w, Untyped.add_loc e loc)


and computation ctx (t, loc) =
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
        let w1, e1 = expression ctx t1 in
        let c2 = computation ctx t2 in
        ( w1
        , if_then_else e1 c2
            (Untyped.add_loc
               (Untyped.Value
                  (Untyped.add_loc (Untyped.Const Const.of_false) loc2))
               loc2) )
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "||", loc1), t1), loc2), t2) ->
        let w1, e1 = expression ctx t1 in
        let c2 = computation ctx t2 in
        ( w1
        , if_then_else e1
            (Untyped.add_loc
               (Untyped.Value
                  (Untyped.add_loc (Untyped.Const Const.of_true) loc2))
               loc2)
            c2 )
    | Sugared.Apply (t1, t2) ->
        let w1, e1 = expression ctx t1 in
        let w2, e2 = expression ctx t2 in
        (w1 @ w2, Untyped.Apply (e1, e2))
    | Sugared.Match (t, cs) ->
        let cs = List.map (abstraction ctx) cs in
        let w, e = expression ctx t in
        (w, Untyped.Match (e, cs))
    | Sugared.Handle (t1, t2) ->
        let w1, e1 = expression ctx t1 in
        let c2 = computation ctx t2 in
        (w1, Untyped.Handle (e1, c2))
    | Sugared.Conditional (t, t1, t2) ->
        let w, e = expression ctx t in
        let c1 = computation ctx t1 in
        let c2 = computation ctx t2 in
        (w, if_then_else e c1 c2)
    | Sugared.Check t -> ([], Untyped.Check (computation ctx t))
    | Sugared.Let (defs, t) ->
        let ctx', defs, _ =
          List.fold_right
            (fun (p, c) (ctx', defs, forbidden) ->
              let check_forbidden (x, _) =
                if List.mem x forbidden then
                  Error.syntax ~loc:(snd p) "Several definitions of %s" x
              in
              let p_vars, p = pattern p in
              List.iter check_forbidden p_vars ;
              let c = computation ctx c in
              (p_vars @ ctx', (p, c) :: defs, List.map fst p_vars @ forbidden)
              )
            defs (ctx, [], [])
        in
        let c = computation ctx' t in
        ([], Untyped.Let (defs, c))
    | Sugared.LetRec (defs, t) ->
        let ctx', ns, _ =
          List.fold_right
            (fun (x, t) (ctx', ns, forbidden) ->
              if List.mem x forbidden then
                Error.syntax ~loc:(snd t) "Several definitions of %s" x ;
              let n = fresh_variable (Some x) in
              ((x, n) :: ctx', n :: ns, x :: forbidden) )
            defs (ctx, [], [])
        in
        let defs =
          List.fold_right
            (fun (p, (_, c)) defs ->
              let c = let_rec ctx' c in
              (p, c) :: defs )
            (List.combine ns defs) []
        in
        let c = computation ctx' t in
        ([], Untyped.LetRec (defs, c))
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | Sugared.Var _ | Sugared.Const _ | Sugared.Tuple _ | Sugared.Record _
     |Sugared.Variant _ | Sugared.Lambda _ | Sugared.Function _
     |Sugared.Handler _ | Sugared.Effect _ ->
        let w, e = expression ctx (t, loc) in
        (w, Untyped.Value e)
  in
  match w with
  | [] -> Untyped.add_loc c loc
  | _ :: _ -> Untyped.add_loc (Untyped.Let (w, Untyped.add_loc c loc)) loc


and abstraction ctx (p, t) =
  let vars, p = pattern p in
  (p, computation (vars @ ctx) t)


and abstraction2 ctx (p1, p2, t) =
  let vars1, p1 = pattern p1 in
  let vars2, p2 = pattern p2 in
  (p1, p2, computation (vars1 @ vars2 @ ctx) t)


and let_rec ctx (e, loc) =
  match e with
  | Sugared.Lambda a -> abstraction ctx a
  | Sugared.Function cs ->
      let x = fresh_variable (Some "$let_rec_function") in
      let cs = List.map (abstraction ctx) cs in
      ( Untyped.add_loc (Untyped.PVar x) loc
      , Untyped.add_loc
          (Untyped.Match (Untyped.add_loc (Untyped.Var x) loc, cs)) loc )
  | _ ->
      Error.syntax ~loc
        "This kind of expression is not allowed in a recursive definition"


and expressions ctx = function
  | [] -> ([], [])
  | t :: ts ->
      let w, e = expression ctx t in
      let ws, es = expressions ctx ts in
      (w @ ws, e :: es)


and record_expressions ctx = function
  | [] -> ([], [])
  | (f, t) :: ts ->
      let w, e = expression ctx t in
      let ws, es = record_expressions ctx ts in
      (w @ ws, (f, e) :: es)


and handler loc ctx
    { Sugared.effect_clauses= ops
    ; Sugared.value_clause= val_a
    ; Sugared.finally_clause= fin_a } =
  let rec operation_cases = function
    | [] -> []
    | (op, a2) :: cs ->
        let cs' = operation_cases cs in
        (op, abstraction2 ctx a2) :: cs'
  in
  let ops = operation_cases ops in
  ( []
  , { Untyped.effect_clauses= ops
    ; Untyped.value_clause=
        ( match val_a with
        | None -> id_abstraction loc
        | Some a -> abstraction ctx a )
    ; Untyped.finally_clause=
        ( match fin_a with
        | None -> id_abstraction loc
        | Some a -> abstraction ctx a ) } )


let top_ctx = ref []

let top_let defs =
  let ctx', defs, _ =
    List.fold_right
      (fun (p, c) (ctx', defs, forbidden) ->
        let check_forbidden (x, _) =
          if List.mem x forbidden then
            Error.syntax ~loc:(snd p) "Several definitions of %s" x
        in
        let p_vars, p = pattern p in
        List.iter check_forbidden p_vars ;
        let c = computation !top_ctx c in
        (p_vars @ ctx', (p, c) :: defs, List.map fst p_vars @ forbidden) )
      defs (!top_ctx, [], [])
  in
  top_ctx := ctx' ;
  defs


let top_let_rec defs =
  let ctx', ns, _ =
    List.fold_right
      (fun (x, t) (ctx', ns, forbidden) ->
        if List.mem x forbidden then
          Error.syntax ~loc:(snd t) "Several definitions of %s" x ;
        let n = fresh_variable (Some x) in
        ((x, n) :: ctx', n :: ns, x :: forbidden) )
      defs (!top_ctx, [], [])
  in
  let defs =
    List.fold_right
      (fun (p, (_, c)) defs ->
        let c = let_rec ctx' c in
        (p, c) :: defs )
      (List.combine ns defs) []
  in
  top_ctx := ctx' ;
  defs


let external_ty x t =
  let n = fresh_variable (Some x) in
  top_ctx := (x, n) :: !top_ctx ;
  let ts = syntax_to_core_params (free_params t) in
  (n, ty ts t)


let top_computation c = computation !top_ctx c

let rec toplevel (cmd, loc) =
  {Untyped.term= plain_toplevel cmd; Untyped.location= loc}

and plain_toplevel = function
  | Sugared.Tydef defs -> Untyped.Tydef (tydefs defs)
  | Sugared.TopLet defs ->
      let defs = top_let defs in
      Untyped.TopLet defs
  | Sugared.TopLetRec defs ->
      let defs = top_let_rec defs in
      Untyped.TopLetRec defs
  | Sugared.External (x, ty, y) ->
      let x, ty = external_ty x ty in
      Untyped.External (x, ty, y)
  | Sugared.DefEffect (eff, (ty1, ty2)) ->
      Untyped.DefEffect (eff, (ty [] ty1, ty [] ty2))
  | Sugared.Term t ->
      let c = top_computation t in
      Untyped.Computation c
  | Sugared.Use filename -> Untyped.Use filename
  | Sugared.Reset -> Untyped.Reset
  | Sugared.Help -> Untyped.Help
  | Sugared.Quit -> Untyped.Quit
  | Sugared.TypeOf t ->
      let c = top_computation t in
      Untyped.TypeOf c
