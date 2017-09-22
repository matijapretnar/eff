(** Desugaring of syntax into the core language. *)

module C = Common
module T = Type

(* ***** Desugaring of types. ***** *)

let fresh_dirt_param = Common.fresh (fun n -> Sugared.DirtParam n)

(* Fill in missing dirt and region parameters in a type with fresh ones. Also resolves
   type applications so that applications of effect types are equipped with the extra region
   parameter and other type applications are not. It returns the list of newly introduced
   dirt parameters, the list of newly introduced region parameters, and the type. *)
let fill_args ty =
  let ds = ref []

  in
  let fresh_dirt_param _ =
    let (Sugared.DirtParam x) as d = fresh_dirt_param () in
    ds := x :: !ds ; d
  in
  let rec fill (ty, loc) =
    let ty' =
      match ty with
      | Sugared.TyApply (t, tys, drts) ->
        let tys = List.map fill tys
        and drts =
          begin match drts with
            | Some drts -> Some drts
            | None ->
              begin match Tctx.lookup_params t with
                | None -> None
                | Some (_, ds) -> Some (List.map fresh_dirt_param ds)
              end
          end
        in
        Sugared.TyApply (t, tys, drts)
      | Sugared.TyParam _ as ty -> ty
      | Sugared.TyArrow (t1, t2, None) -> Sugared.TyArrow (fill t1, fill t2, Some (fresh_dirt_param ()))
      | Sugared.TyArrow (t1, t2, Some drt) -> Sugared.TyArrow (fill t1, fill t2, Some drt)
      | Sugared.TyTuple lst -> Sugared.TyTuple (List.map fill lst)
      | Sugared.TyHandler (t1, None, t2, None) -> Sugared.TyHandler (fill t1, Some (fresh_dirt_param ()), fill t2, Some (fresh_dirt_param ()))
      | Sugared.TyHandler (t1, Some drt, t2, None) -> Sugared.TyHandler (fill t1, Some drt, fill t2, Some (fresh_dirt_param ()))
      | Sugared.TyHandler (t1, None, t2, Some drt) -> Sugared.TyHandler (fill t1, Some (fresh_dirt_param ()), fill t2, Some drt)
      | Sugared.TyHandler (t1, Some drt1, t2, Some drt2) -> Sugared.TyHandler (fill t1, Some drt1, fill t2, Some drt2)
    in
    (ty', loc)
  in
  let ty = fill ty in
  !ds, ty

let fill_args_tydef def =
  match def with
  | Sugared.TyRecord lst ->
    let (ds, lst) =
      List.fold_right
        (fun (fld, ty) (ds, lst) ->
           let (ds'), ty = fill_args ty in
           (ds' @ ds, (fld, ty) :: lst))
        lst ([], [])
    in
    (ds), Sugared.TyRecord lst
  | Sugared.TySum lst ->
    let (ds, lst) =
      List.fold_right
        (fun (lbl, ty_op) (ds, lst) ->
           match ty_op with
           | None -> (ds, (lbl, None) :: lst)
           | Some ty ->
             let ds', ty = fill_args ty in
             (ds' @ ds, (lbl, Some ty) :: lst))
        lst ([], [])
    in
    ds, Sugared.TySum lst
  | Sugared.TyInline ty ->
    let params, ty = fill_args ty in
    params, Sugared.TyInline ty

(* Desugar a type, where only the given type, dirt and region parameters may appear.
   If a type application with missing dirt and region parameters is encountered,
   it uses [ds] and [rs] instead. This is used in desugaring of recursive type definitions
   where we need to figure out which type and dirt parameters are missing in a type defnition.
   Also, it relies on the optional region parameter in [T.Apply] to figure out whether
   an application applies to an effect type. So, it is prudent to call [fill_args] before
   calling [ty].
*)
let ty (ts, ds) =
  let rec ty (t, loc) = match t with
    | Sugared.TyApply (t, tys, drts) ->
      let tys = List.map ty tys
      and (drts) = begin match drts with
        | Some (drts) -> (List.map (dirt loc) drts)
        | None -> (List.map (fun (_, d) -> Type.simple_dirt d) ds)
      end
      in
      T.Apply (t, (tys, drts))
    | Sugared.TyParam t ->
      begin match C.lookup t ts with
        | None -> Error.syntax ~loc "Unbound type parameter '%s" t
        | Some p -> T.TyVar p
      end
    | Sugared.TyArrow (t1, t2, Some drt) -> T.Arrow (ty t1, (ty t2, dirt loc drt))
    | Sugared.TyArrow (t1, t2, None) -> assert false
    | Sugared.TyTuple lst -> T.Tuple (List.map ty lst)
    | Sugared.TyHandler (t1, Some drt1, t2, Some drt2) -> T.Handler ((ty t1, dirt loc drt1), (ty t2, dirt loc drt2))
    | Sugared.TyHandler (t1, _, t2, _) -> assert false
  and dirt loc (Sugared.DirtParam d) =
    match C.lookup d ds with
    | None -> Error.syntax ~loc "Unbound dirt parameter 'drt%d" d
    | Some d -> Type.simple_dirt d
  in
  ty

let trio_empty = ([], [])
let trio_append (ts1, ds1) (ts2, ds2) = (ts1 @ ts2, ds1 @ ds2)
let trio_flatten_map f lst = List.fold_left trio_append trio_empty (List.map f lst)
let trio_diff (ts1, ds1) (ts2, ds2) = (Common.diff ts1 ts2, Common.diff ds1 ds2)
let trio_uniq (ts1, ds1) = (Common.uniq ts1, Common.uniq ds1)

(** [free_params t] returns a triple of all free type, dirt, and region params in [t]. *)
let free_params t =
  let (@@@) = trio_append
  and optional f = function
    | None -> trio_empty
    | Some x -> f x
  in
  let rec ty (t, loc) = match t with
    | Sugared.TyApply (_, tys, drts) ->
      trio_flatten_map ty tys @@@ (optional dirts) drts
    | Sugared.TyParam s -> ([s], [])
    | Sugared.TyArrow (t1, t2, drt) -> ty t1 @@@ ty t2 @@@ (optional dirt) drt
    | Sugared.TyTuple lst -> trio_flatten_map ty lst
    | Sugared.TyHandler (t1, drt1, t2, drt2) -> ty t1 @@@ ty t2 @@@ (optional dirt) drt1 @@@ (optional dirt) drt2
  and dirt (Sugared.DirtParam d) = ([], [d])
  and dirts (drts) = trio_flatten_map dirt drts
  in
  trio_uniq (ty t)

let syntax_to_core_params (ts, ds) = (
  List.map (fun p -> (p, Params.fresh_ty_param ())) ts,
  List.map (fun d -> (d, Params.fresh_dirt_param ())) ds
)

(** [tydef params d] desugars the type definition with parameters [params] and definition [d]. *)
let tydef params d =
  let (ts, ds) as sbst = syntax_to_core_params params in
  (Params.make (List.map snd ts, List.map snd ds),
   begin match d with
     | Sugared.TyRecord lst -> Tctx.Record (List.map (fun (f,t) -> (f, ty sbst t)) lst)
     | Sugared.TySum lst -> Tctx.Sum (List.map (fun (lbl, t) -> (lbl, C.option_map (ty sbst) t)) lst)
     | Sugared.TyInline t -> Tctx.Inline (ty sbst t)
   end)

(** [tydefs defs] desugars the simultaneous type definitions [defs]. *)
let tydefs defs =
  (* The first thing to do is to fill the missing dirt and region parameters.
     At the end [ds] and [rs] hold the newly introduces dirt and region parameters.
     These become parameters to type definitions in the second stage. *)
  let ds, defs =
    List.fold_right
      (fun (tyname, (params, def)) (ds, defs) ->
         let d, def = fill_args_tydef def in
         (d @ ds, ((tyname, (params, def)) :: defs)))
      defs trio_empty
  in
  (* Now we traverse again and the rest of the work. *)
  List.map (fun (tyname, (ts, def)) -> (tyname, tydef (ts, ds) def)) defs


(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_variable ()] creates a fresh variable ["gen_gen1"], ["gen_gen2"], ... on
    each call *)
let fresh_variable = function
  | None -> Untyped.Variable.fresh "anon"
  | Some x -> Untyped.Variable.fresh x

let id_abstraction loc =
  let x = fresh_variable (Some "gen_id_par") in
  (Untyped.annotate (Untyped.PVar x) loc, (Untyped.annotate (Untyped.Value (Untyped.annotate (Untyped.Var x) loc)) loc))

let pattern ?(forbidden=[]) (p, loc) =
  let vars = ref [] in
  let forbidden = ref forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~loc "Variable %s occurs more than once in a pattern" x
    else
      let var = fresh_variable (Some x) in
      vars := (x, var) :: !vars;
      forbidden := x :: !forbidden;
      var
  in
  let rec pattern (p, loc) =
    let p = match p with
      | Pattern.Var x ->
        let x = new_var x in
        Untyped.PVar x
      | Pattern.As (p, x) ->
        let x = new_var x in
        let p' = pattern p in
        Untyped.PAs (p', x)
      | Pattern.Tuple ps -> Untyped.PTuple (List.map pattern ps)
      | Pattern.Record flds -> Untyped.PRecord (Common.assoc_map pattern flds)
      | Pattern.Variant (lbl, p) -> Untyped.PVariant (lbl, Common.option_map pattern p)
      | Pattern.Const c -> Untyped.PConst c
      | Pattern.Nonbinding -> Untyped.PNonbinding
    in
    { Untyped.term = p; Untyped.location = loc }
  in
  let p = pattern (p, loc) in
  !vars, p

(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec expression ctx (t, loc) =
  let w, e = match t with
    | Sugared.Var x ->
      begin match Common.lookup x ctx with
        | Some n -> [], Untyped.Var n
        | None -> Error.typing ~loc "Unknown variable %s" x
      end
    | Sugared.Const k ->
      [], Untyped.Const k
    | Sugared.Lambda a ->
      let a = abstraction ctx a in
      [], Untyped.Lambda a
    | Sugared.Function cs ->
      let x = fresh_variable (Some "gen_function") in
      let cs = List.map (abstraction ctx) cs in
      [], Untyped.Lambda ((Untyped.annotate (Untyped.PVar x) loc), Untyped.annotate (Untyped.Match (Untyped.annotate (Untyped.Var x) loc, cs)) loc)
    | Sugared.Handler cs ->
      let w, h = handler loc ctx cs in
      w, Untyped.Handler h
    | Sugared.Tuple ts ->
      let w, es = expressions ctx ts in
      w, Untyped.Tuple es
    | Sugared.Record ts ->
      if not (C.injective fst ts) then Error.syntax ~loc "Fields in a record must be distinct";
      let w, es = record_expressions ctx ts in
      w, Untyped.Record es
    | Sugared.Variant (lbl, None) ->
      [], Untyped.Variant (lbl, None)
    | Sugared.Variant (lbl, Some t) ->
      let w, e = expression ctx t in
      w, Untyped.Variant (lbl, Some e)
    | Sugared.Effect eff ->
      [], Untyped.Effect eff
    (* Terms that are desugared into computations. We list them explicitly in
       order to catch any future constructs. *)
    | Sugared.Apply _ | Sugared.Match _ | Sugared.Let _ | Sugared.LetRec _
    | Sugared.Handle _ | Sugared.Conditional _ ->
      let x = fresh_variable (Some "gen_bind") in
      let c = computation ctx (t, loc) in
      let w = [Untyped.annotate (Untyped.PVar x) loc, c] in
      w, Untyped.Var x
  in
  w, Untyped.annotate e loc

and computation ctx (t, loc) =
  let if_then_else e c1 c2 =
    Untyped.Match (e, [
        ((Untyped.annotate (Untyped.PConst (Const.of_true)) c1.Untyped.location), c1);
        ((Untyped.annotate (Untyped.PConst (Const.of_false)) c2.Untyped.location), c2)
      ])
  in
  let w, c = match t with
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "&&", loc1), t1), loc2), t2) ->
      let w1, e1 = expression ctx t1 in
      let c2 = computation ctx t2 in
      w1, if_then_else e1 c2 (Untyped.annotate (Untyped.Value (Untyped.annotate (Untyped.Const Const.of_false) loc2)) loc2)
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "||", loc1), t1), loc2), t2) ->
      let w1, e1 = expression ctx t1 in
      let c2 = computation ctx t2 in
      w1, if_then_else e1 (Untyped.annotate (Untyped.Value (Untyped.annotate (Untyped.Const Const.of_true) loc2)) loc2) c2
    | Sugared.Apply (t1, t2) ->
      let w1, e1 = expression ctx t1 in
      let w2, e2 = expression ctx t2 in
      (w1 @ w2), Untyped.Apply (e1, e2)
    | Sugared.Match (t, cs) ->
      let cs = List.map (abstraction ctx) cs in
      let w, e = expression ctx t in
      w, Untyped.Match (e, cs)
    | Sugared.Handle (t1, t2) ->
      let w1, e1 = expression ctx t1 in
      let c2 = computation ctx t2 in
      w1, Untyped.Handle (e1, c2)
    | Sugared.Conditional (t, t1, t2) ->
      let w, e = expression ctx t in
      let c1 = computation ctx t1 in
      let c2 = computation ctx t2 in
      w, if_then_else e c1 c2
    | Sugared.Let (defs, t) ->
      let ctx', defs, _ =
        List.fold_right (fun (p, c) (ctx', defs, forbidden) ->
            let check_forbidden (x, _) =
              if List.mem x forbidden then
                Error.syntax ~loc:(snd p) "Several definitions of %s" x
            in
            let p_vars, p = pattern p in
            List.iter check_forbidden p_vars;
            let c = computation ctx c in
            (p_vars @ ctx', (p, c) :: defs, (List.map fst p_vars) @ forbidden)) defs (ctx, [], []) in
      let c = computation ctx' t in
      [], Untyped.Let (defs, c)
    | Sugared.LetRec (defs, t) ->
      let ctx', ns, _ = List.fold_right (fun (x, t) (ctx', ns, forbidden) ->
          if List.mem x forbidden then
            Error.syntax ~loc:(snd t) "Several definitions of %s" x;
          let n = fresh_variable (Some x) in
          ((x, n) :: ctx', n :: ns, x :: forbidden)) defs (ctx, [], []) in
      let defs =
        List.fold_right (fun (p, (_, c)) defs ->
            let c = let_rec ctx' c in
            ((p, c) :: defs)) (List.combine ns defs) [] in
      let c = computation ctx' t in
      [], Untyped.LetRec (defs, c)
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | (Sugared.Var _ | Sugared.Const _ | Sugared.Tuple _ | Sugared.Record _  | Sugared.Variant _ | Sugared.Lambda _ | Sugared.Function _ | Sugared.Handler _ | Sugared.Effect _) ->
      let w, e = expression ctx (t, loc) in
      w, Untyped.Value e
  in
  match w with
  | [] -> Untyped.annotate c loc
  | _ :: _ -> Untyped.annotate (Untyped.Let (w, Untyped.annotate c loc)) loc

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
    let x = fresh_variable (Some "gen_let_rec_function") in
    let cs = List.map (abstraction ctx) cs in
    (Untyped.annotate (Untyped.PVar x) loc), Untyped.annotate (Untyped.Match (Untyped.annotate (Untyped.Var x) loc, cs)) loc
  | _ -> Error.syntax ~loc "This kind of expression is not allowed in a recursive definition"

and expressions ctx = function
  | [] -> [], []
  | t :: ts ->
    let w, e = expression ctx t in
    let ws, es = expressions ctx ts in
    w @ ws, (e :: es)

and record_expressions ctx = function
  | [] -> [], []
  | (f, t) :: ts ->
    let w, e = expression ctx t in
    let ws, es = record_expressions ctx ts in
    w @ ws, ((f, e) :: es)

and handler loc ctx {Sugared.effect_clauses=ops; Sugared.value_clause=val_a; Sugared.finally_clause=fin_a} =
  let rec operation_cases = function
    | [] -> []
    | (op, a2) :: cs ->
      let cs' = operation_cases cs in
      (op, abstraction2 ctx a2) :: cs'
  in
  let ops = operation_cases ops in
  [], { Untyped.effect_clauses = ops;
        Untyped.value_clause = Common.option_map (abstraction ctx) val_a;
        Untyped.finally_clause = Common.option_map (abstraction ctx) fin_a}

let top_ctx = ref []

let top_let defs =
  let ctx', defs, _ =
    List.fold_right (fun (p, c) (ctx', defs, forbidden) ->
        let check_forbidden (x, _) =
          if List.mem x forbidden then
            Error.syntax ~loc:(snd p) "Several definitions of %s" x
        in
        let p_vars, p = pattern p in
        List.iter check_forbidden p_vars;
        let c = computation !top_ctx c in
        (p_vars @ ctx', (p, c) :: defs, (List.map fst p_vars) @ forbidden)) defs (!top_ctx, [], []) in
  top_ctx := ctx';
  defs

let top_let_rec defs =
  let ctx', ns, _ = List.fold_right (fun (x, t) (ctx', ns, forbidden) ->
      if List.mem x forbidden then
        Error.syntax ~loc:(snd t) "Several definitions of %s" x;
      let n = fresh_variable (Some x) in
      ((x, n) :: ctx', n :: ns, x :: forbidden)) defs (!top_ctx, [], []) in
  let defs =
    List.fold_right (fun (p, (_, c)) defs ->
        let c = let_rec ctx' c in
        ((p, c) :: defs)) (List.combine ns defs) [] in
  top_ctx := ctx';
  defs

let external_ty x t =
  let _, t = fill_args t in
  let n = fresh_variable (Some x) in
  top_ctx := (x, n) :: !top_ctx;
  let params = syntax_to_core_params (free_params t) in
  n, ty params t

let top_computation c = computation !top_ctx c

let rec toplevel (cmd, loc) =
  {
    Untyped.term = plain_toplevel cmd;
    Untyped.location = loc
  }
and plain_toplevel = function
  | Sugared.Tydef defs ->
    Untyped.Tydef (tydefs defs)
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
    let ds1, ty1 = fill_args ty1
    and ds2, ty2 = fill_args ty2 in
    let ty1 = ty (syntax_to_core_params ([], ds1)) ty1
    and ty2 = ty (syntax_to_core_params ([], ds2)) ty2 in
    Untyped.DefEffect (eff, (ty1, ty2))
  | Sugared.Term t ->
    let c = top_computation t in
    Untyped.Computation c
  | Sugared.Use filename ->
    Untyped.Use filename
  | Sugared.Reset ->
    Untyped.Reset
  | Sugared.Help ->
    Untyped.Help
  | Sugared.Quit ->
    Untyped.Quit
  | Sugared.TypeOf t ->
    let c = top_computation t in
    Untyped.TypeOf c
