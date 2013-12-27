(** Desugaring of syntax into the core language. *)

module C = Common
module T = Type
module Sugared = SyntaxSugared

(* ***** Desugaring of types. ***** *)

let fresh_dirt_param = Common.fresh (fun n -> Sugared.DirtParam n)
let fresh_region_param = Common.fresh (fun n -> Sugared.RegionParam n)

(* Fill in missing dirt and region parameters in a type with fresh ones. Also resolves
   type applications so that applications of effect types are equipped with the extra region
   parameter and other type applications are not. It returns the list of newly introduced
   dirt parameters, the list of newly introduced region parameters, and the type. *)
let fill_args is_effect ty =
  let ds = ref []
  and rs = ref []
  in
  let fresh_dirt_param _ =
    let (Sugared.DirtParam x) as d = fresh_dirt_param () in
      ds := x :: !ds ; d
  and fresh_region_param _ =
    let (Sugared.RegionParam x) as r = fresh_region_param () in
      rs := x :: !rs ; r
  in
  let rec fill (ty, pos) =
  let ty' =
  match ty with
  | Sugared.TyApply (t, tys, drts_rgns, rgn) ->
      let tys = List.map fill tys
      and drts_rgns =
        begin match drts_rgns with
          | Some drts_rgns -> Some drts_rgns
          | None ->
            begin match Tctx.lookup_params t with
              | None -> None
              | Some (_, ds, rs) -> Some (List.map fresh_dirt_param ds, List.map fresh_region_param rs)
            end
        end
      and rgn = begin match rgn with
        | Some rgn ->
          if is_effect t then Some rgn else Error.typing ~pos "A non-effect type %s tagged with a region." t
        | None ->
          if is_effect t then Some (fresh_region_param ()) else None
      end
      in
      Sugared.TyApply (t, tys, drts_rgns, rgn)
  | Sugared.TyParam _ as ty -> ty
  | Sugared.TyArrow (t1, t2, None) -> Sugared.TyArrow (fill t1, fill t2, Some (fresh_dirt_param ()))
  | Sugared.TyArrow (t1, t2, Some drt) -> Sugared.TyArrow (fill t1, fill t2, Some drt)
  | Sugared.TyTuple lst -> Sugared.TyTuple (List.map fill lst)
  | Sugared.TyHandler (t1, None, t2, None) -> Sugared.TyHandler (fill t1, Some (fresh_dirt_param ()), fill t2, Some (fresh_dirt_param ()))
  | Sugared.TyHandler (t1, Some drt, t2, None) -> Sugared.TyHandler (fill t1, Some drt, fill t2, Some (fresh_dirt_param ()))
  | Sugared.TyHandler (t1, None, t2, Some drt) -> Sugared.TyHandler (fill t1, Some (fresh_dirt_param ()), fill t2, Some drt)
  | Sugared.TyHandler (t1, Some drt1, t2, Some drt2) -> Sugared.TyHandler (fill t1, Some drt1, fill t2, Some drt2)
  in
  (ty', pos)
  in
  let ty = fill ty in
  (!ds, !rs), ty

let fill_args_tydef is_effect def =
  match def with
    | Sugared.TyRecord lst ->
      let (ds, rs, lst) =
        List.fold_right
          (fun (fld, ty) (ds, rs, lst) ->
            let (ds', rs'), ty = fill_args is_effect ty in
              (ds' @ ds, rs' @ rs, (fld, ty) :: lst))
          lst Trio.empty
      in
        (ds, rs), Sugared.TyRecord lst
    | Sugared.TySum lst ->
      let (ds, rs, lst) =
        List.fold_right
          (fun (lbl, ty_op) (ds, rs, lst) ->
            match ty_op with
              | None -> (ds, rs, (lbl, None) :: lst)
              | Some ty ->
                let (ds', rs'), ty = fill_args is_effect ty in
                  (ds' @ ds, rs' @ rs, (lbl, Some ty) :: lst))
          lst Trio.empty
      in
        (ds, rs), Sugared.TySum lst
    | Sugared.TyEffect lst ->
      let (ds, rs, lst) =
        List.fold_right
          (fun (op, (ty1, ty2)) (ds, rs, lst) ->
            let (ds1, rs1), ty1 = fill_args is_effect ty1 in
            let (ds2, rs2), ty2 = fill_args is_effect ty2 in
              (ds1 @ ds2 @ ds, rs1 @ rs2 @ rs, (op, (ty1, ty2)) :: lst))
          lst Trio.empty
      in
        (ds, rs), Sugared.TyEffect lst

    | Sugared.TyInline ty ->
      let params, ty = fill_args is_effect ty in
        params, Sugared.TyInline ty

(* Desugar a type, where only the given type, dirt and region parameters may appear. 
   If a type application with missing dirt and region parameters is encountered,
   it uses [ds] and [rs] instead. This is used in desugaring of recursive type definitions
   where we need to figure out which type and dirt parameters are missing in a type defnition.
   Also, it relies on the optional region parameter in [T.Apply] to figure out whether
   an application applies to an effect type. So, it is prudent to call [fill_args] before
   calling [ty].
*)
let ty (ts, ds, rs) =
  let rec ty (t, pos) = match t with
  | Sugared.TyApply (t, tys, drts_rgns, rgn) ->
      let tys = List.map ty tys
      and (drts, rgns) = begin match drts_rgns with
        | Some (drts, rgns) -> (List.map (dirt pos) drts, List.map (region pos) rgns)
        | None -> (List.map (fun (_, d) -> Type.simple_dirt d) ds, List.map (fun (_, r) -> r) rs)
      end 
      in begin match rgn with
        | None -> T.Apply (t, (tys, drts, rgns))
        | Some rgn -> T.Effect (t, (tys, drts, rgns), (region pos) rgn)
      end
  | Sugared.TyParam t ->
    begin match C.lookup t ts with
    | None -> Error.syntax ~pos "Unbound type parameter '%s" t
    | Some p -> T.TyParam p
    end
  | Sugared.TyArrow (t1, t2, Some drt) -> T.Arrow (ty t1, (ty t2, dirt pos drt))
  | Sugared.TyArrow (t1, t2, None) -> assert false
  | Sugared.TyTuple lst -> T.Tuple (List.map ty lst)
  | Sugared.TyHandler (t1, Some drt1, t2, Some drt2) -> T.Handler ((ty t1, dirt pos drt1), (ty t2, dirt pos drt2))
  | Sugared.TyHandler (t1, _, t2, _) -> assert false
  and dirt pos (Sugared.DirtParam d) =
    match C.lookup d ds with
    | None -> Error.syntax ~pos "Unbound dirt parameter 'drt%d" d
    | Some d -> Type.simple_dirt d
  and region pos (Sugared.RegionParam r) =
    match C.lookup r rs with
    | None -> Error.syntax ~pos "Unbound region parameter 'rgn%d" r
    | Some r -> r
  in
  ty

(** [free_params t] returns a triple of all free type, dirt, and region params in [t]. *)
let free_params t =
  let (@@@) = Trio.append
  and optional f = function
    | None -> Trio.empty
    | Some x -> f x
  in
  let rec ty (t, pos) = match t with
  | Sugared.TyApply (_, tys, drts_rgns, rgn) ->
      Trio.flatten_map ty tys @@@ (optional dirts_regions) drts_rgns @@@ (optional region) rgn
  | Sugared.TyParam s -> ([s], [], [])
  | Sugared.TyArrow (t1, t2, drt) -> ty t1 @@@ ty t2 @@@ (optional dirt) drt
  | Sugared.TyTuple lst -> Trio.flatten_map ty lst
  | Sugared.TyHandler (t1, drt1, t2, drt2) -> ty t1 @@@ ty t2 @@@ (optional dirt) drt1 @@@ (optional dirt) drt2
  and dirt (Sugared.DirtParam d) = ([], [d], [])
  and region (Sugared.RegionParam r) = ([], [], [r])
  and dirts_regions (drts, rgns) = Trio.flatten_map dirt drts @@@ Trio.flatten_map region rgns
  in
  Trio.uniq (ty t)

let syntax_to_core_params (ts, ds, rs) = (
    List.map (fun p -> (p, Type.fresh_ty_param ())) ts,
    List.map (fun d -> (d, Type.fresh_dirt_param ())) ds,
    List.map (fun r -> (r, Type.fresh_region_param ())) rs
  )

(** [tydef params d] desugars the type definition with parameters [params] and definition [d]. *)
let tydef params d =
  let (ts, ds, rs) as sbst = syntax_to_core_params params in
    (Trio.snds (ts, ds, rs),
     begin match d with
       | Sugared.TyRecord lst -> Tctx.Record (List.map (fun (f,t) -> (f, ty sbst t)) lst)
       | Sugared.TySum lst -> Tctx.Sum (List.map (fun (lbl, t) -> (lbl, C.option_map (ty sbst) t)) lst)
       | Sugared.TyEffect lst -> Tctx.Effect (List.map (fun (op,(t1,t2)) -> (op, (ty sbst t1, ty sbst t2))) lst)
       | Sugared.TyInline t -> Tctx.Inline (ty sbst t)
     end)

(** [tydefs defs] desugars the simultaneous type definitions [defs]. *)
let tydefs ~pos defs =
  (* First we build a predicate which tells whether a type name refers to an effect type. *)
  let is_effect =
    let rec find forbidden tyname =
      match C.lookup tyname defs with
        | Some (_, (Sugared.TyRecord _ | Sugared.TySum _)) -> false
        | Some (_, (Sugared.TyInline (Sugared.TyApply (tyname', _, _, _), pos))) ->
          if List.mem tyname' forbidden
          then Error.typing ~pos "Type definition %s is cyclic." tyname' (* Compare to [Tctx.check_noncyclic]. *)
          else find (tyname :: forbidden) tyname'
        | Some (_, Sugared.TyInline _) -> false
        | Some (_, (Sugared.TyEffect _)) -> true
        | None -> Tctx.is_effect ~pos tyname
    in
      find []
  in
  (* The first thing to do is to fill the missing dirt and region parameters. 
     At the end [ds] and [rs] hold the newly introduces dirt and region parameters.
     These become parameters to type definitions in the second stage. *)
  let ds, rs, defs =
    List.fold_right
      (fun (tyname, (params, def)) (ds, rs, defs) ->
        let (d, r), def = fill_args_tydef is_effect def in
          (d @ ds, r @ rs, ((tyname, (params, def)) :: defs)))
      defs Trio.empty
  in
    (* Now we traverse again and the rest of the work. *)
    List.map (fun (tyname, (ts, def)) -> (tyname, tydef (ts, ds, rs) def)) defs


(* ***** Desugaring of expressions and computations. ***** *)

(** [fresh_variable ()] creates a fresh variable ["$gen1"], ["$gen2"], ... on
    each call *)
let fresh_variable = Common.fresh (fun n -> (n, "$gen" ^ string_of_int n))

let id_abstraction pos =
  let x = fresh_variable () in
  ((Pattern.Var x, pos), (Syntax.Value (Syntax.Var x, pos), pos))

let pattern ?(forbidden=[]) (p, pos) =
  let vars = ref [] in
  let forbidden = ref forbidden in
  let new_var x =
    if List.mem x !forbidden then
      Error.syntax ~pos "Variable %s occurs more than once in a pattern" x
    else
      let (n, _) = fresh_variable () in
      vars := (x, (n, x)) :: !vars;
      forbidden := x :: !forbidden;
      (n, x)
  in
  let rec pattern (p, pos) =
    let p = match p with
    | Pattern.Var x ->
        let x = new_var x in
        Pattern.Var x
    | Pattern.As (p, x) ->
        let x = new_var x in
        let p' = pattern p in
        Pattern.As (p', x)
    | Pattern.Tuple ps -> Pattern.Tuple (List.map pattern ps)
    | Pattern.Record flds -> Pattern.Record (Common.assoc_map pattern flds)
    | Pattern.Variant (lbl, p) -> Pattern.Variant (lbl, Common.option_map pattern p)
    | (Pattern.Const _ | Pattern.Nonbinding) as p -> p
    in
    (p, pos)
  in
  let p = pattern (p, pos) in
  !vars, p

(* Desugaring functions below return a list of bindings and the desugared form. *)

let rec expression ctx (t, pos) =
  let w, e = match t with
  | Sugared.Var x ->
      begin match Common.lookup x ctx with
      | Some n -> [], Syntax.Var n
      | None -> Error.typing ~pos "Unknown variable %s" x
      end
  | Sugared.Const k ->
      [], Syntax.Const k
  | Sugared.Lambda a ->
      let a = abstraction ctx a in
      [], Syntax.Lambda a
  | Sugared.Function cs ->
      let x = fresh_variable () in
      let cs = List.map (abstraction ctx) cs in
      [], Syntax.Lambda ((Pattern.Var x, pos), (Syntax.Match ((Syntax.Var x, pos), cs), pos))
  | Sugared.Handler cs ->
      let w, h = handler pos ctx cs in
      w, Syntax.Handler h
  | Sugared.Tuple ts ->
      let w, es = expressions ctx ts in
      w, Syntax.Tuple es
  | Sugared.Record ts ->
      if not (C.injective fst ts) then Error.syntax ~pos "Fields in a record must be distinct";
      let w, es = record_expressions ctx ts in
      w, Syntax.Record es
  | Sugared.Variant (lbl, None) ->
      [], Syntax.Variant (lbl, None)
  | Sugared.Variant (lbl, Some t) ->
      let w, e = expression ctx t in
      w, Syntax.Variant (lbl, Some e)
  | Sugared.Operation (t, op) ->
      let w, e = expression ctx t in
      w, Syntax.Operation (e, op)
  (* Terms that are desugared into computations. We list them explicitly in
     order to catch any future constructs. *)
  | Sugared.Apply _ | Sugared.Match _ | Sugared.Let _ | Sugared.LetRec _
  | Sugared.Handle _ | Sugared.Conditional _ | Sugared.While _ | Sugared.For _ | Sugared.New _ | Sugared.Check _ ->
      let x = fresh_variable () in
      let c = computation ctx (t, pos) in
      let w = [(Pattern.Var x, pos), c] in
      w, Syntax.Var x
  in
  w, (e, pos)

and computation ctx (t, pos) =
  let if_then_else e ((_, pos1) as c1) ((_, pos2) as c2) =
    Syntax.Match (e, [
      (Pattern.Const (C.Boolean true), pos1), c1;
      (Pattern.Const (C.Boolean false), pos2), c2
    ])
  in
  let w, c = match t with
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "&&", pos1), t1), pos2), t2) ->
      let w1, e1 = expression ctx t1 in
      let c2 = computation ctx t2 in
          w1, if_then_else e1 c2 ((Syntax.Value (Syntax.Const (C.Boolean false), pos2)), pos2)
    | Sugared.Apply ((Sugared.Apply ((Sugared.Var "||", pos1), t1), pos2), t2) ->
      let w1, e1 = expression ctx t1 in
      let c2 = computation ctx t2 in
          w1, if_then_else e1 ((Syntax.Value (Syntax.Const (C.Boolean true), pos2)), pos2) c2
    | Sugared.Apply (t1, t2) ->
        let w1, e1 = expression ctx t1 in
        let w2, e2 = expression ctx t2 in
          (w1 @ w2), Syntax.Apply (e1, e2)
    | Sugared.Match (t, cs) ->
        let cs = List.map (abstraction ctx) cs in
        let w, e = expression ctx t in
          w, Syntax.Match (e, cs)
    | Sugared.New (eff, None) ->
        [], Syntax.New (eff, None)
    | Sugared.New (eff, Some (t, lst)) ->
        let w, e = expression ctx t in
        let lst = List.map (fun (op, a) -> (op, abstraction2 ctx a)) lst in
          w, Syntax.New (eff, Some (e, lst))
    | Sugared.Handle (t1, t2) ->
        let w1, e1 = expression ctx t1 in
        let c2 = computation ctx t2 in
          w1, Syntax.Handle (e1, c2)
    | Sugared.Conditional (t, t1, t2) ->
        let w, e = expression ctx t in
        let c1 = computation ctx t1 in
        let c2 = computation ctx t2 in
          w, if_then_else e c1 c2
    | Sugared.While (t1, t2) ->
        let c1 = computation ctx t1 in
        let c2 = computation ctx t2 in
          [], Syntax.While (c1, c2)

    | Sugared.For (i, t1, t2, t, b) ->
      let w1, e1 = expression ctx t1 in
      let w2, e2 = expression ctx t2 in
      let j = fresh_variable () in
      let c = computation ((i, j) :: ctx) t in
        w1 @ w2, Syntax.For (j, e1, e2, c, b)
    | Sugared.Check t ->
        [], Syntax.Check (computation ctx t)
    | Sugared.Let (defs, t) ->
        let ctx', defs, _ =
            List.fold_right (fun (p, c) (ctx', defs, forbidden) ->
                    let check_forbidden (x, _) =
                      if List.mem x forbidden then
                        Error.syntax ~pos:(snd p) "Several definitions of %s" x
                    in
                    let p_vars, p = pattern p in
                    List.iter check_forbidden p_vars;
                    let c = computation ctx c in
                    (p_vars @ ctx', (p, c) :: defs, (List.map fst p_vars) @ forbidden)) defs (ctx, [], []) in
        let c = computation ctx' t in
          [], Syntax.Let (defs, c)
    | Sugared.LetRec (defs, t) ->
        let ctx', ns, _ = List.fold_right (fun (x, t) (ctx', ns, forbidden) ->
                                          if List.mem x forbidden then
                                            Error.syntax ~pos:(snd t) "Several definitions of %s" x;
                                          let n = fresh_variable () in
                                          ((x, n) :: ctx', n :: ns, x :: forbidden)) defs (ctx, [], []) in
        let defs =
          List.fold_right (fun (p, (_, c)) defs ->
                            let c = let_rec ctx' c in
                            ((p, c) :: defs)) (List.combine ns defs) [] in
        let c = computation ctx' t in
          [], Syntax.LetRec (defs, c)
    (* The remaining cases are expressions, which we list explicitly to catch any
       future changes. *)
    | (Sugared.Var _ | Sugared.Const _ | Sugared.Tuple _ | Sugared.Record _  | Sugared.Variant _ | Sugared.Lambda _ | Sugared.Function _ | Sugared.Handler _ | Sugared.Operation _) ->
        let w, e = expression ctx (t, pos) in
          w, Syntax.Value e
  in
    match w with
      | [] -> (c, pos)
      | _ :: _ -> Syntax.Let (w, (c, pos)), pos

and abstraction ctx (p, t) =
  let vars, p = pattern p in
  (p, computation (vars @ ctx) t)

and abstraction2 ctx (p1, p2, t) =
  let vars1, p1 = pattern p1 in
  let vars2, p2 = pattern p2 in
  (p1, p2, computation (vars1 @ vars2 @ ctx) t)

and let_rec ctx = function
  | (Sugared.Lambda a, _) -> abstraction ctx a
  | (Sugared.Function cs, pos) ->
    let x = fresh_variable () in
    let cs = List.map (abstraction ctx) cs in
    ((Pattern.Var x, pos), (Syntax.Match ((Syntax.Var x, pos), cs), pos))
  | (_, pos) -> Error.syntax ~pos "This kind of expression is not allowed in a recursive definition"

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

and handler pos ctx {Sugared.operations=ops; Sugared.value=val_a; Sugared.finally=fin_a} =
  let rec operation_cases = function
  | [] -> [], []
  | ((t, op), a2) :: cs ->
    let w, e = expression ctx t in
    let ws, cs' = operation_cases cs in
    w @ ws, ((e, op), abstraction2 ctx a2) :: cs'
  in
  let ws, ops = operation_cases ops in
  ws, { Syntax.operations = ops;
    Syntax.value =
      (match val_a with None -> id_abstraction pos | Some a -> abstraction ctx a);
    Syntax.finally =
      (match fin_a with None -> id_abstraction pos | Some a -> abstraction ctx a)}

let top_ctx = ref []

let top_let defs =
  let ctx', defs, _ =
  List.fold_right (fun (p, c) (ctx', defs, forbidden) ->
                    let check_forbidden (x, _) =
                      if List.mem x forbidden then
                        Error.syntax ~pos:(snd p) "Several definitions of %s" x
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
                                      Error.syntax ~pos:(snd t) "Several definitions of %s" x;
                                    let (n, _) = fresh_variable () in
                                    let n = (n, x) in
                                    ((x, n) :: ctx', n :: ns, x :: forbidden)) defs (!top_ctx, [], []) in
  let defs =
    List.fold_right (fun (p, (_, c)) defs ->
                      let c = let_rec ctx' c in
                      ((p, c) :: defs)) (List.combine ns defs) [] in
  top_ctx := ctx';
  defs

let external_ty is_effect x t =
  let _, t = fill_args is_effect t in
  let (n, _) = fresh_variable () in
  let n = (n, x) in
  top_ctx := (x, n) :: !top_ctx;
  let (ts, ds, rs) = syntax_to_core_params (free_params t) in
  n, ([], ty (ts, ds, rs) t, Constraints.empty)

let top_computation c = computation !top_ctx c
