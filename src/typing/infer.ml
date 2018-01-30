module C = OldUtils
module T = Type
module Core = CoreSyntax

type t = Ctx.t

let empty = Ctx.empty

let warn_implicit_sequencing = ref false

let disable_typing = ref false

(* We perform type inference int the style of Standard ML 97, i.e.,
   Hindley-Milner polymorphism with value restriction. Throughout, we work with
   a reference to a type substitution, usually called [cstr], in which we
   collect the results of unification. That is, we perform unification as early
   as locssible (rather than collect all equations and then solve them), and
   store the results in [cstr]. 

   The effect of carrying around the substitution is that we need to be careful
   about when to apply it:
   
   1. we apply the substitution to types [t1] and [t2] before trying to solve
      the equation [t1 = t2].

   2. we apply the substitution to a type which we just looked up in the context.
*)
(* Can a computation safely be generalized, i.e., is it non-expansive in the parlance of
   SML? In our case non-expansive simply means "is a value". *)
let nonexpansive = function
  | Core.Value _ -> true
  | Core.Apply _ | Core.Match _ | Core.Handle _ | Core.Let _ | Core.LetRec _
   |Core.Check _ ->
      false


let empty_constraint = []

let add_ty_constraint cstr loc t1 t2 = cstr := (t1, t2, loc) :: !cstr

let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty


(* [infer_pattern cstr pp] infers the type of pattern [pp]. It returns the list of
   pattern variables with their types, which are all guaranteed to be [Type.Meta]'s, together
   with the type of the pattern. *)
let infer_pattern cstr pp =
  (* XXX *)
  (*   if not (Pattern.linear_pattern pp) then
    Error.typing ~loc:(snd pp) "Variables in a pattern must be distinct." ; *)
  let vars = ref [] in
  let rec infer p =
    let loc = p.Core.location in
    match p.Core.term with
    | Core.PVar x ->
        let t = if !disable_typing then T.universal_ty else T.fresh_ty () in
        vars := (x, t) :: !vars ;
        t
    | Core.PAs (p, x) ->
        let t = infer p in
        vars := (x, t) :: !vars ;
        t
    | Core.PNonbinding -> T.fresh_ty ()
    | Core.PConst const -> ty_of_const const
    | Core.PTuple ps -> T.Tuple (C.map infer ps)
    | Core.PRecord [] -> assert false
    | Core.PRecord ((fld, _) :: _ as lst) -> (
      match Tctx.infer_field fld with
      | None -> Error.typing ~loc "Unbound record field label %s" fld
      | Some (ty, (t, us)) ->
          let unify_record_pattern (fld, p) =
            match C.lookup fld us with
            | None ->
                Error.typing ~loc
                  "Unexpected field %s in a pattern of type %s." fld t
            | Some u -> add_ty_constraint cstr loc (infer p) u
          in
          List.iter unify_record_pattern lst ;
          ty )
    | Core.PVariant (lbl, p) ->
      match Tctx.infer_variant lbl with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some (ty, u) ->
          ( match (p, u) with
          | None, None -> ()
          | Some p, Some u -> add_ty_constraint cstr loc (infer p) u
          | None, Some _ ->
              Error.typing ~loc
                "Constructor %s should be applied to an argument." lbl
          | Some _, None ->
              Error.typing ~loc
                "Constructor %s cannot be applied to an argument." lbl ) ;
          ty
  in
  let t = infer pp in
  (!vars, t)


let extend_with_pattern ?(forbidden_vars= []) ctx cstr p =
  let vars, t = infer_pattern cstr p in
  match C.find (fun (x, _) -> List.mem_assoc x vars) forbidden_vars with
  | Some (x, _) ->
      Error.typing ~loc:p.Core.location "Several definitions of %t."
        (Core.Variable.print x)
  | None ->
      ( vars
      , t
      , List.fold_right (fun (x, t) ctx -> Ctx.extend_ty ctx x t) vars ctx )


let rec infer_abstraction ctx cstr (p, c) =
  let _, t1, ctx = extend_with_pattern ctx cstr p in
  let t2 = infer_comp ctx cstr c in
  (t1, t2)


and infer_abstraction2 ctx cstr (p1, p2, c) =
  let vs, t1, ctx = extend_with_pattern ctx cstr p1 in
  let _, t2, ctx = extend_with_pattern ~forbidden_vars:vs ctx cstr p2 in
  let t3 = infer_comp ctx cstr c in
  (t1, t2, t3)


and infer_handler_case_abstraction ctx cstr (p, k, e) =
  let vs, t1, ctx = extend_with_pattern ctx cstr p in
  let _, tk, ctx = extend_with_pattern ~forbidden_vars:vs ctx cstr k in
  let t2 = infer_comp ctx cstr e in
  (tk, t1, t2)


and infer_let ctx cstr loc defs =
  ( if !warn_implicit_sequencing && List.length defs >= 2 then
      let locations = List.map (fun (_, c) -> c.Core.location) defs in
      Print.warning ~loc
        "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
        (Print.sequence "," Location.print locations) ) ;
  let vars, ctx =
    List.fold_left
      (fun (vs, ctx') (p, c) ->
        let tc = infer_comp ctx cstr c in
        let ws, tp = infer_pattern cstr p in
        add_ty_constraint cstr c.Core.location tc tp ;
        match C.find_duplicate (List.map fst ws) (List.map fst vs) with
        | Some x ->
            Error.typing ~loc "Several definitions of %t."
              (Core.Variable.print x)
        | None ->
            let sbst = Unify.solve !cstr in
            let ws = OldUtils.assoc_map (T.subst_ty sbst) ws in
            let ctx = Ctx.subst_ctx ctx sbst in
            let ws =
              OldUtils.assoc_map
                (Ctx.generalize ctx (nonexpansive c.Core.term))
                ws
            in
            let ctx' =
              List.fold_right
                (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme)
                ws ctx'
            in
            (List.rev ws @ vs, ctx') )
      ([], ctx) defs
  in
  (vars, Ctx.subst_ctx ctx (Unify.solve !cstr))


and infer_let_rec ctx cstr loc defs =
  if not (OldUtils.injective fst defs) then
    Error.typing ~loc "Multiply defined recursive value." ;
  let lst =
    List.map
      (fun (f, (p, c)) ->
        let u1 = T.fresh_ty () in
        let u2 = T.fresh_ty () in
        (f, u1, u2, p, c) )
      defs
  in
  let vars =
    List.fold_right
      (fun (f, u1, u2, _, _) vars -> (f, T.Arrow (u1, u2)) :: vars)
      lst []
  in
  let ctx' =
    List.fold_right
      (fun (f, u1, u2, _, _) ctx -> Ctx.extend_ty ctx f (T.Arrow (u1, u2)))
      lst ctx
  in
  List.iter
    (fun (_, u1, u2, p, c) ->
      let _, tp, ctx' = extend_with_pattern ctx' cstr p in
      let tc = infer_comp ctx' cstr c in
      add_ty_constraint cstr p.Core.location u1 tp ;
      add_ty_constraint cstr c.Core.location u2 tc )
    lst ;
  let sbst = Unify.solve !cstr in
  let vars = OldUtils.assoc_map (T.subst_ty sbst) vars in
  let ctx = Ctx.subst_ctx ctx sbst in
  let vars = OldUtils.assoc_map (Ctx.generalize ctx true) vars in
  let ctx =
    List.fold_right
      (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme)
      vars ctx
  in
  (vars, ctx)


(* [infer_expr ctx cstr (e,loc)] infers the type of expression [e] in context
   [ctx]. It returns the inferred type of [e]. *)
and infer_expr ctx cstr e =
  let loc = e.Core.location in
  match e.Core.term with
  | Core.Var x -> Ctx.lookup ~loc ctx x
  | Core.Const const -> ty_of_const const
  | Core.Tuple es -> T.Tuple (C.map (infer_expr ctx cstr) es)
  | Core.Record [] -> assert false
  | Core.Record ((fld, _) :: _ as lst) -> (
    match
      (* XXX *)
      (*       if not (Pattern.linear_record lst) then
        Error.typing ~loc "Fields in a record must be distinct." ;
 *)
      Tctx.infer_field fld
    with
    | None ->
        Error.typing ~loc "Unbound record field label %s in a pattern" fld
    | Some (ty, (t_name, arg_types)) ->
        if List.length lst <> List.length arg_types then
          Error.typing ~loc "malformed record of type %s" t_name
        else
          let arg_types' = C.assoc_map (infer_expr ctx cstr) lst in
          let unify_record_arg (fld, t) =
            match C.lookup fld arg_types with
            | None ->
                Error.typing ~loc
                  "Unexpected record field label %s in a pattern" fld
            | Some u -> add_ty_constraint cstr loc t u
          in
          List.iter unify_record_arg arg_types' ;
          ty )
  | Core.Variant (lbl, u) -> (
    match Tctx.infer_variant lbl with
    | None -> Error.typing ~loc "Unbound constructor %s in a pattern" lbl
    | Some (ty, arg_type) ->
        ( match (arg_type, u) with
        | None, None -> ()
        | Some ty, Some u ->
            let ty' = infer_expr ctx cstr u in
            add_ty_constraint cstr loc ty ty'
        | _, _ ->
            Error.typing ~loc "Wrong number of arguments for label %s." lbl ) ;
        ty )
  | Core.Lambda a ->
      let t1, t2 = infer_abstraction ctx cstr a in
      T.Arrow (t1, t2)
  | Core.Effect op -> (
    match Ctx.infer_effect ctx op with
    | None -> Error.typing ~loc "Unbound operation %s" op
    | Some (t1, t2) -> T.Arrow (t1, t2) )
  | Core.Handler
      { Core.effect_clauses= ops
      ; Core.value_clause= a_val
      ; Core.finally_clause= a_fin } ->
      let t_value = T.fresh_ty () in
      let t_finally = T.fresh_ty () in
      let t_yield = T.fresh_ty () in
      let unify_operation (op, a2) =
        match Ctx.infer_effect ctx op with
        | None -> Error.typing ~loc "Unbound operation %s in a handler" op
        | Some (t1, t2) ->
            let tk, u1, u2 = infer_handler_case_abstraction ctx cstr a2 in
            add_ty_constraint cstr loc t1 u1 ;
            (* XXX maybe we need to change the direction of inequalities here,
                     or even require equalities. *)
            add_ty_constraint cstr loc tk (T.Arrow (t2, t_yield)) ;
            add_ty_constraint cstr loc t_yield u2
      in
      List.iter unify_operation ops ;
      let valt1, valt2 = infer_abstraction ctx cstr a_val in
      let fint1, fint2 = infer_abstraction ctx cstr a_fin in
      add_ty_constraint cstr loc valt1 t_value ;
      add_ty_constraint cstr loc valt2 t_yield ;
      add_ty_constraint cstr loc fint2 t_finally ;
      add_ty_constraint cstr loc fint1 t_yield ;
      T.Handler {T.value= t_value; T.finally= t_finally}


(* [infer_comp ctx cstr (c,loc)] infers the type of computation [c] in context [ctx].
   It returns the list of newly introduced meta-variables and the inferred type. *)
and infer_comp ctx cstr cp =
  (* XXX Why isn't it better to just not call type inference when type checking is disabled? *)
  if !disable_typing then T.universal_ty
  else
    let rec infer ctx c =
      let loc = c.Core.location in
      match c.Core.term with
      | Core.Apply (e1, e2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer_expr ctx cstr e2 in
          let t = T.fresh_ty () in
          add_ty_constraint cstr loc t1 (T.Arrow (t2, t)) ;
          t
      | Core.Value e -> infer_expr ctx cstr e
      | Core.Match (e, []) ->
          let t_in = infer_expr ctx cstr e in
          let t_out = T.fresh_ty () in
          add_ty_constraint cstr loc t_in T.empty_ty ;
          t_out
      | Core.Match (e, lst) ->
          let t_in = infer_expr ctx cstr e in
          let t_out = T.fresh_ty () in
          let infer_case ((p, e') as a) =
            let t_in', t_out' = infer_abstraction ctx cstr a in
            add_ty_constraint cstr e.Core.location t_in t_in' ;
            add_ty_constraint cstr e'.Core.location t_out' t_out
          in
          List.iter infer_case lst ; t_out
      | Core.Handle (e1, c2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer ctx c2 in
          let t3 = T.fresh_ty () in
          let t1' = T.Handler {T.value= t2; T.finally= t3} in
          add_ty_constraint cstr loc t1' t1 ;
          t3
      | Core.Let (defs, c) ->
          let _, ctx = infer_let ctx cstr loc defs in
          infer ctx c
      | Core.LetRec (defs, c) ->
          let _, ctx = infer_let_rec ctx cstr loc defs in
          infer ctx c
      | Core.Check c ->
          ignore (infer ctx c) ;
          T.unit_ty
    in
    let ty = infer ctx cp in
    ty


let infer_top_comp ctx c =
  let cstr = ref [] in
  let ty = infer_comp ctx cstr c in
  let sbst = Unify.solve !cstr in
  Exhaust.check_comp c ;
  let ctx = Ctx.subst_ctx ctx sbst in
  let ty = Type.subst_ty sbst ty in
  (ctx, Ctx.generalize ctx (nonexpansive c.Core.term) ty)


let infer_top_let ~loc ctx defs =
  let vars, ctx = infer_let ctx (ref empty_constraint) Location.unknown defs in
  List.iter
    (fun (p, c) -> Exhaust.is_irrefutable p ; Exhaust.check_comp c)
    defs ;
  (vars, ctx)


let infer_top_let_rec ~loc ctx defs =
  let vars, ctx =
    infer_let_rec ctx (ref empty_constraint) Location.unknown defs
  in
  List.iter
    (fun (_, (p, c)) -> Exhaust.is_irrefutable p ; Exhaust.check_comp c)
    defs ;
  (vars, ctx)
