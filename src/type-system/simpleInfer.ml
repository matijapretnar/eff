open CoreUtils
module T = Type
module Untyped = UntypedSyntax
module Ctx = SimpleCtx
module Unify = SimpleUnify

type state = Ctx.t

let initial_state = Ctx.empty

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
  | Untyped.Value _ -> true
  | Untyped.Apply _ | Untyped.Match _ | Untyped.Handle _ | Untyped.Let _
   |Untyped.LetRec _ | Untyped.Check _ ->
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
  let rec infer {it= p; at= loc} =
    match p with
    | Untyped.PVar x ->
        let t = if !disable_typing then T.universal_ty else T.fresh_ty () in
        vars := (x, t) :: !vars ;
        t
    | Untyped.PAnnotated (p, t) ->
        let p_t = infer p in
        add_ty_constraint cstr loc p_t t;
        t
    | Untyped.PAs (p, x) ->
        let t = infer p in
        vars := (x, t) :: !vars ;
        t
    | Untyped.PNonbinding -> T.fresh_ty ()
    | Untyped.PConst const -> ty_of_const const
    | Untyped.PTuple ps -> T.Tuple (OldUtils.map infer ps)
    | Untyped.PRecord flds -> (
      match Assoc.pop flds with
      | None -> assert false
      | Some ((fld, _), _) ->
        match Tctx.infer_field fld with
        | None -> Error.typing ~loc "Unbound record field label %s" fld
        | Some (ty, (t, us)) ->
            let unify_record_pattern (fld, p) =
              match Assoc.lookup fld us with
              | None ->
                  Error.typing ~loc
                    "Unexpected field %s in a pattern of type %s." fld t
              | Some u -> add_ty_constraint cstr loc (infer p) u
            in
            Assoc.iter unify_record_pattern flds ;
            ty )
    | Untyped.PVariant (lbl, p) ->
      match Tctx.infer_variant lbl with
      | None -> assert false
      | Some (ty, u) ->
          ( match (p, u) with
          | None, None -> ()
          | Some p, Some u -> add_ty_constraint cstr loc (infer p) u
          | None, Some _ -> assert false
          | Some _, None -> assert false ) ;
          ty
  in
  let t = infer pp in
  (!vars, t)

let extend_with_pattern ?(forbidden_vars= []) ctx cstr p =
  let vars, t = infer_pattern cstr p in
  match List.find_opt (fun (x, _) -> List.mem_assoc x vars) forbidden_vars with
  | Some (x, _) ->
      Error.typing ~loc:p.at "Several definitions of %t."
        (Untyped.Variable.print x)
  | None ->
      let ctx' =
        List.fold_right (fun (x, t) ctx -> Ctx.extend_ty ctx x t) vars ctx
      in
      (vars, t, ctx')

let rec infer_abstraction ctx cstr (p, c) =
  let _, t1, ctx' = extend_with_pattern ctx cstr p in
  let t2 = infer_comp ctx' cstr c in
  (t1, t2)

and infer_abstraction2 ctx cstr (p1, p2, c) =
  let vs, t1, ctx' = extend_with_pattern ctx cstr p1 in
  let _, t2, ctx'' = extend_with_pattern ~forbidden_vars:vs ctx' cstr p2 in
  let t3 = infer_comp ctx'' cstr c in
  (t1, t2, t3)

and infer_handler_case_abstraction ctx cstr (p, k, e) =
  let vs, t1, ctx' = extend_with_pattern ctx cstr p in
  let _, tk, ctx'' = extend_with_pattern ~forbidden_vars:vs ctx' cstr k in
  let t2 = infer_comp ctx'' cstr e in
  (tk, t1, t2)

and infer_let ctx cstr loc defs =
  ( if !warn_implicit_sequencing && List.length defs >= 2 then
      let locations = List.map (fun (_, c) -> c.at) defs in
      Print.warning ~loc
        "Implicit sequencing between computations:@?@[<v 2>@,%t@]"
        (Print.sequence "," Location.print locations) ) ;
  let infer_fold_fun (vs, ctx') (p, c) =
    let tc = infer_comp ctx cstr c in
    let ws, tp = infer_pattern cstr p in
    add_ty_constraint cstr c.at tc tp ;
    match OldUtils.find_duplicate (List.map fst ws) (List.map fst vs) with
    | Some x ->
        Error.typing ~loc "Several definitions of %t."
          (Untyped.Variable.print x)
    | None ->
        let sbst = Unify.solve !cstr in
        let ws = Assoc.map (T.subst_ty sbst) (Assoc.of_list ws) in
        let ctx = Ctx.subst_ctx ctx sbst in
        let ws = Assoc.map (Ctx.generalize ctx (nonexpansive c.it)) ws in
        let ws = Assoc.to_list ws in
        let ctx' =
          List.fold_right
            (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme)
            ws ctx'
        in
        (List.rev ws @ vs, ctx')
  in
  let vars, ctx' = List.fold_left infer_fold_fun ([], ctx) defs in
  (vars, Ctx.subst_ctx ctx' (Unify.solve !cstr))

and infer_let_rec ctx cstr loc defs =
  if not (OldUtils.no_duplicates (List.map fst defs)) then
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
      add_ty_constraint cstr p.at u1 tp ;
      add_ty_constraint cstr c.at u2 tc )
    lst ;
  let sbst = Unify.solve !cstr in
  let vars = Assoc.map (T.subst_ty sbst) (Assoc.of_list vars) in
  let ctx = Ctx.subst_ctx ctx sbst in
  let vars = Assoc.map (Ctx.generalize ctx true) vars in
  let vars = Assoc.to_list vars in
  let ctx =
    List.fold_right
      (fun (x, ty_scheme) ctx -> Ctx.extend ctx x ty_scheme)
      vars ctx
  in
  (vars, ctx)

(* [infer_expr ctx cstr (e,loc)] infers the type of expression [e] in context
   [ctx]. It returns the inferred type of [e]. *)
and infer_expr ctx cstr {it= e; at= loc} =
  match e with
  | Untyped.Var x -> Ctx.lookup ~loc ctx x
  | Untyped.Const const -> ty_of_const const
  | Untyped.Annotated (t, ty) ->
      let ty' = infer_expr ctx cstr t in
      add_ty_constraint cstr loc ty ty';
      ty
  | Untyped.Tuple es -> T.Tuple (OldUtils.map (infer_expr ctx cstr) es)
  | Untyped.Record flds -> (
    match Assoc.pop flds with
    | None -> assert false
    | Some ((fld, _), _) ->
      match
        (* XXX *)
        (*       if not (Pattern.linear_record flds') then
          Error.typing ~loc "Fields in a record must be distinct." ;*)
        Tctx.infer_field fld
      with
      | None ->
          Error.typing ~loc "Unbound record field label %s in a pattern" fld
      | Some (ty, (t_name, arg_types)) ->
          if Assoc.length flds <> Assoc.length arg_types then
            Error.typing ~loc "malformed record of type %s" t_name
          else
            let arg_types' = Assoc.map (infer_expr ctx cstr) flds in
            let unify_record_arg (fld, t) =
              match Assoc.lookup fld arg_types with
              | None ->
                  Error.typing ~loc
                    "Unexpected record field label %s in a pattern" fld
              | Some u -> add_ty_constraint cstr loc t u
            in
            Assoc.iter unify_record_arg arg_types' ;
            ty )
  | Untyped.Variant (lbl, u) -> (
    match Tctx.infer_variant lbl with
    | None -> assert false
    | Some (ty, arg_type) ->
        ( match (arg_type, u) with
        | None, None -> ()
        | Some ty, Some u ->
            let ty' = infer_expr ctx cstr u in
            add_ty_constraint cstr loc ty ty'
        | _, _ -> assert false ) ;
        ty )
  | Untyped.Lambda a ->
      let t1, t2 = infer_abstraction ctx cstr a in
      T.Arrow (t1, t2)
  | Untyped.Effect op -> (
    match Ctx.infer_effect ctx op with
    | None -> Error.typing ~loc "Unbound operation %s" op
    | Some (t1, t2) -> T.Arrow (t1, t2) )
  | Untyped.Handler
      { Untyped.effect_clauses= ops
      ; Untyped.value_clause= a_val
      ; Untyped.finally_clause= a_fin } ->
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
      Assoc.iter unify_operation ops ;
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
    let rec infer ctx {it= c; at= loc} =
      match c with
      | Untyped.Apply (e1, e2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer_expr ctx cstr e2 in
          let t = T.fresh_ty () in
          add_ty_constraint cstr loc t1 (T.Arrow (t2, t)) ;
          t
      | Untyped.Value e -> infer_expr ctx cstr e
      | Untyped.Match (e, []) ->
          let t_in = infer_expr ctx cstr e in
          let t_out = T.fresh_ty () in
          add_ty_constraint cstr loc t_in T.empty_ty ;
          t_out
      | Untyped.Match (e, lst) ->
          let t_in = infer_expr ctx cstr e in
          let t_out = T.fresh_ty () in
          let infer_case ((p, e') as a) =
            let t_in', t_out' = infer_abstraction ctx cstr a in
            add_ty_constraint cstr e.at t_in t_in' ;
            add_ty_constraint cstr e'.at t_out' t_out
          in
          List.iter infer_case lst ; t_out
      | Untyped.Handle (e1, c2) ->
          let t1 = infer_expr ctx cstr e1 in
          let t2 = infer ctx c2 in
          let t3 = T.fresh_ty () in
          let t1' = T.Handler {T.value= t2; T.finally= t3} in
          add_ty_constraint cstr loc t1' t1 ;
          t3
      | Untyped.Let (defs, c) ->
          let _, ctx = infer_let ctx cstr loc defs in
          infer ctx c
      | Untyped.LetRec (defs, c) ->
          let _, ctx = infer_let_rec ctx cstr loc defs in
          infer ctx c
      | Untyped.Check c ->
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
  (ctx, Ctx.generalize ctx (nonexpansive c.it) ty)

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
  let exhaust_check (_, (p, c)) =
    Exhaust.is_irrefutable p ; Exhaust.check_comp c
  in
  List.iter exhaust_check defs ;
  (vars, ctx)
