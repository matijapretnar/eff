module T = Type

type state = {
  context : TypingEnv.t;
  (* effects : (Type.ty * Type.ty) Untyped.EffectMap.t *)
}

let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty

(* let add_effect env eff (ty1, ty2) =
  {env with effects = Untyped.EffectMap.add eff (ty1, ty2) env.effects}
 *)
let add_def env x ty_sch =
  {env with context = TypingEnv.update env.context x ty_sch}

(* let infer_effect ~loc env eff =
  try
    eff, (Untyped.EffectMap.find eff env.effects)
  with
  | Not_found -> Error.typing ~loc "Unbound effect %s" eff
 *)
(* [type_pattern p] infers the type scheme of a pattern [p].
   This consists of:
   - the context, which contains bound variables and their types,
   - the type of the whole pattern (what it matches against), and
   - constraints connecting all these types.
   Note that unlike in ordinary type schemes, context types are positive while
   pattern type is negative. *)
let rec type_pattern p =
  let loc = p.Untyped.location in
  (* let unify = Scheme.finalize_pattern_scheme ~loc in *)
  let ty_sch, pat = match p.Untyped.term with

    | Untyped.PVar x ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

    | Untyped.PAs (p, x) ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

    | Untyped.PNonbinding ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

    | Untyped.PConst const ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

    | Untyped.PTuple ps ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

    | Untyped.PRecord [] ->
        assert false

    | Untyped.PRecord (((fld, _) :: _) as lst) ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

    | Untyped.PVariant (lbl, p) ->
        assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

  in
  (* Print.debug "%t : %t" (Untyped.print_pattern (p, loc)) (Scheme.print_ty_scheme ty_sch); *)
  {
    Typed.term = pat;
    Typed.location = loc
  }

let extend_env vars env =
  List.fold_right (fun (x, ty_sch) env -> {env with context = TypingEnv.update env.context x ty_sch}) vars env

let rec type_expr st {Untyped.term=expr; Untyped.location=loc} =
  let e, constraints = type_plain_expr st expr in
  Typed.annotate e loc, constraints
and type_plain_expr st = function
  | Untyped.Var x ->
    let ty_sch = begin match TypingEnv.lookup st.context x with
      | Some ty_sch -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      | None -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      end
    in
    assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Const const ->
      Typed.Const const, []
  | Untyped.Tuple es -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Record lst -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Variant (lbl, e) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Lambda a -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Effect eff -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Handler h -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
and type_comp st {Untyped.term=comp; Untyped.location=loc} =
  let c, constraints = type_plain_comp st comp in
  Typed.annotate c loc, constraints
and type_plain_comp st = function
  | Untyped.Value e ->
      let typed_e, constraints = type_expr st e in
      Typed.Value typed_e, constraints
  | Untyped.Match (e, cases) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Apply (e1, e2) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Handle (e, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Let (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.LetRec (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)


let type_toplevel ~loc st = function
  | Untyped.Computation c ->
    let c, constraints = type_comp st c in
    Print.debug "A LOT OF CONSTRAINTS";
    Typed.Computation c, st
  | Untyped.Use fn ->
    Typed.Use fn, st
  | Untyped.Reset ->
    Typed.Reset, st
  | Untyped.Help ->
    Typed.Help, st
  | Untyped.Quit ->
    Typed.Quit, st


let type_cmd st cmd =
  let loc = cmd.Untyped.location in
  let cmd, st = type_toplevel ~loc st cmd.Untyped.term in
  (cmd, loc), st

let type_cmds st cmds =
  let cmds, st =
    List.fold_left (fun (cmds, st) cmd ->
        let cmd, st = type_cmd st cmd in
        (cmd :: cmds, st)
      ) ([], st) cmds
  in
  List.rev cmds, st
