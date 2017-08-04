module T = Type

(* Shadowing
The state is altered in order to store variables and effects
In type definitions, externals or effect definitions, the state is kept when going to the next toplevel computation.
In between other computations, no state is maintained.
eg.
  effect Op : string -> unit (* Op is added to the state, this is persistent *)
  (fun x -> x);;  (* During type inference, x is stored in the state *)
                  (* State changes that occured during this computation are not persistent*)
  (fun x -> x);;
*)

type state = {
  context : TypingEnv.t;
  effects : (Type.ty * Type.ty) Untyped.EffectMap.t
}

let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty

let add_effect env eff (ty1, ty2) =
  {env with effects = Untyped.EffectMap.add eff (ty1, ty2) env.effects}

let add_def env x ty_sch =
  {env with context = TypingEnv.update env.context x ty_sch}

let infer_effect ~loc env eff =
  try
    eff, (Untyped.EffectMap.find eff env.effects)
  with
  | Not_found -> Error.typing ~loc "Unbound effect %s" eff

let extend_env vars env =
  List.fold_right (fun (x, ty_sch) env -> {env with context = TypingEnv.update env.context x ty_sch}) vars env

(**************************)
(* PATTERN TYPE INFERENCE *)
(**************************)

let rec type_pattern st {Untyped.term=pat; Untyped.location=loc} =
  let scheme, pattern = type_plain_pattern st pat in
  Typed.annotate pattern scheme loc

(* [type_pattern p] infers the type scheme of a pattern [p].
   This consists of:
   - the context, which contains bound variables and their types,
   - the type of the whole pattern (what it matches against), and
   - constraints connecting all these types.
   Note that unlike in ordinary type schemes, context types are positive while
   pattern type is negative. *)
and type_plain_pattern st = function
  | Untyped.PVar x ->
      let ty = Type.fresh_ty () in
      let sch = Scheme.simple ty in
      let sch = Scheme.add_to_context x ty sch in
      sch, Typed.PVar x
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

(*****************************)
(* EXPRESSION TYPE INFERENCE *)
(*****************************)

(* Type an expression
    type_expr will annotate the terms with location information
*)
let rec type_expr st {Untyped.term=expr; Untyped.location=loc} = type_plain_expr st loc expr

(* Type a plain expression *)
and type_plain_expr st loc = function
  | Untyped.Var x ->
    let ty_sch = begin match TypingEnv.lookup st.context x with
      | Some ty_sch -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      | None -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      end
    in
    assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Const const ->
      Ctor.const ~loc const
  | Untyped.Tuple es -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Record lst -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Variant (lbl, e) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Lambda (p, c) ->
    assert false
    (* let sch, pt = type_pattern st p in
    let ct, constraints = type_comp st c in
    Typed.Lambda (pt, Scheme.get_type sch, ct), constraints *)
  | Untyped.Effect eff -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Handler h -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

(******************************)
(* COMPUTATION TYPE INFERENCE *)
(******************************)

(* Type a computation
    type_comp will annotate the terms with location information
*)
and type_comp st {Untyped.term=comp; Untyped.location=loc} = type_plain_comp st loc comp

(* Type a plain computation *)
and type_plain_comp st loc = function
  | Untyped.Value e ->
    let typed_e = type_expr st e in
    Ctor.value ~loc typed_e
  | Untyped.Match (e, cases) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Apply (e1, e2) ->
    assert false
    (* let expr1, _ = type_expr st e1 in
    let expr2, _ = type_expr st e2 in
    (* Smartconstructors.apply ~loc expr1 expr2, constraints *)
    Typed.Apply (expr1, expr2), [] *)
  | Untyped.Handle (e, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Let (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.LetRec (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)

(***************************)
(* TOPLEVEL TYPE INFERENCE *)
(***************************)

(* Execute type inference for a toplevel command *)
let type_toplevel ~loc st = function
  (* Main toplevel command for toplevel computations *)
  | Untyped.Computation c ->
    let c = type_comp st c in
    (* Print.debug "A LOT OF CONSTRAINTS"; *)
    Typed.Computation c, st
  (* Use keyword: include a file *)
  | Untyped.Use fn ->
    Typed.Use fn, st
  (* Reset keyword *)
  | Untyped.Reset ->
    Typed.Reset, st
  (* Help keyword *)
  | Untyped.Help ->
    Typed.Help, st
  (* Quit keyword: exit interactive toplevel *)
  | Untyped.Quit ->
    Typed.Quit, st
  (* Type definition *)
  | Untyped.Tydef defs ->
    Tctx.extend_tydefs ~loc defs;
    Typed.Tydef defs, st
  (* Top let command: let x = c1 in c2 *)
  | Untyped.TopLet defs ->
    assert false
  (* Top letrec command: let rec x = c1 in c2 *)
  | Untyped.TopLetRec defs'' ->
    assert false
  (* Exernal definition *)
  | Untyped.External (x, ty, f) ->
    let st = add_def st x (Scheme.simple ty) in
    Typed.External (x, ty, f), st
  (* Define an effect *)
  | Untyped.DefEffect (eff, (ty1, ty2)) ->
    let st = add_effect st eff (ty1, ty2) in
    Typed.DefEffect ((eff, (ty1, ty2)), (ty1, ty2)), st
  (* Get the type of *)
  | Untyped.TypeOf c ->
    assert false

(**************************)
(* COMMAND TYPE INFERENCE *)
(**************************)

(* Execute typing for a single toplevel command *)
let type_cmd st cmd =
  let loc = cmd.Untyped.location in
  let cmd, st = type_toplevel ~loc st cmd.Untyped.term in
  (cmd, loc), st

(* Go through all *toplevel* commands and execute type inference *)
let type_cmds st cmds =
  let cmds, st =
    List.fold_left (fun (cmds, st) cmd ->
        let cmd, st = type_cmd st cmd in
        (cmd :: cmds, st)
      ) ([], st) cmds
  in
  List.rev cmds, st
