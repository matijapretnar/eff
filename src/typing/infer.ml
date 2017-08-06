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

(* Get the type of a constant *)
let ty_of_const = function
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty


(* Infer the effect or throw an error when the effect doesn't exist *)
let infer_effect ~loc env eff =
  try
    eff, (Untyped.EffectMap.find eff env.effects)
  with
    | Not_found -> Error.typing ~loc "Unbound effect %s" eff

(* Add an effect to the environment *)
let add_effect env eff (ty1, ty2) =
  {env with effects = Untyped.EffectMap.add eff (ty1, ty2) env.effects}

(* Add x : Typed.variable, ty_sch : Scheme.ty_scheme to the environment *)
let add_def env x ty_sch =
  {env with context = TypingEnv.update env.context x ty_sch}

(* Add vars : (Typed.variable * Scheme.ty_scheme) list to the environment *)
let add_multiple_defs vars env =
  List.fold_right (fun (x, ty_sch) env -> {env with context = TypingEnv.update env.context x ty_sch}) vars env

(* Lookup a type scheme for a variable in the typing environment
    Otherwise, create a new scheme (and add it to the typing environment)
*)
let get_var_scheme_env st x =
  begin match TypingEnv.lookup st.context x with
    | Some ty_sch -> ty_sch, st
    | None -> let ty = Type.fresh_ty () in
              let sch = Scheme.var x ty in
              sch, add_def st x sch
  end

(**************************)
(* PATTERN TYPE INFERENCE *)
(**************************)

let rec type_pattern st {Untyped.term=pat; Untyped.location=loc} = type_plain_pattern st loc pat

(* [type_pattern p] infers the type scheme of a pattern [p].
   This consists of:
   - the context, which contains bound variables and their types,
   - the type of the whole pattern (what it matches against), and
   - constraints connecting all these types.
   Note that unlike in ordinary type schemes, context types are positive while
   pattern type is negative. *)
and type_plain_pattern st loc = function
  | Untyped.PVar x ->
    Ctor.pvar ~loc x

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
    (* Print.debug "Variable: %t" (Location.print loc); *)
    let ty_sch, st = get_var_scheme_env st x in
    Ctor.var ~loc x ty_sch, st
  | Untyped.Const const ->
    (* Print.debug "Constant: %t" (Location.print loc); *)
    Ctor.const ~loc const, st
  | Untyped.Tuple es -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Record lst -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Variant (lbl, e) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Lambda (p, c) ->
    (* Print.debug "Lambda: %t" (Location.print loc); *)
    let pat = type_pattern st p in
    let comp, st = type_comp st c in
    Ctor.lambda ~loc pat comp, st
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
    (* Print.debug "Value: %t" (Location.print loc); *)
    let typed_e, st = type_expr st e in
    Ctor.value ~loc typed_e, st
  | Untyped.Match (e, cases) ->
    assert false
    (* Typed.match' ~loc (type_expr env e) (List.map (type_abstraction env) cases) *)
  | Untyped.Apply (e1, e2) ->
    (* Print.debug "Application: %t" (Location.print loc); *)
    let expr1, st = type_expr st e1 in
    let expr2, st = type_expr st e2 in
    Ctor.apply ~loc expr1 expr2, st
  | Untyped.Handle (e, c) ->
    assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
    (* Typed.handle ~loc (type_expr env e) (type_comp env c) *)
  | Untyped.Let (defs, c) ->
    assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
    (* let env', defs' = type_let_defs ~loc env defs in
    Typed.let' ~loc defs' (type_comp env' c) *)
  | Untyped.LetRec (defs, c) ->
    assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
    (* let env', defs' = type_let_rec_defs ~loc env defs in
    let env', defs' = type_let_rec_defs ~loc env' defs in
    Typed.let_rec' ~loc defs' (type_comp env' c) *)

(***************************)
(* TOPLEVEL TYPE INFERENCE *)
(***************************)

(* Execute type inference for a toplevel command *)
let type_toplevel ~loc ppf st = function
  (* Main toplevel command for toplevel computations *)
  | Untyped.Computation c ->
      (* Do not capture state since we do not want to persist it *)
      let c, _ = type_comp st c in
      Format.fprintf ppf "@[- : %t@]@." (Scheme.print_dirty_scheme c.Typed.scheme);
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
  (* let cmd, st = type_toplevel ~loc st cmd.Untyped.term in *)
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
