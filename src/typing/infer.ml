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

(* Infer the effect or throw an error when the effect doesn't exist *)
let infer_effect ~loc st eff =
  try
    eff, (Untyped.EffectMap.find eff st.effects)
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
    let pat = type_pattern st p in
    Ctor.pas ~loc pat x
  | Untyped.PNonbinding ->
    Ctor.pnonbinding ~loc
  | Untyped.PConst const ->
    Ctor.pconst ~loc const
  | Untyped.PTuple ps ->
    let pats = List.map (type_pattern st) ps in
    Ctor.ptuple ~loc pats
  | Untyped.PRecord [] ->
    assert false
  | Untyped.PRecord (((fld, _) :: _) as lst) ->
    (* TODO *)
    assert false
  | Untyped.PVariant (lbl, p) ->
    (* TODO *)
    assert false

(******************************)
(* ABSTRACTION TYPE INFERENCE *)
(******************************)

and type_abstraction st loc (p, c) =
  let pat = type_pattern st p in
  let comp, st = type_comp st c in
  Ctor.abstraction ~loc pat comp, st

and type_abstraction2 st loc (p1, p2, c) =
  let pat1 = type_pattern st p1 in
  let pat2 = type_pattern st p2 in
  let comp, st = type_comp st c in
  Ctor.abstraction2 ~loc pat1 pat2 comp, st

(*****************************)
(* EXPRESSION TYPE INFERENCE *)
(*****************************)

(* Type an expression
    type_expr will annotate the terms with location information
*)
and type_expr st {Untyped.term=expr; Untyped.location=loc} = type_plain_expr st loc expr

(* Type a plain expression *)
and type_plain_expr st loc = function
  | Untyped.Var x ->
    let ty_sch, st = get_var_scheme_env st x in
    Ctor.var ~loc x ty_sch, st
  | Untyped.Const const ->
    Ctor.const ~loc const, st
  | Untyped.Tuple es ->
    let els = List.map (fun (a, b) -> a) (List.map (type_expr st) es) in
    Ctor.tuple ~loc els, st
  | Untyped.Record lst ->
    (* TODO *)
    assert false
  | Untyped.Variant (lbl, e) ->
    (* TODO *)
    assert false
  | Untyped.Lambda (p, c) ->
    let pat = type_pattern st p in
    let comp, st = type_comp st c in
    Ctor.lambda ~loc pat comp, st
  | Untyped.Effect eff ->
    let eff = infer_effect ~loc st eff in
    Ctor.effect ~loc eff, st
  | Untyped.Handler {
      effect_clauses=effect_cases;
      value_clause=value_case;
      finally_clause=finally_case;
    } ->
    assert false
    (* let type_handler_clause (eff, (p1, p2, c)) =
      let eff = infer_effect ~loc:(c.Untyped.location) st eff in
      (eff, type_abstraction2 st loc (p1, p2, c))
    in
    let typed_effect_cases = Common.map type_handler_clause effect_cases in
    let untyped_value_clause =
      match value_case with
        | Some a -> a
        | None -> Desugar.id_abstraction Location.unknown
    in
    let typed_value_clause = type_abstraction st loc untyped_value_clause in
    (* let typed_finally_clause =  *)
    Ctor.handler ~loc typed_effect_cases typed_value_clause, st *)

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
    let typed_e, st = type_expr st e in
    Ctor.value ~loc typed_e, st
  | Untyped.Match (e, es) ->
    let cases = List.map (fun (a, b) -> a) (List.map (type_abstraction st loc) es) in
    let exp, st = (type_expr st e) in
    Ctor.patmatch ~loc exp cases, st
  | Untyped.Apply (e1, e2) ->
    let expr1, st = type_expr st e1 in
    let expr2, st = type_expr st e2 in
    Ctor.apply ~loc expr1 expr2, st
  | Untyped.Handle (e, c) ->
    (* TODO *)
    assert false
    (* Typed.handle ~loc (type_expr env e) (type_comp env c) *)
  | Untyped.Let (defs, c) ->
    (* TODO *)
    assert false
    (* let env', defs' = type_let_defs ~loc env defs in
    Typed.let' ~loc defs' (type_comp env' c) *)
  | Untyped.LetRec (defs, c) ->
    (* TODO *)
    assert false
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
    (* TODO *)
    assert false
  (* Top letrec command: let rec x = c1 in c2 *)
  | Untyped.TopLetRec defs'' ->
    (* TODO *)
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
    let c, st = type_comp st c in
    Typed.TypeOf c, st

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
