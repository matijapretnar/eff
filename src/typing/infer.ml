module T = Type
module Typed = Typed
module Untyped = Untyped

module Variable = Symbol.Make(Symbol.String)

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

(* Change the types in effect to primitives *)
let fix_type ty =
  begin match ty with
    | Type.Apply ("unit", ([], _)) -> Type.Tuple []
    | Type.Apply ("bool", ([], _)) -> Type.Prim Type.BoolTy
    | Type.Apply ("int", ([], _)) -> Type.Prim Type.IntTy
    | Type.Apply ("string", ([], _)) -> Type.Prim Type.StringTy
    | Type.Apply ("float", ([], _)) -> Type.Prim Type.FloatTy
    | _ -> ty
  end

(* Add an effect to the environment *)
let add_effect st eff (ty1, ty2) =
  {st with effects = Untyped.EffectMap.add eff (fix_type ty1, fix_type ty2) st.effects}

(* Add x : Typed.variable, ty_sch : Scheme.ty_scheme to the environment *)
let add_def st x ty_sch =
  {st with context = TypingEnv.update st.context x ty_sch}

(* Add vars : (Typed.variable * Scheme.ty_scheme) list to the environment *)
let add_multiple_defs vars st =
  List.fold_right (fun (x, ty_sch) st -> {st with context = TypingEnv.update st.context x ty_sch}) vars st

(* Lookup a type scheme for a variable in the typing environment
    Otherwise, create a new scheme (and add it to the typing environment)
*)
let get_var_scheme_env ~loc st x =
  begin match TypingEnv.lookup st.context x with
    | Some ty_sch -> ty_sch
    | None -> (* Error.typing ~loc "Unbound poly variable %t" (Variable.print ~safe:true x) *)
              let ty = Type.fresh_ty () in
              let sch = Scheme.tmpvar ~loc x ty in
              sch
  end

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc
(**************************)
(* PATTERN TYPE INFERENCE *)
(**************************)

(* [pattern_vars p] returns the list of variables appearing in pattern [p]. *)
let rec pattern_vars {Untyped.term=p; Untyped.location=loc} =
  match p with
  | Untyped.PVar x -> [x]
  | Untyped.PAs (p,x) -> x :: pattern_vars p
  | Untyped.PTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
  | Untyped.PRecord lst -> List.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
  | Untyped.PVariant (_, None) -> []
  | Untyped.PVariant (_, Some p) -> pattern_vars p
  | Untyped.PConst _ -> []
  | Untyped.PNonbinding -> []

(* [linear_pattern p] verifies that [p] is linear and has linear records. *)
let linear_pattern p =
  let rec linear_records {Untyped.term=p; Untyped.location=loc} =
    match p with
    | Untyped.PVar x -> true
    | Untyped.PAs (p, _) -> linear_records p
    | Untyped.PTuple lst -> List.for_all linear_records lst
    | Untyped.PRecord lst -> List.for_all (fun (_, p) -> linear_records p) lst
    | Untyped.PVariant (_, None) -> true
    | Untyped.PVariant (_, Some p) -> linear_records p
    | Untyped.PConst _ -> true
    | Untyped.PNonbinding -> true
  in
  OldUtils.injective (fun x -> x) (pattern_vars p) && linear_records p

(* [linear_record r] verifies that a record or a record pattern has linear field names. *)
let linear_record lst = OldUtils.injective fst lst

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
    Ctor.pvar ~loc x, st
  | Untyped.PAs (p, x) ->
    let pat, st = type_pattern st p in
    Ctor.pas ~loc pat x, st
  | Untyped.PNonbinding ->
    Ctor.pnonbinding ~loc, st
  | Untyped.PConst const ->
    Ctor.pconst ~loc const, st
  | Untyped.PTuple ps ->
    let pats = List.map (fun (e, _) -> e) (List.map (type_pattern st) ps) in
    Ctor.ptuple ~loc pats, st
  | Untyped.PRecord [] ->
    assert false
  | Untyped.PRecord (((fld, _) :: _) as lst) ->
    if not (linear_record lst) then
      Error.typing ~loc "Fields in a record must be distinct";
    let lst = OldUtils.assoc_map (fun (e, _) -> e) (OldUtils.assoc_map (type_pattern st) lst) in
    Ctor.precord ~loc fld lst, st
  | Untyped.PVariant (lbl, p) ->
    begin match Tctx.infer_variant lbl with
      | None -> Error.typing ~loc "Unbound constructor %s" lbl
      | Some (ty, arg_ty) ->
        begin match p, arg_ty with
          | None, None -> Ctor.pvariant_none ~loc lbl ty, st
          | Some p, Some arg_ty ->
            let p, st = type_pattern st p in
            Ctor.pvariant_some ~loc lbl arg_ty ty p, st
          | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
          | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
        end
    end

(******************************)
(* ABSTRACTION TYPE INFERENCE *)
(******************************)

and type_abstraction st loc ctx (p, c) =
  let pat, st = type_pattern st p in
  let comp, st = type_comp_ctx st (ctx @ (Scheme.get_context pat.Typed.scheme)) c in
  Ctor.abstraction ~loc pat comp, st

and type_abstraction2 st loc ctx (p1, p2, c) =
  let pat1, st = type_pattern st p1 in
  let pat2, st = type_pattern st p2 in
  let comp, st = type_comp_ctx st (ctx @ (Scheme.get_context pat1.Typed.scheme) @ (Scheme.get_context pat2.Typed.scheme)) c in
  Ctor.abstraction2 ~loc pat1 pat2 comp

and let_rec_defs ~loc defs =
  let add_binding (x, a) (poly_tys, ctx) =
    let ctx_a, (ty_p, drty_c), cnstrs_a = a.Typed.scheme in
    let poly_tys = (x, Type.Arrow (ty_p, drty_c)) :: poly_tys in
    poly_tys, ctx_a @ ctx
  in
  let poly_tys, ctx = List.fold_right add_binding defs ([], []) in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.make ctx ty) poly_tys in
  poly_tyschs

and type_let_rec_defs ~loc st defs =
  let defs' = OldUtils.assoc_map (type_abstraction st loc []) defs in
  let defs' = OldUtils.assoc_map (fun (a, st) -> a) defs' in
  let poly_tyschs = let_rec_defs ~loc defs' in
  let st = add_multiple_defs poly_tyschs st in
  let defs' = OldUtils.assoc_map (type_abstraction st loc []) defs in
  let defs' = OldUtils.assoc_map (fun (a, st) -> a) defs' in
  defs', poly_tyschs, st

and let_defs ~loc defs =
  let add_binding (p, c) (poly_tys, ctx) =
    let ctx_p, ty_p, _ = p.Typed.scheme in
    let ctx_c, drty_c, _ = c.Typed.scheme in
    let ctx_let = Unification.unify_let (ctx_p, ty_p) (ctx_c, drty_c) in
    let poly_tys =
      match c.Typed.term with
      | Typed.Value _ ->
        ctx_let @ poly_tys
      | Typed.Apply _ | Typed.Match _ | Typed.Handle _ 
      | Typed.LetRec _ | Typed.Bind _ | Typed.Call _ ->
        ctx_let @ poly_tys
    in
    poly_tys, ctx_c @ ctx
  in
  let poly_tys, ctx = List.fold_right add_binding defs ([], []) in
  let poly_tyschs = OldUtils.assoc_map (fun ty -> Scheme.make ctx ty) poly_tys in
  poly_tyschs

and type_let_defs ~loc st defs =
  let defs' = List.map (fun (p, c) -> (type_pattern st p, type_comp st c)) defs in
  let defs' = List.map (fun ((p, _), (c, _)) -> (p, c)) defs' in
  let poly_tyschs = let_defs ~loc defs' in
  let st = add_multiple_defs poly_tyschs st in
  defs', poly_tyschs, st

(*****************************)
(* EXPRESSION TYPE INFERENCE *)
(*****************************)

(* Type an expression
    type_expr will annotate the terms with location information
*)
and type_expr st ctx {Untyped.term=expr; Untyped.location=loc} = type_plain_expr st loc ctx expr

(* Type a plain expression *)
and type_plain_expr st loc ctx = function
  | Untyped.Var x ->
    (* the parser only parses into Untyped.var and 
       does not distinguish between lambda-bound variables
       and let-bound variables. 
       Thus, we need to make this distinction ourselves.
       
       Lookup the variable in the context, which includes only
       lambda-bound variables.
       If we can find the variable, it is lambda-bound.
       Otherwise, check the (polymorphic) context 
    *)
    begin match OldUtils.lookup x ctx with
        | Some ty -> Ctor.lambdavar ~loc x ty, st
        | None -> Ctor.letvar ~loc x (get_var_scheme_env ~loc st x), st
      end
  | Untyped.Const const ->
    Ctor.const ~loc const, st
  | Untyped.Tuple es ->
    let els = List.map (fun (e, _) -> e) (List.map (type_expr st ctx) es) in
    Ctor.tuple ~loc els, st
  | Untyped.Record lst ->
    let lst = List.map (fun (f, (e, _)) -> (f, e)) (OldUtils.assoc_map (type_expr st ctx) lst) in
    Ctor.record ~loc lst, st
  | Untyped.Variant (lbl, e) ->
    let exp = OldUtils.option_map (fun (e, _) -> e) (OldUtils.option_map (type_expr st ctx) e) in
    Ctor.variant ~loc (lbl, exp), st
  | Untyped.Lambda (p, c) ->
    let pat, st = type_pattern st p in
    let comp, st = type_comp_ctx st (ctx @ (Scheme.get_context pat.Typed.scheme)) c in
    Ctor.lambda ~loc pat comp, st
  | Untyped.Effect eff ->
    let eff = infer_effect ~loc st eff in
    Ctor.effect ~loc eff, st
  | Untyped.Handler {
      effect_clauses=effect_cases;
      value_clause=value_case;
      finally_clause=finally_case;
    } ->
    let type_handler_clause (eff, (p1, p2, c)) =
      let eff = infer_effect ~loc:(c.Untyped.location) st eff in
      (eff, type_abstraction2 st loc ctx (p1, p2, c))
    in
    let typed_effect_clauses = OldUtils.map type_handler_clause effect_cases in
    let untyped_value_clause =
      match value_case with
        | Some a -> a
        | None -> Desugar.id_abstraction Location.unknown
    in
    let typed_value_clause, st = type_abstraction st loc ctx untyped_value_clause in
    (* let typed_finally_clause =  *)
    Ctor.handler ~loc typed_effect_clauses typed_value_clause, st

(******************************)
(* COMPUTATION TYPE INFERENCE *)
(******************************)

(* Type a computation
    type_comp will annotate the terms with location information
*)
and type_comp st {Untyped.term=comp; Untyped.location=loc} = type_plain_comp st loc [] comp

and type_comp_ctx st ctx {Untyped.term=comp; Untyped.location=loc} = type_plain_comp st loc ctx comp

(* Type a plain computation *)
and type_plain_comp st loc ctx = function
  | Untyped.Value e ->
    let typed_e, st = type_expr st ctx e in
    Ctor.value ~loc typed_e, st
  | Untyped.Match (e, es) ->
    let cases = List.map (fun (a, b) -> a) (List.map (type_abstraction st loc ctx) es) in
    let exp, st = (type_expr st ctx e) in
    Ctor.patmatch ~loc exp cases, st
  | Untyped.Apply (e1, e2) ->
    let expr1, st = type_expr st ctx e1 in
    let expr2, st = type_expr st ctx e2 in
    Ctor.apply ~loc expr1 expr2, st
  | Untyped.Handle (e, c) ->
    let exp, st = type_expr st ctx e in
    let comp, st = type_comp st c in
    Ctor.handle ~loc exp comp, st
  | Untyped.Let (defs, c) ->
    let defs, _, st = type_let_defs ~loc st defs in
    let c, st = type_comp st c in
    Ctor.letbinding ~loc defs c, st
  | Untyped.LetRec (defs, c) ->
    let defs, _, st = type_let_rec_defs ~loc st defs in
    let c, st = type_comp st c in
    Ctor.letrecbinding ~loc defs c, st

(***************************)
(* TOPLEVEL TYPE INFERENCE *)
(***************************)

let infer_top_let_rec ?loc st defs =
  let loc = backup_location loc [] in
  let defs, vars, st = type_let_rec_defs ~loc st defs in
  (* List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs; *)
  defs, vars, st

let infer_top_let ?loc st defs =
  let loc = backup_location loc [] in
  let defs, vars, st = type_let_defs ~loc st defs in
  (* List.iter (fun (_, (p, c)) -> Exhaust.is_irrefutable p; Exhaust.check_comp c) defs; *)
  defs, vars, st

(* Execute type inference for a toplevel command *)
let type_toplevel ~loc st = function
  (* Main toplevel command for toplevel computations *)
  | Untyped.Computation c ->
    (* Do not capture state since we do not want to persist it *)
    let c, _ = type_comp st c in
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
    let defs, vars, st = infer_top_let ~loc st defs in
    Typed.TopLet (defs, vars), st
  (* Top letrec command: let rec x = c1 in c2 *)
  | Untyped.TopLetRec defs ->
    let defs, vars, st = infer_top_let_rec ~loc st defs in
    Typed.TopLetRec (defs, vars), st
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
