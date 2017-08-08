module T = Type

let ty_less = Scheme.ty_less
let dirt_less = Scheme.dirt_less
let dirty_less = Scheme.dirty_less
let just = Scheme.just
let trim_context = Scheme.trim_context

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


let rec make_target_effects effects =
  begin match effects with
   | [] -> Types.Empty
   | ((x,_)::xs) -> Types.Union (x ,  make_target_effects xs)
 end


let rec source_to_target ty = 
  begin match ty with
    | T.Apply (_,_) -> assert false
    | T.Param x -> Types.Tyvar x
    | T.Basic s -> begin match s with
                   | "int" -> Types.PrimTy IntTy
                   | "string" -> Types.PrimTy StringTy
                   | "bool" -> Types.PrimTy BoolTy
                   | "float" -> Types.PrimTy FloatTy
                   end
    | T.Tuple l -> let new_l = List.map source_to_target l
                   in Types.Tuple new_l
    | T.Arrow  (ty1 ,dirty1) -> let dirtyt = source_to_target_dirty dirty1
                             in let tyt = source_to_target ty1
                             in Types.Arrow (tyt,dirtyt) 
    | T.Handler (dirty1, dirty2) -> Types.Handler (source_to_target_dirty dirty1, source_to_target_dirty dirty2)
  end

and source_to_target_dirty dirty_type = 
  let (ty,dirt) = dirty_type in 
  let new_ty = source_to_target ty in
  let ops = dirt.ops in
  let new_dirt = make_target_effects ops in 
  (new_ty, new_dirt)  


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
  let pat = match p.Untyped.term with

    | Untyped.PVar x ->
        Typed.PVar x

    | Untyped.PAs (p, x) ->
        Typed.PAs (type_pattern p, x)

    | Untyped.PNonbinding ->
        Typed.PNonbinding

    | Untyped.PConst const ->
        Typed.PConst const

    | Untyped.PTuple ps ->
        Typed.PTuple (List.map type_pattern ps)

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
  let e, ttype, constraints = type_plain_expr st expr in
  Typed.annotate e loc, ttype, constraints
and type_plain_expr st = function
  | Untyped.Var x ->
    let ty_sch = begin match TypingEnv.lookup st.context x with
      | Some ty_schi -> let (_,v_source_type,_) = ty_schi in 
                       let v_target_type = source_to_target v_source_type in 
                       (Typed.Var x, v_target_type, [])
      | None -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      end
    in
    assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Const const -> 
        begin match const with
        | Integer _ -> (Typed.Const const, Types.PrimTy IntTy, [])
        | String _ -> (Typed.Const const, Types.PrimTy StringTy, [])
        | Boolean _ -> (Typed.Const const, Types.PrimTy BoolTy, [])
        | Float _ -> (Typed.Const const, Types.PrimTy FloatTy, [])
      end 
      
  | Untyped.Tuple es -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Record lst -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Variant (lbl, e) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Lambda a -> 
        Print.debug "in infer lambda";
        let (p,c) = a in 
        let new_ty_var = Params.fresh_ty_param () in
        let in_ty = Types.Tyvar new_ty_var in
        let target_pattern = (type_pattern p) in
        let (target_comp_term,target_comp_ty,target_comp_cons)= (type_comp st c) in
        (*need to extend the environment*)
        let target_ty = Types.Arrow (in_ty, target_comp_ty) in
        let target_lambda = Typed.Lambda (target_pattern,in_ty,target_comp_term) in 
        (target_lambda,target_ty,[])
  | Untyped.Effect eff -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Handler h -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
and type_comp st {Untyped.term=comp; Untyped.location=loc} =
  let c, ttype, constraints = type_plain_comp st comp in
  Typed.annotate c loc, ttype, constraints
and type_plain_comp st = function
  | Untyped.Value e ->
      let (typed_e, tt, constraints) = type_expr st e in
      (Typed.Value typed_e, (tt, Types.Empty) ,constraints)
  | Untyped.Match (e, cases) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Apply (e1, e2) -> 
      let (typed_e1, tt_1, constraints_1) = type_expr st e1 in
      let (typed_e2, tt_2, constraints_2) = type_expr st e2 in 
      Print.debug "in infer apply";
      ((Typed.Apply (typed_e1,typed_e2)), (tt_2,Types.Empty), [])
  | Untyped.Handle (e, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Let (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.LetRec (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)


let type_toplevel ~loc st = function
  | Untyped.Computation c ->
    let c, _,constraints = type_comp st c in
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
