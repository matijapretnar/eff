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
    let target_ty = begin match TypingEnv.lookup st.context x with
      | Some ty_schi ->  ty_schi
      | None -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      end in
      (Typed.Var x, target_ty, [])
  | Untyped.Const const -> 
        begin match const with
        | Integer _ -> (Typed.Const const, Types.PrimTy IntTy, [])
        | String _ -> (Typed.Const const, Types.PrimTy StringTy, [])
        | Boolean _ -> (Typed.Const const, Types.PrimTy BoolTy, [])
        | Float _ -> (Typed.Const const, Types.PrimTy FloatTy, [])
      end 
      
  | Untyped.Tuple es -> 
      let target_list = (List.map (type_expr st) es) in
      let target_terms = Typed.Tuple (List.fold_right (fun (x,_,_) xs -> x ::xs )  target_list []) in
      let target_types = Types.Tuple(List.fold_right (fun (_,x,_) xs -> x::xs )  target_list []) in
      let target_cons = List.fold_right (fun (_,_,x) xs -> List.append x xs )  target_list [] in
      (target_terms, target_types, target_cons) 
  | Untyped.Record lst -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Variant (lbl, e) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Lambda a -> 
        Print.debug "in infer lambda";
        let (p,c) = a in 
        let new_ty_var = Params.fresh_ty_param () in
        let in_ty = Types.Tyvar new_ty_var in
        let Untyped.PVar x = p.Untyped.term in
        let target_pattern = (type_pattern p) in
        let new_st = add_def st x in_ty in
        let (target_comp_term,target_comp_ty,target_comp_cons)= (type_comp new_st c) in
        let target_ty = Types.Arrow (in_ty, target_comp_ty) in
        let target_lambda = Typed.Lambda (target_pattern,in_ty,target_comp_term) in 
        Print.debug "lambda ty: %t" (Types.print_target_ty target_ty);
        (target_lambda,target_ty,target_comp_cons)
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
      Print.debug "in infer apply";
      let (typed_e1, tt_1, constraints_1) = type_expr st e1 in
      let (typed_e2, tt_2, constraints_2) = type_expr st e2 in
      Print.debug "e1 apply type : %t" (Types.print_target_ty tt_1);
      Print.debug "e2 apply type : %t" (Types.print_target_ty tt_2);
      let new_ty_var = Types.Tyvar (Params.fresh_ty_param ()) in 
      let new_ty_var_2 = Types.Tyvar (Params.fresh_ty_param ()) in
      let new_dirt_var = Types.DirtVar (Params.fresh_dirt_param ()) in 
      let fresh_dirty_ty =  (new_ty_var_2, new_dirt_var) in 
      let cons1 = Types.LeqTy (tt_1 , Types.Arrow (new_ty_var, fresh_dirty_ty)) in
      let cons2 = Types.LeqTy (tt_2, new_ty_var) in 
      let constraints = List.append [cons1;cons2] (List.append constraints_1 constraints_2) in 
      let e1_coerced = Typed.annotate (Typed.CastExp (typed_e1, Typed.TyCoercionVar( (Params.fresh_ty_coercion_param ()), cons1))) typed_e1.location in 
      let e2_coerced = Typed.annotate (Typed.CastExp (typed_e2,  Typed.TyCoercionVar( (Params.fresh_ty_coercion_param ()), cons2))) typed_e2.location in 
      ( (Typed.Apply (e1_coerced,e2_coerced) ), fresh_dirty_ty , constraints)
  
  | Untyped.Handle (e, c) ->
      let alpha_2 = Types.Tyvar (Params.fresh_ty_param ()) in
      let alpha_1 = Types.Tyvar (Params.fresh_ty_param ()) in
      let gamma_1 = Types.DirtVar (Params.fresh_dirt_param ()) in 
      let gamma_2 = Types.DirtVar (Params.fresh_dirt_param ()) in
      let dirty_1 = (alpha_1, gamma_1) in 
      let dirty_2 = (alpha_2, gamma_2) in
      let (typed_exp,exp_type,exp_constraints) = type_expr st e in
      let (typed_comp,comp_dirty_type,comp_constraints) = type_comp st c in
      let (comp_type,comp_dirt) = comp_dirty_type in
      let cons1 = Types.LeqTy (exp_type, (Types.Handler (dirty_1, dirty_2))) in
      let cons2 = Types.LeqTy (comp_type, alpha_1) in
      let cons3 = Types.LeqDirt (comp_dirt, gamma_1) in 
      let coer1 = Typed.TyCoercionVar( (Params.fresh_ty_coercion_param ()), cons1) in
      let coer2 = Typed.TyCoercionVar( (Params.fresh_ty_coercion_param ()), cons2) in
      let coer3 = Typed.DirtCoercionVar( (Params.fresh_dirt_coercion_param ()), cons3) in 
      let coer_exp = Typed.annotate (Typed.CastExp (typed_exp,coer1)) typed_exp.location in
      let coer_comp =  Typed.annotate (Typed.CastComp (typed_comp, Typed.BangCoercion (coer2,coer3))) typed_comp.location in
      let constraints = List.append [cons1;cons2;cons3] (List.append exp_constraints comp_constraints) in
      ((Typed.Handle (coer_exp, coer_comp)) , dirty_2 , constraints)

  
  | Untyped.Let (defs, c_2) -> 
    let [(p_def, c_1)] = defs in 
    let (typed_c1,(type_c1,dirt_c1),cons_c1) = type_comp st c_1 in
    let Untyped.PVar x = p_def.Untyped.term in
    let new_st = add_def st x type_c1 in 
    let (typed_c2,(type_c2,dirt_c2),cons_c2) = type_comp new_st c_2 in 
    let new_dirt_var = Types.DirtVar (Params.fresh_dirt_param ()) in 
    let cons1 = Types.LeqDirt (dirt_c1,new_dirt_var) in
    let cons2 = Types.LeqDirt (dirt_c2,new_dirt_var) in
    let coer1 = Typed.DirtCoercionVar((Params.fresh_dirt_coercion_param ()), cons1) in 
    let coer2 = Typed.DirtCoercionVar((Params.fresh_dirt_coercion_param ()), cons2) in 
    let coer_c1 = Typed.annotate (Typed.CastComp_dirt (typed_c1, coer1) ) typed_c1.location in  
    let coer_c2 = Typed.annotate (Typed.CastComp_dirt (typed_c2, coer2) ) typed_c2.location in
    let typed_pattern = type_pattern p_def in 
    let abstraction = Typed.annotate  (typed_pattern,coer_c2) (typed_c2.location) in 
    let constraints = List.append [cons1;cons2] (List.append cons_c1 cons_c2) in
    ((Typed.Bind (coer_c1,abstraction)), (type_c2,new_dirt_var), constraints) 

  | Untyped.LetRec (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)


let type_toplevel ~loc st = function
  | Untyped.Computation c ->
    let c, (ttype,_),constraints = type_comp st c in
    Print.debug "Computation type : %t" (Types.print_target_ty ttype);
    List.map (fun cons -> Print.debug "constraint: %t" (Types.print_constraint cons)) constraints;
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
