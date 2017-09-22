module T = Type
module Typed = Typed
module Untyped = CoreSyntax

type state = {
  context : TypingEnv.t;
  effects : (Types.target_ty * Types.target_ty) Untyped.EffectMap.t
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


let rec make_target_effects effects =
  let new_effects = List.map (fun (x,_) ->  x ) effects in 
  let new_set = Types.list_to_effect_set new_effects in 
  Types.SetEmpty new_set


let rec source_to_target ty = 
  begin match ty with
    | T.Apply (ty_name, ([], _, _)) -> source_to_target (T.Basic ty_name)
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
  | Untyped.Effect eff -> 
        let (in_ty,out_ty) =  Untyped.EffectMap.find eff st.effects in
        let s = Types.list_to_effect_set [eff] in
        (Typed.Effect (eff,(in_ty,out_ty)) , Types.Arrow (in_ty,(out_ty,(Types.SetEmpty s))) , []) 
        
   | Untyped.Handler h -> 
        let in_ty_var = Params.fresh_ty_param () in 
        let in_dirt_var = Params.fresh_dirt_param () in
        let out_ty_var = Params.fresh_ty_param () in 
        let out_dirt_var = Params.fresh_dirt_param () in
        let in_ty = Types.Tyvar in_ty_var in 
        let in_dirt = Types.SetVar (Types.empty_effect_set, in_dirt_var) in 
        let out_ty = Types.Tyvar (out_ty_var) in 
        let out_dirt = Types.SetVar (Types.empty_effect_set, out_dirt_var) in 
        let Some (pv,cv) = h.value_clause in
        let new_ty_var = Params.fresh_ty_param () in
        let x_ty = Types.Tyvar new_ty_var in
        let Untyped.PVar x = pv.Untyped.term in
        let target_pattern = (type_pattern pv) in
        let new_st = add_def st x x_ty in
        let (cv_target, (b_r,delta_r), constraints_cr) = type_comp new_st cv in 
        let cons_1 = ((b_r,delta_r),(out_ty,out_dirt)) in 
        let coerp1 = Params.fresh_dirty_coercion_param () in 
        let omega_1 =  Typed.DirtyCoercionVar( coerp1 ) in
        let omega_cons_1 = Typed.DirtyOmega(coerp1,cons_1) in 
        let coerced_cv = Typed.annotate (Typed.CastComp(cv_target,omega_1)) cv_target.location in
        let cons_4 = (in_ty,x_ty) in
        let coerp4 = Params.fresh_ty_coercion_param () in 
        let omega_4 = Typed.TyCoercionVar(coerp4) in
        let omega_cons_4 = Typed.TyOmega (coerp4, cons_4) in 
        let y_var_name = Typed.Variable.fresh "fresh_var" in 
        let y = Typed.PVar (y_var_name ) in 
        let annot_y = Typed.annotate y Location.unknown in 
        let exp_y = Typed.annotate (Typed.Var y_var_name) Location.unknown in
        let coerced_y = Typed.annotate (Typed.CastExp(exp_y,omega_4)) exp_y.location in 
        let lambda_v_clause = Typed.annotate (Typed.Lambda((target_pattern, x_ty, coerced_cv))) coerced_cv.location in
        let application_v_clause =Typed.annotate (Typed.Apply (lambda_v_clause, coerced_y)) Location.unknown in 
        let target_v_clause = Typed.abstraction annot_y application_v_clause in 
        let mapper_function (eff,abs2) = 
            let (in_op_ty,out_op_ty) =  Untyped.EffectMap.find eff st.effects in
            let (x,k,c_op) = abs2 in
            let Untyped.PVar x_var = x.Untyped.term in
            let Untyped.PVar k_var = k.Untyped.term in
            let alpha_op = Types.Tyvar (Params.fresh_ty_param ()) in 
            let delta_op =  Types.SetVar (Types.empty_effect_set,Params.fresh_dirt_param ()) in 
            let tmp_st = add_def st x_var in_op_ty in
            let new_st = add_def tmp_st k_var (Types.Arrow(out_op_ty,(alpha_op,delta_op))) in 
            let (typed_c_op, typed_c_op_type, c_op_constraints) = type_comp new_st c_op in 
            let (out_op_ty,_) = typed_c_op_type in 
            let cons_2 =  (typed_c_op_type , (out_ty,out_dirt)) in
            let cons_3 =  ( (Types.Arrow (out_op_ty, (out_ty,out_dirt))), (Types.Arrow (out_op_ty , (alpha_op,delta_op))) ) in 
            let coerp2 = Params.fresh_dirty_coercion_param () in 
            let coerp3 = Params.fresh_ty_coercion_param () in
            let omega_2 = Typed.DirtyCoercionVar( coerp2 ) in
            let omega_3 = Typed.TyCoercionVar( coerp3 ) in 
            let cons_omega_2 = Typed.DirtyOmega (coerp2,cons_2) in 
            let cons_omega_3 = Typed.TyOmega (coerp3, cons_3) in 
            let coerced_c_op = Typed.annotate (Typed.CastComp (typed_c_op,omega_2)) typed_c_op.location in 
            let l_var_name = Typed.Variable.fresh "fresh_var" in 
            let l = Typed.PVar (l_var_name ) in 
            let annot_l = Typed.annotate l Location.unknown in
            let exp_l = Typed.annotate (Typed.Var l_var_name) Location.unknown in 
            let coerced_l = Typed.annotate (Typed.CastExp (exp_l ,omega_3)) Location.unknown in
            let lambda = Typed.annotate (Typed.Lambda ((type_pattern k), out_op_ty, coerced_c_op)) coerced_c_op.location in 
            let application = Typed.annotate (Typed.Apply (lambda,coerced_l)) lambda.location in
            let final_abstraction2 = Typed.abstraction2 (type_pattern x ) annot_l  application in
            let tagert_effect = (eff, (in_op_ty,out_op_ty)) in 
            let operation_clause = ( tagert_effect, final_abstraction2) in 
            (operation_clause, (List.append c_op_constraints [ cons_omega_2;cons_omega_3])) in
        let map_list = OldUtils.map mapper_function h.effect_clauses in 
        let op_clauses = OldUtils.map (fun (x,_) -> x) map_list in
        let target_handler = 
            {
            Typed.effect_clauses = op_clauses;
            value_clause = target_v_clause;
            } in
        let target_type = Types.Handler ((in_ty,in_dirt), (out_ty,out_dirt)) in 
        let target_handler = Typed.annotate (Typed.Handler target_handler) Location.unknown in 
        let for_set_handlers_ops = List.map (fun ((eff,(_,_)),_)-> eff) op_clauses in 
        let ops_set = Types.list_to_effect_set for_set_handlers_ops in 
        let handlers_ops = Types.SetVar (ops_set,out_dirt_var) in 
        let cons_5 = (in_dirt, handlers_ops) in
        let coerp5 = Params.fresh_dirt_coercion_param () in
        let omega_5 = Typed.DirtCoercionVar (coerp5) in 
        let omega_cons_5 = Typed.DirtOmega (coerp5,cons_5) in  
        let in_handler_coercion = Typed.BangCoercion ((Typed.ReflTy ((Types.Tyvar in_ty_var))), omega_5) in 
        let out_handler_dirt = Types.SetVar (Types.empty_effect_set , out_dirt_var) in
        let out_handler_coercion = Typed.BangCoercion ((Typed.ReflTy((Types.Tyvar out_ty_var))), Typed.ReflDirt(out_handler_dirt)) in 
        let handler_coercion = Typed.HandlerCoercion (in_handler_coercion, out_handler_coercion) in 
        let constraints = List.append ( List.append constraints_cr [omega_cons_5;omega_cons_1;omega_cons_4] ) 
                          (List.flatten (OldUtils.map (fun(_,x) -> x) map_list)) in 
        let coerced_handler = Typed.CastExp (target_handler, handler_coercion) in  
        (coerced_handler,target_type,constraints)



and type_comp st {Untyped.term=comp; Untyped.location=loc} =
  let c, ttype, constraints = type_plain_comp st comp in
  Typed.annotate c loc, ttype, constraints
and type_plain_comp st = function
  | Untyped.Value e ->
      let (typed_e, tt, constraints) = type_expr st e in
      (Typed.Value typed_e, (tt, (Types.SetEmpty Types.empty_effect_set)) ,constraints)
  | Untyped.Match (e, cases) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
  | Untyped.Apply (e1, e2) -> 
      Print.debug "in infer apply";
      let (typed_e1, tt_1, constraints_1) = type_expr st e1 in
      let (typed_e2, tt_2, constraints_2) = type_expr st e2 in
      Print.debug "e1 apply type : %t" (Types.print_target_ty tt_1);
      Print.debug "e2 apply type : %t" (Types.print_target_ty tt_2);
      begin match typed_e1.term with
      | Typed.Effect (eff, (eff_in,eff_out)) ->
           let cons1 = (tt_2, eff_in) in
           let coerp1 = Params.fresh_ty_coercion_param () in 
           let e2_coerced = Typed.annotate (Typed.CastExp (typed_e2, Typed.TyCoercionVar( coerp1 ))) typed_e1.location in
           let omega_cons_1 = Typed.TyOmega (coerp1,cons1) in 
           let constraints = List.append [omega_cons_1] constraints_2 in
           let dirt_of_out_ty = Types.list_to_effect_set [eff] in 
           (Typed.Op ( (eff, (eff_in,eff_out)) ,e2_coerced), (eff_out, (Types.SetEmpty dirt_of_out_ty)), constraints)
      | _ ->
          let new_ty_var = Types.Tyvar (Params.fresh_ty_param ()) in 
          let new_ty_var_2 = Types.Tyvar (Params.fresh_ty_param ()) in
          let new_dirt_var = Types.SetVar (Types.empty_effect_set, (Params.fresh_dirt_param ())) in 
          let fresh_dirty_ty =  (new_ty_var_2, new_dirt_var) in 
          let cons1 = (tt_1 , Types.Arrow (new_ty_var, fresh_dirty_ty)) in
          let cons2 = (tt_2, new_ty_var) in
          let coerp1 = Params.fresh_ty_coercion_param () in
          let coerp2 = Params.fresh_ty_coercion_param () in 
          let omega_cons_1 = Typed.TyOmega (coerp1,cons1) in
          let omega_cons_2 = Typed.TyOmega (coerp2,cons2) in
          let constraints = List.append [omega_cons_1;omega_cons_2] (List.append constraints_1 constraints_2) in 
          let e1_coerced = Typed.annotate (Typed.CastExp (typed_e1, Typed.TyCoercionVar( coerp1))) typed_e1.location in 
          let e2_coerced = Typed.annotate (Typed.CastExp (typed_e2,  Typed.TyCoercionVar( coerp2))) typed_e2.location in 
          ( (Typed.Apply (e1_coerced,e2_coerced) ), fresh_dirty_ty , constraints)
      end
   | Untyped.Handle (e, c) ->
      let alpha_2 = Types.Tyvar (Params.fresh_ty_param ()) in
      let alpha_1 = Types.Tyvar (Params.fresh_ty_param ()) in
      let gamma_1 = Types.SetVar (Types.empty_effect_set, (Params.fresh_dirt_param ())) in 
      let gamma_2 = Types.SetVar (Types.empty_effect_set, (Params.fresh_dirt_param ())) in
      let dirty_1 = (alpha_1, gamma_1) in 
      let dirty_2 = (alpha_2, gamma_2) in
      let (typed_exp,exp_type,exp_constraints) = type_expr st e in
      let (typed_comp,comp_dirty_type,comp_constraints) = type_comp st c in
      let (comp_type,comp_dirt) = comp_dirty_type in
      let cons1 = (exp_type, (Types.Handler (dirty_1, dirty_2))) in
      let cons2 = (comp_type, alpha_1) in
      let cons3 = (comp_dirt, gamma_1) in 
      let coerp1 = Params.fresh_ty_coercion_param () in
      let coerp2 = Params.fresh_ty_coercion_param () in 
      let coerp3 = Params.fresh_dirt_coercion_param () in
      let coer1 = Typed.TyCoercionVar( coerp1) in
      let coer2 = Typed.TyCoercionVar( coerp2) in
      let coer3 = Typed.DirtCoercionVar( coerp3) in 
      let omega_cons_1 = Typed.TyOmega (coerp1,cons1) in
      let omega_cons_2 = Typed.TyOmega (coerp2,cons2) in
      let omega_cons_3 = Typed.DirtOmega (coerp3,cons3) in
      let coer_exp = Typed.annotate (Typed.CastExp (typed_exp,coer1)) typed_exp.location in
      let coer_comp =  Typed.annotate (Typed.CastComp (typed_comp, Typed.BangCoercion (coer2,coer3))) typed_comp.location in
      let constraints = List.append [omega_cons_1;omega_cons_2;omega_cons_3] (List.append exp_constraints comp_constraints) in
      ((Typed.Handle (coer_exp, coer_comp)) , dirty_2 , constraints)

  
  | Untyped.Let (defs, c_2) -> 
    let [(p_def, c_1)] = defs in 
    let (typed_c1,(type_c1,dirt_c1),cons_c1) = type_comp st c_1 in
    let Untyped.PVar x = p_def.Untyped.term in
    let new_st = add_def st x type_c1 in 
    let (typed_c2,(type_c2,dirt_c2),cons_c2) = type_comp new_st c_2 in 
    let new_dirt_var = Types.SetVar (Types.empty_effect_set, (Params.fresh_dirt_param ())) in 
    let cons1 = (dirt_c1,new_dirt_var) in
    let cons2 = (dirt_c2,new_dirt_var) in
    let coerp1 = Params.fresh_dirt_coercion_param () in
    let coerp2 = Params.fresh_dirt_coercion_param () in
    let coer1 = Typed.DirtCoercionVar(coerp1) in 
    let coer2 = Typed.DirtCoercionVar(coerp2) in 
    let omega_cons_1 = Typed.DirtOmega (coerp1,cons1) in
    let omega_cons_2 = Typed.DirtOmega (coerp2,cons2) in
    let coer_c1 = Typed.annotate (Typed.CastComp_dirt (typed_c1, coer1) ) typed_c1.location in  
    let coer_c2 = Typed.annotate (Typed.CastComp_dirt (typed_c2, coer2) ) typed_c2.location in
    let typed_pattern = type_pattern p_def in 
    let abstraction = Typed.annotate  (typed_pattern,coer_c2) (typed_c2.location) in 
    let constraints = List.append [omega_cons_1;omega_cons_2] (List.append cons_c1 cons_c2) in
    ((Typed.Bind (coer_c1,abstraction)), (type_c2,new_dirt_var), constraints) 

  | Untyped.LetRec (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)


let type_toplevel ~loc st = function
  | Untyped.Computation c ->
    let ct, (ttype,dirt),constraints = type_comp st c in
    let x::xs = constraints in 
    Print.debug "Single constraint : %t" (Typed.print_omega_ct x);
    Print.debug "Computation : %t" (Typed.print_computation ct);
    Print.debug "Computation type : %t ! {%t}" (Types.print_target_ty ttype) (Types.print_target_dirt dirt);
    let (sub,final) = Unification.unify ([],[],constraints) in

    Typed.Computation ct, st
  | Untyped.Use fn ->
    Typed.Use fn, st
  | Untyped.Reset ->
    Typed.Reset, st
  | Untyped.Help ->
    Typed.Help, st
  | Untyped.Quit ->
    Typed.Quit, st
  | Untyped.DefEffect ( eff , (ty1 , ty2) ) ->
    Print.debug "%t ----> %t"  (Type.print_ty ty1) (Type.print_ty ty2);
    let target_ty1 = source_to_target ty1 in 
    let target_ty2 = source_to_target ty2 in
    let new_st =  add_effect st eff (target_ty1, target_ty2) in 
    Typed.DefEffect( eff , (target_ty1 , target_ty2) ) , new_st

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
