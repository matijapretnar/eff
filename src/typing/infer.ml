module T = Type
module Typed = Typed
module Untyped = CoreSyntax


module TyVarSet = Set.Make (struct
                             type t = Params.ty_param
                             let compare = compare
                           end);;

module DirtVarSet = Set.Make (struct
                             type t = Params.dirt_param
                             let compare = compare
                           end);;


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

let print_env env = 
  List.map (fun (x, ty_sch) -> Print.debug "%t : %t" (Typed.print_variable x ) (Types.print_target_ty ty_sch) ;) env

let constraint_free_ty_vars cons = 
  begin match cons with 
  | Typed.TyOmega (_,(ty1,ty2)) ->
        begin match (ty1,ty2) with 
        | (Types.Tyvar a, Types.Tyvar b) -> [a;b]
        | (Types.Tyvar a, _ ) -> [a]
        | (_, Types.Tyvar a) -> [a]
        end
  | _ -> []
  end

let constraint_free_dirt_vars cons = 
  begin match cons with 
  | Typed.DirtOmega (_, (ty1, ty2)) ->
        begin match (ty1,ty2) with 
        | (Types.SetVar (_,a), Types.SetVar (_,b)) -> [a;b]
        | (Types.SetVar (_,a), _ ) -> [a]
        | (_, Types.SetVar (_,a)) -> [a]
        end
  | _ -> []
  end


let rec free_ty_vars_ty t = 
 begin match t with 
 | Types.Tyvar x -> [x]
 | Types.Arrow (a,c) -> (free_ty_vars_ty a) @ (free_ty_var_dirty c)
 | Types.Tuple tup -> List.flatten (List.map (free_ty_vars_ty) tup)
 | Types.Handler (c1,c2) -> (free_ty_var_dirty c1) @ (free_ty_var_dirty c2)
 | Types.PrimTy _ -> []
 | Types.QualTy ( _, a) -> free_ty_vars_ty a
 | Types.QualDirt ( _, a) -> free_ty_vars_ty a
 | Types.TySchemeTy (ty_param,a) -> 
  let free_a = free_ty_vars_ty a in 
  List.filter (fun x -> not (List.mem x [ty_param])) free_a
 | Types.TySchemeDirt (dirt_param,a) -> free_ty_vars_ty a 
 end
and
free_ty_var_dirty (a,d) = free_ty_vars_ty a 

let rec free_dirt_vars_ty t = 
 begin match t with 
 | Types.Arrow (a,c) -> (free_dirt_vars_ty a) @ (free_dirt_vars_dirty c)
 | Types.Tuple tup -> List.flatten (List.map (free_dirt_vars_ty) tup)
 | Types.Handler (c1,c2) -> (free_dirt_vars_dirty c1) @ (free_dirt_vars_dirty c2)
 | Types.QualTy ( _, a) -> free_dirt_vars_ty a
 | Types.QualDirt ( _, a) -> free_dirt_vars_ty a
 | Types.TySchemeTy (ty_param,a) ->  free_dirt_vars_ty a
 | Types.TySchemeDirt (dirt_param,a) -> 
      let free_a = free_dirt_vars_ty a in 
        List.filter (fun x -> not (List.mem x [dirt_param])) free_a
 | _ -> []
 end
and
free_dirt_vars_dirty (a,d) = free_dirt_vars_dirt d
and
free_dirt_vars_dirt d = 
 begin match d with 
 | Types.SetVar(_,sv) -> [sv]
 | _ -> []
 end 

let rec state_free_ty_vars st = 
  List.fold_right (fun (_,ty) acc-> List.append (free_ty_vars_ty ty) acc) st []


let rec state_free_dirt_vars st = 
  List.fold_right (fun (_,ty) acc-> List.append (free_dirt_vars_ty ty) acc) st []


let set_of_ty_list = List.fold_left (fun acc x -> TyVarSet.add x acc) TyVarSet.empty

let set_of_dirt_list = List.fold_left (fun acc x -> DirtVarSet.add x acc) DirtVarSet.empty

let splitter st constraints simple_ty =
   Print.debug "Splitter Input Constraints: ";
   Unification.print_c_list constraints;
   Print.debug "Splitter Input Ty: %t" (Types.print_target_ty simple_ty);
   Print.debug "Splitter Env :";
   print_env st ;
   let simple_ty_freevars_ty = set_of_ty_list (free_ty_vars_ty simple_ty) in 
   Print.debug "Simple type free vars: ";
   List.iter (fun x -> Print.debug "%t" (Params.print_ty_param x) ) (free_ty_vars_ty simple_ty);
   let simple_ty_freevars_dirt = set_of_dirt_list (free_dirt_vars_ty simple_ty) in
   let state_freevars_ty = set_of_ty_list (state_free_ty_vars st) in
    Print.debug "state free vars: ";
   List.iter (fun x -> Print.debug "%t" (Params.print_ty_param x) ) (state_free_ty_vars st); 
   let state_freevars_dirt = set_of_dirt_list (state_free_dirt_vars st) in
   let cons2 = List.filter (fun cons -> 
                                      let cons_freevars_ty = set_of_ty_list (constraint_free_ty_vars cons) in 
                                      let cons_freevars_dirt = set_of_dirt_list (constraint_free_dirt_vars cons) in
                                      let is_sub_ty = ( TyVarSet.subset cons_freevars_ty state_freevars_ty) || (TyVarSet.equal cons_freevars_ty state_freevars_ty) in 
                                      let is_sub_dirt = (DirtVarSet.subset cons_freevars_dirt state_freevars_dirt) || (DirtVarSet.equal cons_freevars_dirt state_freevars_dirt) in 
                                      is_sub_ty && is_sub_dirt
                           ) constraints in 
   let cons1 = OldUtils.diff constraints cons2 in 
   let constraints_freevars_ty= List.fold_right ( fun cons acc -> TyVarSet.union (set_of_ty_list (constraint_free_ty_vars cons)) acc ) constraints TyVarSet.empty in 
   let constraints_freevars_dirt= List.fold_right ( fun cons acc -> DirtVarSet.union (set_of_dirt_list (constraint_free_dirt_vars cons)) acc ) constraints DirtVarSet.empty in
   let alpha_list = TyVarSet.elements (TyVarSet.diff (TyVarSet.union constraints_freevars_ty simple_ty_freevars_ty) state_freevars_ty) in
   let delta_list = DirtVarSet.elements (DirtVarSet.diff (DirtVarSet.union constraints_freevars_dirt simple_ty_freevars_dirt) state_freevars_dirt) in
   Print.debug "Splitter output free_ty_vars: ";
   List.iter (fun x -> Print.debug "%t" (Params.print_ty_param x) ) alpha_list;
   Print.debug "Splitter output free_dirt_vars: ";
   List.iter (fun x -> Print.debug "%t" (Params.print_dirt_param x) ) delta_list;
   Print.debug "Splitter first constraints list :";
   Unification.print_c_list cons1;
   Print.debug "Splitter second constraints list :";
   Unification.print_c_list cons2;

   (alpha_list,delta_list,cons1,cons2) 


let rec get_sub_of_ty ty_sch = 
  begin match ty_sch with
  | Types.TySchemeTy (p,t) -> 
          let new_p = Params.fresh_ty_param () in 
          ( ((p,new_p) :: (fst (get_sub_of_ty t))) , (snd (get_sub_of_ty t) ) )
  | Types.TySchemeDirt(p,t) -> 
          let new_p = Params.fresh_dirt_param () in 
          ( (fst (get_sub_of_ty t)) , ((p,new_p) :: (snd (get_sub_of_ty t))))
  | _ -> ([],[])
  end


let rec get_basic_type ty_sch =
  begin match ty_sch with
  | Types.TySchemeTy (_,t) -> get_basic_type t
  | Types.TySchemeDirt(_,t) -> get_basic_type t
  | Types.QualTy(_,t) -> get_basic_type t
  | Types.QualDirt(_,t)-> get_basic_type t
  | t -> t
  end


let rec apply_sub_to_type ty_subs dirt_subs ty =
  begin match ty with
  | Types.Tyvar p -> 
      begin match (OldUtils.lookup p ty_subs) with
      | Some p' -> Types.Tyvar p'
      | None -> ty
      end
  
  | Types.Arrow (a,(b,d)) -> Types.Arrow ((apply_sub_to_type ty_subs dirt_subs a), ((apply_sub_to_type ty_subs dirt_subs b),(apply_sub_to_dirt dirt_subs d)))
  | Types.Tuple ty_list -> Types.Tuple (List.map ( fun x -> (apply_sub_to_type ty_subs dirt_subs x)) ty_list) 
  | Types.Handler ((a,b),(c,d)) -> Types.Handler (  ((apply_sub_to_type ty_subs dirt_subs a),(apply_sub_to_dirt dirt_subs b))  ,   ((apply_sub_to_type ty_subs dirt_subs c),(apply_sub_to_dirt dirt_subs d)) )
  | Types.PrimTy _ -> ty
  | _ -> assert false
  end
and apply_sub_to_dirt dirt_subs ty =
  begin match ty with 
  | Types.SetVar (s,p)->
      begin match (OldUtils.lookup p dirt_subs) with
      | Some p' -> Types.SetVar (s,p')
      | None -> ty
      end
  | x -> x
end


let rec get_applied_cons_from_ty ty_subs dirt_subs ty = 
  begin match ty with 
  | Types.TySchemeTy (_,t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.TySchemeDirt(_,t) -> get_applied_cons_from_ty ty_subs dirt_subs t
  | Types.QualTy(cons,t) -> 
              let (c1,c2) =  get_applied_cons_from_ty ty_subs dirt_subs t in
              let (ty1,ty2) =  cons in 
              let (newty1,newty2) = (apply_sub_to_type ty_subs dirt_subs ty1 , apply_sub_to_type ty_subs dirt_subs ty2) in 
              let new_omega = Params.fresh_ty_coercion_param () in 
              let new_cons = Typed.TyOmega (new_omega, (newty1,newty2) ) in
              (new_cons::c1 , c2 )
  | Types.QualDirt(cons,t)-> 
              let (c1,c2) =  get_applied_cons_from_ty ty_subs dirt_subs t in
              let (ty1,ty2) =  cons in 
              let (newty1,newty2) = (apply_sub_to_dirt dirt_subs ty1 , apply_sub_to_dirt dirt_subs ty2) in 
              let new_omega = Params.fresh_dirt_coercion_param () in 
              let new_cons = Typed.DirtOmega (new_omega, (newty1,newty2) ) in
              (c1 , new_cons::c2 )
  | _ -> [],[]
end

let apply_types ty_subs dirt_subs var ty_sch =
   let ty_apps = List.fold_left (fun a (_,b) -> (Typed.annotate (Typed.ApplyTyExp (a, Types.Tyvar b)) Location.unknown)  ) (Typed.annotate (Typed.Var var) Location.unknown) ty_subs in 
   let dirt_apps = List.fold_left (fun a (_,b) -> (Typed.annotate (Typed.ApplyDirtExp (a, Types.SetVar (Types.empty_effect_set ,b) )) Location.unknown)  ) ty_apps dirt_subs in 
   let (ty_cons,dirt_cons) = get_applied_cons_from_ty ty_subs dirt_subs ty_sch in 
   let ty_cons_apps = List.fold_left (fun a (Typed.TyOmega (omega, _ )) -> (Typed.annotate (Typed.ApplyTyCoercion (a, Typed.TyCoercionVar omega)) Location.unknown) ) dirt_apps ty_cons in 
   let dirt_cons_apps = List.fold_left (fun a (Typed.DirtOmega (omega, _ )) -> (Typed.annotate (Typed.ApplyDirtCoercion (a, Typed.DirtCoercionVar omega)) Location.unknown) ) ty_cons_apps dirt_cons in 
   (dirt_cons_apps , (ty_cons @ dirt_cons ))

let rec type_expr st {Untyped.term=expr; Untyped.location=loc} =
  let e, ttype, constraints = type_plain_expr st expr in
  Typed.annotate e loc, ttype, constraints
and type_plain_expr st = function
  | Untyped.Var x ->
    begin match TypingEnv.lookup st.context x with
      | Some ty_schi -> 
                let (bind_tyvar_sub,bind_dirtvar_sub) = get_sub_of_ty ty_schi in
                Print.debug "in Var";
                Print.debug " var : %t" (Typed.print_variable x);
                Print.debug " typeSch: %t " (Types.print_target_ty ty_schi);
                let basic_type = get_basic_type ty_schi in
                Print.debug "basicTy: %t" (Types.print_target_ty basic_type); 
                let applied_basic_type = apply_sub_to_type bind_tyvar_sub bind_dirtvar_sub basic_type in
                let (returned_x, returnd_cons) = apply_types bind_tyvar_sub bind_dirtvar_sub x ty_schi in 
                Print.debug "returned: %t" (Typed.print_expression returned_x) ;
                Print.debug "returned_type: %t" (Types.print_target_ty applied_basic_type);
                (returned_x.term , applied_basic_type, returnd_cons)
      | None -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)
      end
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
        let cons_1a =(b_r,out_ty) in 
        let cons_1b = (delta_r,out_dirt) in 
        let coerp1a = Params.fresh_ty_coercion_param () in 
        let coerp1b = Params.fresh_dirt_coercion_param () in 
        let omega_1a = Typed.TyCoercionVar coerp1a in 
        let omega_1b = Typed.DirtCoercionVar coerp1b in 
        let omega_cons_1a = Typed.TyOmega (coerp1a , cons_1a) in 
        let omega_cons_1b = Typed.DirtOmega (coerp1b, cons_1b) in 
        let coerced_cv = Typed.annotate (Typed.CastComp(cv_target,Typed.BangCoercion(omega_1a,omega_1b))) cv_target.location in
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
            let (c_op_ty,c_op_dirt) = typed_c_op_type in 
            let cons_2a = (c_op_ty,out_ty) in 
            let cons_2b = (c_op_dirt,out_dirt) in 
            let coerp2a = Params.fresh_ty_coercion_param () in 
            let coerp2b = Params.fresh_dirt_coercion_param () in 
            let omega_2a = Typed.TyCoercionVar (coerp2a) in 
            let omega_2b = Typed.DirtCoercionVar (coerp2b) in 
            let cons_omega_2a = Typed.TyOmega (coerp2a, cons_2a) in 
            let cons_omega_2b = Typed.DirtOmega (coerp2b, cons_2b) in 
            let cons_3 =  ( (Types.Arrow (out_op_ty, (out_ty,out_dirt))), (Types.Arrow (out_op_ty , (alpha_op,delta_op))) ) in 
            let coerp3 = Params.fresh_ty_coercion_param () in
            let omega_3 = Typed.TyCoercionVar( coerp3 ) in 
            let cons_omega_3 = Typed.TyOmega (coerp3, cons_3) in 
            let coerced_c_op = Typed.annotate (Typed.CastComp (typed_c_op,Typed.BangCoercion (omega_2a,omega_2b))) typed_c_op.location in 
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
            (operation_clause, (List.append c_op_constraints [ cons_omega_2a;cons_omega_2b;cons_omega_3])) in
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
        let constraints = List.append ( List.append constraints_cr [omega_cons_5;omega_cons_1a;omega_cons_1b;omega_cons_4] ) 
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
           let new_var = Typed.Variable.fresh "cont_bind" in
           let continuation_comp = Untyped.Value ( Untyped.annotate (Untyped.Var new_var) typed_e2.location ) in 
           let new_st = add_def st new_var eff_out in 
           let (typed_cont_comp, typed_cont_comp_dirty_ty, cont_comp_cons)= 
                    type_comp new_st (Untyped.annotate continuation_comp typed_e2.location) in 
           let (typed_comp_ty,typed_comp_dirt) = typed_cont_comp_dirty_ty in 
           let final_dirt = 
              begin match typed_comp_dirt with 
              | Types.SetVar (s,dv) -> Types.SetVar (Types.effect_set_union s (Types.list_to_effect_set [eff]), dv)
              | Types.SetEmpty s -> Types.SetEmpty (Types.effect_set_union s (Types.list_to_effect_set [eff]))
              end in 
          let cont_abstraction = Typed.annotate ((Typed.annotate (Typed.PVar new_var) typed_e2.location), typed_cont_comp) 
                                 typed_e2.location in
          ( Typed.Call( (eff, (eff_in,eff_out)) ,e2_coerced, cont_abstraction ),
            (typed_comp_ty,final_dirt),
            cont_comp_cons @ constraints)
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
     begin match c_1.term with 
     | Untyped.Value e_1 -> 
        let (typed_e1, type_e1,cons_e1) = type_expr st e_1 in 
        let (split_ty_vars, split_dirt_vars, split_cons1, split_cons2) = splitter (TypingEnv.return_context st.context) cons_e1 type_e1 in 
        let Untyped.PVar x = p_def.Untyped.term in
        let qual_ty = List.fold_right (fun cons acc -> 
                                          begin match cons with 
                                          | Typed.TyOmega(_,t) -> Types.QualTy (t,acc)
                                          | Typed.DirtOmega(_,t) -> Types.QualDirt(t,acc) 
                                          end 
                                      ) split_cons1 type_e1 in 
        let ty_sc_dirt = List.fold_right (fun cons acc -> Types.TySchemeDirt (cons,acc)) split_dirt_vars qual_ty in
        let ty_sc_ty = List.fold_right  (fun cons acc -> Types.TySchemeTy (cons,acc)) split_ty_vars ty_sc_dirt in 
        let new_st = add_def st x ty_sc_ty in 
        let (typed_c2,type_c2,cons_c2) = type_comp new_st c_2 in

        let var_exp = List.fold_right(fun cons acc -> 
                                          begin match cons with 
                                          | Typed.TyOmega(om,t) -> Typed.annotate (Typed.LambdaTyCoerVar (om,t,acc)) typed_c2.location
                                          | Typed.DirtOmega(om,t) -> Typed.annotate(Typed.LambdaDirtCoerVar(om,t,acc)) typed_c2.location
                                          end 
                                      ) split_cons1 typed_e1 in 
        let var_exp_dirt_lamda = List.fold_right (fun cons acc -> Typed.annotate ( Typed.BigLambdaDirt (cons,acc) ) typed_c2.location )  split_dirt_vars var_exp in
        let var_exp_ty_lambda = List.fold_right (fun cons acc -> Typed.annotate (Typed.BigLambdaTy (cons,acc) )typed_c2.location ) split_ty_vars var_exp_dirt_lamda in
        let return_term = Typed.LetVal (x, var_exp_ty_lambda, typed_c2) in 
        (return_term, type_c2 , (cons_c2 @ split_cons2))


     | _-> 
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
        let coer_c1 = Typed.annotate (Typed.CastComp (typed_c1, Typed.BangCoercion (Typed.ReflTy type_c1,coer1)) ) typed_c1.location in  
        let coer_c2 = Typed.annotate (Typed.CastComp (typed_c2, Typed.BangCoercion (Typed.ReflTy type_c2,coer2)) ) typed_c2.location in
        let typed_pattern = type_pattern p_def in 
        let abstraction = Typed.annotate  (typed_pattern,coer_c2) (typed_c2.location) in 
        let constraints = List.append [omega_cons_1;omega_cons_2] (List.append cons_c1 cons_c2) in
        ((Typed.Bind (coer_c1,abstraction)), (type_c2,new_dirt_var), constraints) 
     end 
  | Untyped.LetRec (defs, c) -> assert false (* in fact it is not yet implemented, but assert false gives us source location automatically *)


let type_toplevel ~loc st c =
    let ct, (ttype,dirt),constraints = type_comp st c in
    (* let x::xs = constraints in 
    Print.debug "Single constraint : %t" (Typed.print_omega_ct x); *)
    Print.debug "Computation : %t" (Typed.print_computation ct);
    Print.debug "Computation type : %t ! {%t}" (Types.print_target_ty ttype) (Types.print_target_dirt dirt);
    let (sub,final) = Unification.unify ([],[],constraints) in
    let ct' =  Unification.apply_substitution sub ct in
    Print.debug "New Computation : %t" (Typed.print_computation ct');
    let (tch_ty,tch_dirt) = TypeChecker.type_check_comp (TypeChecker.new_checker_state) ct'.term in 
    Print.debug "Type from Type Checker : %t ! %t" (Types.print_target_ty tch_ty) (Types.print_target_dirt tch_dirt);
    ct', st

let add_effect eff (ty1 , ty2) st =
    Print.debug "%t ----> %t"  (Type.print_ty ty1) (Type.print_ty ty2);
    let target_ty1 = source_to_target ty1 in 
    let target_ty2 = source_to_target ty2 in
    let new_st =  add_effect st eff (target_ty1, target_ty2) in 
    new_st
