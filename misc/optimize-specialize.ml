
(* var can be instantiated to anything *)

(* Try to specialize a recursive function f with continuation cont.
 * If the body is an abstraction, substitute all applications f v of f in cont with
 * a new variable f'. Then prefix let-bindings f' = f v to cont for all
 * substitutions.
 * `specialize_letrec` first checks if the LetRec has the right form to be
 * specialized. The actual specialization is done in `specialize`.
 * The specialize_comp/expr/abs functions traverse the syntax tree, searching
 * for abstractions and applications. They create the specializations, add them
 * to the assoc and substitute a fresh variable. *)
 let rec specialize_letrec (cont : Term.computation)
 ( (fvar : Term.variable),
   (argty : Type.ty),
   ((resty, resdt) : Type.dirty),
   ((p, fbody_c) : Term.abstraction) ) : Term.computation =
match fbody_c with
| Value fbody -> (
   match (resty, fbody) with
   (* | TySchemeTy _, BigLambdaTy _ -> specialize fvar fbody resty cont *)
   (* | TySchemeDirt _, BigLambdaDirt _ -> specialize fvar fbody resty cont *)
   (* | TySchemeSkel _, BigLambdaSkel _ -> specialize fvar fbody resty cont *)
   | QualTy _, LambdaTyCoerVar _ -> specialize fvar fbody resty cont
   | QualDirt _, LambdaDirtCoerVar _ -> specialize fvar fbody resty cont
   | _ ->
       (* Print.debug "SPEC: letrec body is not an abstraction"; *)
       cont)
| _ ->
   (* Print.debug "SPEC: letrec body is not a value"; *)
   cont

and specialize (fvar : Term.variable) (fbody : Term.expression)
 (resty : Type.ty) (cont : Term.computation) : Term.computation =
(* Define a referenced map that holds the substitutions. *)
let assoc = ref Assoc.empty in

let specialize_app (e : Term.expression) : Term.variable =
 (* check if the specialized version already exists *)
 match Assoc.lookup e !assoc with
 | Some f' -> f' (* already exists, substituting *)
 | None ->
     (* creating new specialization *)
     (* create a new variable name fv' *)
     let f' = CoreTypes.Variable.refresh fvar in
     (* add it to mapping *)
     assoc := Assoc.update e f' !assoc;
     f'
in

(* The following are tree traversal functions that look for the specializations *)
(* Specialize computations. *)
let rec specialize_comp c =
 match c with
 | Value e1 ->
     let e1' = specialize_expr e1 in
     Value e1'
 | LetVal (e1, a1) ->
     let e1' = specialize_expr e1 in
     let a1' = specialize_abs_with_ty a1 in
     LetVal (e1', a1')
 | LetRec (bs1, c1) ->
     let bs1' =
       List.map (fun (p, ty, dty, a1) -> (p, ty, dty, specialize_abs a1)) bs1
     in
     let c1' = specialize_comp c1 in
     LetRec (bs1', c1')
 | Match (e1, dty, abs1) ->
     let e1' = specialize_expr e1 in
     let abs1' = List.map specialize_abs abs1 in
     Match (e1', dty, abs1')
 | Apply (e1, e2) ->
     let e1' = specialize_expr e1 in
     let e2' = specialize_expr e2 in
     Apply (e1', e2')
 | Handle (e1, c1) ->
     let e1' = specialize_expr e1 in
     let c1' = specialize_comp c1 in
     Handle (e1', c1')
 | Call (eff, e1, a1) ->
     let e1' = specialize_expr e1 in
     let a1' = specialize_abs_with_ty a1 in
     Call (eff, e1', a1')
 | Op (eff, e1) ->
     let e1' = specialize_expr e1 in
     Op (eff, e1')
 | Bind (c1, a1) ->
     let c1' = specialize_comp c1 in
     let a1' = specialize_abs a1 in
     Bind (c1', a1')
 | CastComp (c1, dtyco) ->
     let c1' = specialize_comp c1 in
     CastComp (c1', dtyco)
and specialize_expr (e : expression) : expression =
 match e with
 | Var _ -> e
 (* | BuiltIn _ -> e *)
 | Const _ -> e
 | Tuple es ->
     let es' = List.map specialize_expr es in
     Tuple es'
 | Record _ -> failwith __LOC__
 | Variant (lab, e1) ->
     let e1' = specialize_expr e1 in
     Variant (lab, e1')
 | Lambda abs ->
     let abs' = specialize_abs_with_ty abs in
     Lambda abs'
 | Effect _ -> e
 | Handler _ -> e
 (* | BigLambdaTy (tvar, sk, e1) ->
     let e1' = specialize_expr e1 in
     BigLambdaTy (tvar, sk, e1') *)
 (* | BigLambdaDirt (dvar, e1) ->
     let e1' = specialize_expr e1 in
     BigLambdaDirt (dvar, e1') *)
 (* | BigLambdaSkel (evar, e1) ->
     let e1' = specialize_expr e1 in
     BigLambdaSkel (evar, e1') *)
 | CastExp (e1, tyco) ->
     let e1' = specialize_expr e1 in
     CastExp (e1', tyco)
 (* | ApplyTyExp (e1, ty1) -> (
     match ty1 with
     | TyParam _ ->
         (* Don't specialize with typarams *)
         let e1' = specialize_expr e1 in
         ApplyTyExp (e1', ty1)
     | _ -> (
         match (e1, fbody) with
         | Var g, BigLambdaTy (tyvar, evar, v) when g = fvar ->
             Var (specialize_app e)
         | _ ->
             let e1' = specialize_expr e1 in
             ApplyTyExp (e1', ty1))) *)
 | LambdaTyCoerVar (ctvar, ctty, e1) ->
     let e1' = specialize_expr e1 in
     LambdaTyCoerVar (ctvar, ctty, e1')
 | LambdaDirtCoerVar (ctvar, ctty, e1) ->
     let e1' = specialize_expr e1 in
     LambdaDirtCoerVar (ctvar, ctty, e1')
 (* | ApplyDirtExp (e1, d) -> (
     match d.row with
     | ParamRow _ ->
         (* Don't specialize with params *)
         let e1' = specialize_expr e1 in
         ApplyDirtExp (e1', d)
     | _ -> (
         match (e1, fbody) with
         | Var g, BigLambdaDirt (dvar, v) when g = fvar ->
             Var (specialize_app e)
         | _ ->
             let e1' = specialize_expr e1 in
             ApplyDirtExp (e1', d))) *)
 (* | ApplySkelExp (e1, sk) -> (
     match sk with
     | SkelParam _ ->
         (* Don't specialize with params *)
         let e1' = specialize_expr e1 in
         ApplySkelExp (e1', sk)
     | _ -> (
         match (e1, fbody) with
         | Var g, BigLambdaSkel (evar, v) when g = fvar ->
             Var (specialize_app e)
         | _ ->
             let e1' = specialize_expr e1 in
             ApplySkelExp (e1', sk))) *)
 | ApplyTyCoercion (e1, tyco) -> (
     match tyco with
     | TyCoercionVar _ ->
         (* Don't specialize with params *)
         let e1' = specialize_expr e1 in
         ApplyTyCoercion (e1', tyco)
     | _ -> (
         match (e1, fbody) with
         | Var g, LambdaTyCoerVar (ctvar, _, v) when g = fvar ->
             Var (specialize_app e)
         | _ ->
             let e1' = specialize_expr e1 in
             ApplyTyCoercion (e1', tyco)))
 | ApplyDirtCoercion (e1, dco) -> (
     match dco with
     | DirtCoercionVar _ ->
         (* Don't specialize with params *)
         let e1' = specialize_expr e1 in
         ApplyDirtCoercion (e1', dco)
     | _ -> (
         match (e1, fbody) with
         | Var g, LambdaDirtCoerVar (ctvar, _, v) when g = fvar ->
             Var (specialize_app e)
         | _ ->
             let e1' = specialize_expr e1 in
             ApplyDirtCoercion (e1', dco)))
and specialize_abs (p, c) = (p, specialize_comp c)
and specialize_abs_with_ty (p, ty, c) = (p, ty, specialize_comp c) in

(* End of the tree traversal functions *)

(* This function prefixes the specializations in cont, and applies some necessary substitutions. *)
let subst_spec (cont : Term.computation)
   ((app : Term.expression), (fvar' : Term.variable)) : Term.computation =
 match (fbody, resty, app) with
 (* | ( BigLambdaTy (typaram, _sk, v),
     TySchemeTy (typaram', _sk', ty1),
     ApplyTyExp (_var, ty2) ) ->
     assert (typaram = typaram');
     assert (_sk = _sk');
     Print.debug "BigLambdaTy: replacing %t by %t"
       (CoreTypes.TyParam.print typaram)
       (Type.print_ty ty2);
     let sub = Substitution.add_type_substitution_e typaram ty2 in
     (* v' = [T2/a]v *)
     let v' = Substitution.apply_substitutions_to_expression sub v in
     (* T1' = [T2/a]T1 *)
     let ty1' = Substitution.apply_substitutions_to_type sub ty1 in
     LetVal (v', (PVar fvar', ty1', cont)) *)
 (* | ( BigLambdaDirt (dirtparam, v),
     TySchemeDirt (dirtparam', ty),
     ApplyDirtExp (_var, dirt) ) ->
     assert (dirtparam = dirtparam');
     Print.debug "BigLambdaDirt: replacing %t by %t"
       (Type.DirtParam.print dirtparam)
       (Type.print_dirt dirt);
     let sub = Substitution.add_dirt_substitution_e dirtparam dirt in
     (* v' = [D/d]v *)
     let v' = Substitution.apply_substitutions_to_expression sub v in
     (* T' = [D/d]T *)
     let ty' = Substitution.apply_substitutions_to_type sub ty in
     LetVal (v', (PVar fvar', ty', cont)) *)
 (* | ( BigLambdaSkel (skparam, v),
     TySchemeSkel (skparam', ty),
     ApplySkelExp (_var, sk) ) ->
     assert (skparam = skparam');
     Print.debug "BigLambdaSkel: replacing %t by %t"
       (Type.SkelParam.print skparam)
       (Type.print_skeleton sk);
     let sub = Substitution.add_skel_param_substitution_e skparam sk in
     (* v' = [t/s]v *)
     let v' = Substitution.apply_substitutions_to_expression sub v in
     (* T' = [t/s]T *)
     let ty' = Substitution.apply_substitutions_to_type sub ty in
     LetVal (v', (PVar fvar', ty', cont)) *)
 | ( LambdaTyCoerVar (coparam, _ct_ty, v),
     QualTy (_ct_ty', ty),
     ApplyTyCoercion (_var, tyco) ) ->
     assert (_ct_ty = _ct_ty');
     (* Print.debug "LambdaTyCoerVar: replacing %t by %t"
        (Type.TyCoercionParam.print coparam)
        (Constraint.print_ty_coercion tyco); *)
     let sub = Substitution.add_type_coercion_e coparam tyco in
     (* v' = [y/w]v *)
     let v' = Substitution.apply_substitutions_to_expression sub v in
     (* T' = [y/w]T *)
     let ty' = Substitution.apply_substitutions_to_type sub ty in
     LetVal (v', (PVar fvar', ty', cont))
 | ( LambdaDirtCoerVar (coparam, _ct_dirt, v),
     QualDirt (_ct_dirt', ty),
     ApplyDirtCoercion (_var, dco) ) ->
     assert (_ct_dirt = _ct_dirt');
     (* Print.debug "LambdaDirtCoerVar: replacing %t by %t"
        (Type.DirtCoercionParam.print coparam)
        (Constraint.print_dirt_coercion dco); *)
     let sub = Substitution.add_dirt_var_coercion_e coparam dco in
     (* v' = [y/w]v *)
     let v' = Substitution.apply_substitutions_to_expression sub v in
     (* T' = [y/w]T *)
     let ty' = Substitution.apply_substitutions_to_type sub ty in
     LetVal (v', (PVar fvar', ty', cont))
 | _ ->
     (* This should not happen, it should be handled by the match in `specialize_letrec`. *)
     failwith __LOC__
in
(* Gather and substitute specializations *)
(* Print.debug "SPEC: specializing a letrec"; *)
let cont' = specialize_comp cont in
(* Prefix the new specializations as let-bindings for cont. *)
Assoc.fold_left subst_spec cont' !assoc



and reduce_comp st c =
  (* Print.debug "reduce_comp: %t" (Term.print_computation c); *)
  match c with
  | Handle (Handler h, c1) -> (
          match c1 with
          | Apply (e11, e12) -> (
              (* Print.debug "Looking for recursive function name"; *)
              match match_recursive_function st e11 with
              | Some (fvar, fty, fbody) ->
                  (*
                   handle C[f] e12 with H
                   >->
                   let rec f' : ty_{e12} -> dty_{handle C[f] e12 with H}
                        = fun x : ty_{e12} -> handle C[fbody] x with H
                   in f' e12
                *)
                  (* Print.debug "Found recursive function call"; *)
                  let dty_c = TypeChecker.check_computation st.tc_state c in
                  let ty_e12 = TypeChecker.check_expression st.tc_state e12 in
                  let fvar' = CoreTypes.Variable.refresh fvar in
                  let xvar = CoreTypes.Variable.new_fresh () "__x_of_rec__" in
                  let fty' = Arrow (ty_e12, dty_c) in
                  let st' =
                    {
                      st with
                      recursive_functions =
                        Assoc.remove fvar st.recursive_functions;
                      knot_functions =
                        Assoc.update fvar (e11, h, fvar') st.knot_functions;
                    }
                  in
                  let st'' = extend_var_type st' fvar' fty' in
                  let fbody' =
                    optimize_abstraction st'' ty_e12
                      ( PVar xvar,
                        Handle
                          ( e1,
                            Apply
                              ( Term.subst_expr
                                  (Assoc.of_list [ (fvar, refresh_expr fbody) ])
                                  e11,
                                Var xvar ) ) )
                  in
                  LetRec
                    ([ (fvar', ty_e12, dty_c, fbody') ], Apply (Var fvar', e12))
              | None -> (
                  match match_knot_function st e11 h with
                  | Some fvar' -> Apply (Var fvar', e12)
                  | None -> c))
      | _ -> c)



      let find_in_handlers_func_mem st f_name h_exp =
        let loc = h_exphh in
        let findres_cont_list = List.filter
                        (fun (h,old_f,new_f) -> (f_name == old_f) ) (st.handlers_functions_cont_mem) in
        let findres = List.filter
                        (fun (h,old_f,new_f) -> (f_name == old_f) ) st.handlers_functions_mem in
        begin match findres_cont_list with
        |(h,_,newf):: _ ->
                      if (alphaeq_handler_no_vc [] h h_exp)
                      then begin
                           let Handler hh = h in
                           (true, Some newf, Some hh.value_clause)
                           end
                      else begin
                      (true,None,None)
                    end
        | [] ->
              begin match findres with
              | [] -> (false,None,None)
              | [(h,_,newf)] ->
                  if (alphaeq_expr [] h h_exp)
                  then
                    (true,Some newf,None)
                  else begin
                    if (alphaeq_handler_no_vc [] h h_exp)
                    then begin
                      (* Print.debug ~loc:h_exp.Typedhh"ONLY VALUE CLAUSE IS DIFFERENT !! %t" (Term.print_expression h_exp); *)
                      let Handler hh = h in
                      (false,Some newf,Some hh.value_clause)
                    end
                    else
                      begin
                      (* Print.debug ~loc:h_exp.Typedhh"Conflicting specialization call on\n %t \n=====================================\n %t "  (Term.print_expression h_exp) (Term.print_expression h); *)
                      (true,None,None)
                      end
                  end
      
              end
        end
      

        
      
      let different_branch_specialized defs st =
        (* Print.debug "\n\nthe letrec defs size:- %i \n" (List.length defs); *)
        (* Print.debug "\n\nthe global size:- %i \n" (List.length !(st.handlers_functions_ref_mem)); *)
        let findresinlocal = fun f_name -> (
                        List.filter
                        (fun (h,old_f,new_f) ->
                            let Var vv = new_f in
                            (f_name == vv) )   (st.handlers_functions_mem)) in
        let findresinglobal = fun f_name -> (
                        List.filter
                        (fun (h,old_f,new_f) ->
                            let Var vv = new_f in
                            (f_name == vv) )   !(st.handlers_functions_ref_mem)) in
        let globalboollist =
            (List.map (fun (var,abs) ->
                  begin match findresinglobal var with
                  | [] -> false
                  | _ -> true
                  end) defs ) in
        let global_bool = List.fold_right (||) globalboollist false in
        let localboollist =
            (List.map (fun (var,abs) ->
                  begin match findresinlocal var with
                  | [] -> false
                  | (h,old_f,new_f) :: _ -> (* Print.debug "\n my old function :- %t \n" (Term.print_variable old_f); *)
                                            (* Print.debug "\n my new function :- %t \n" (Term.print_expression new_f);  *)
                                            true
                  end) defs ) in
        let local_bool = List.fold_right (||) localboollist false in
        (* Print.debug "LOCAL BOOL :- %b \n Global Bool :- %b\n\n" (local_bool) (global_bool); *)
        (global_bool && ( not local_bool) )
      




        and optimize_sub_comp st c =
        let loc = chh in
        match c with
        | LetRec (defs, c1) when different_branch_specialized defs st ->
          (* List.fold_right (fun (var,abs) st ->
            {st with letrec_memory = (var,abs) :: st.letrec_memory}) defs st; *)
            let [(var,abst)] = defs in
            (* Print.debug "\nst out length %i\n" (List.length (st.handlers_functions_mem) ); *)
            let findresinglobal = fun f_name -> (
                        List.filter
                        (fun (h,old_f,new_f) ->
                            let Var vv = new_f in
                            (f_name == vv) )   !(st.handlers_functions_ref_mem)) in
            begin match findresinglobal var with
            | [] -> let_rec' ~loc (Common.assoc_map (optimize_abs st) defs) (optimize_comp st c1)
            | (h,old_f,new_f) :: _ ->
            (* Print.debug "\nold st length %i\n" (List.length (st.handlers_functions_mem) ); *)
                  let st = {st with handlers_functions_mem = (h,old_f,new_f) :: st.handlers_functions_mem} in
                  (* Print.debug "\nnew st length %i\n" (List.length (st.handlers_functions_mem) );  *)
                  let_rec' ~loc (Common.assoc_map (optimize_abs st) defs) (optimize_comp st c1)
            end
      
      