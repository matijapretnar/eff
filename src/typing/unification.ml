module STyVars = Set.Make (struct
                             type t = Params.ty_param
                             let compare = compare
                           end);;
let set_of_list = List.fold_left (fun acc x -> STyVars.add x acc) STyVars.empty;;
open Types
type substitution =
   | CoerTyVarToTyCoercion of (Params.ty_coercion_param * Typed.ty_coercion) 
   | CoerDirtyVartoDirtyCoercion of (Params.dirty_coercion_param * Typed.dirty_coercion)
   | CoerDirtVartoDirtCoercion of (Params.dirt_coercion_param * Typed.dirt_coercion)
   | TyVarToTy of (Params.ty_param * Types.target_ty)
   | DirtVarToDirt of (Params.dirt_param * Types.dirt)



let print_sub ?max_level c ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  begin match c with
  | CoerTyVarToTyCoercion (p, t) ->  print "%t :-coertyTotyCoer-> %t" 
                              (Params.print_ty_coercion_param p) (Typed.print_ty_coercion t)
  | CoerDirtyVartoDirtyCoercion (p,d) ->  print "%t :-coertyDirtyoDirtyCoer-> %t"
                              (Params.print_dirty_coercion_param p) (Typed.print_dirty_coercion d)
  | CoerDirtVartoDirtCoercion (p,d) ->  print "%t :-coertyDirtoDirtCoer-> %t"
                              (Params.print_dirt_coercion_param p) (Typed.print_dirt_coercion d)
  | TyVarToTy (p,t) ->  print "%t :-tyvarToTargetty-> %t" 
                              (Params.print_ty_param p) (Types.print_target_ty t) 
  | DirtVarToDirt (p,d) ->  print "%t :-dirtvarToTargetdirt-> %t" 
                              (Params.print_dirt_param p) (Types.print_target_dirt d) 
  end
let rec apply_sub sub c_list =
	begin match sub with 
	| [] -> c_list
	| (x::xs) -> 
		begin match x with
		| TyVarToTy (type_p,target_type) ->
			let mapper = fun cons ->
				begin match cons with 
				| Typed.TyOmega (coer_p, (Tyvar tv,ty2)) when (type_p == tv) ->  
						Typed.TyOmega (coer_p, (target_type,ty2)) 
			    | Typed.TyOmega (coer_p, (ty2,Tyvar tv)) when (type_p == tv) ->  
						Typed.TyOmega (coer_p, (ty2,target_type)) 
				| Typed.DirtyOmega (coer_p,( ( Tyvar ty1, dirt1) , (ty2, dirt2))) when (ty1 == type_p)->
					Typed.DirtyOmega (coer_p,( ( target_type, dirt1) , (ty2, dirt2)))
				| Typed.DirtyOmega (coer_p,( ( ty1, dirt1) , (Tyvar ty2, dirt2))) when (ty2 == type_p)->
					Typed.DirtyOmega (coer_p,( ( target_type, dirt1) , (target_type, dirt2)))
				| _ -> cons
				end in
			let result_c_list = List.map mapper c_list in 
			apply_sub xs result_c_list
		
    | DirtVarToDirt (type_p,target_dirt) ->
      let mapper = fun cons ->
        begin match cons with
        | Typed.DirtOmega (coer_p,(SetVar (s1,dv) , d2)) when (dv == type_p)->
          let SetVar (diff_set, new_var) = target_dirt in
          let new_set =  effect_set_union s1 diff_set in 
          Typed.DirtOmega(coer_p,(SetVar(new_set,new_var),d2))
        | Typed.DirtOmega (coer_p,(d2, SetVar (s1,dv) )) when (dv == type_p)->
          let SetVar (diff_set, new_var) = target_dirt in
          let new_set =  effect_set_union s1 diff_set in 
          Typed.DirtOmega(coer_p,(d2,SetVar(new_set,new_var)))
        | _ -> cons
        end in 
        let result_c_list = List.map mapper c_list in 
        apply_sub xs result_c_list
    | _ -> apply_sub xs c_list
		end
	end
let rec free_target_ty t = 
 begin match t with 
 | Tyvar x -> [x]
 | Arrow (a,c) -> (free_target_ty a) @ (free_target_dirty c)
 | Tuple tup -> List.flatten (List.map (free_target_ty) tup)
 | Handler (c1,c2) -> (free_target_dirty c1) @ (free_target_dirty c2)
 | PrimTy _ -> []
 | QualTy ( _, a) -> assert false
 | QualDirt ( _, a) -> assert false
 | TySchemeTy (ty_param,a) -> 
 	let free_a = free_target_ty a in 
 	List.filter (fun x -> not (List.mem x [ty_param])) free_a
 | TySchemeDirt (dirt_param,a) -> free_target_ty a 
 end
and
free_target_dirty (a,d) = free_target_ty a 



let rec refresh_target_ty (ty_sbst,dirt_sbst) t=
 begin match t with 
 | Tyvar x -> 
 	begin match OldUtils.lookup x ty_sbst with
      | Some x' -> (ty_sbst,dirt_sbst) , Tyvar x'
      | None -> 
      	let y = (Params.fresh_ty_param ()) in
      	( (OldUtils.update x y ty_sbst ), dirt_sbst) , Tyvar y
    end
 | Arrow (a,c) -> 
 		  let (a_ty_sbst, a_dirt_sbst), a' =  refresh_target_ty (ty_sbst,dirt_sbst) a in
		  let temp_ty_sbst = a_ty_sbst @ ty_sbst in 
		  let temp_dirt_sbst= a_dirt_sbst @ dirt_sbst in 
		  let (c_ty_sbst, c_dirt_sbst), c' = refresh_target_dirty(temp_ty_sbst,temp_dirt_sbst) c in 
		  (c_ty_sbst, c_dirt_sbst), Arrow(a',c')
 | Tuple tup -> (ty_sbst,dirt_sbst), t
 | Handler (c1,c2) -> 
 		   let (c1_ty_sbst, c1_dirt_sbst), c1' =  refresh_target_dirty (ty_sbst,dirt_sbst) c1 in
		   let temp_ty_sbst = c1_ty_sbst @ ty_sbst in 
		   let temp_dirt_sbst= c1_dirt_sbst @ dirt_sbst in 
		   let (c2_ty_sbst, c2_dirt_sbst), c2' = refresh_target_dirty(temp_ty_sbst,temp_dirt_sbst) c2 in 
		  (c2_ty_sbst, c2_dirt_sbst), Handler(c1',c2')
 | PrimTy x ->  (ty_sbst,dirt_sbst), PrimTy x
 | QualTy ( _, a) -> assert false
 | QualDirt ( _, a) -> assert false
 | TySchemeTy (ty_param,a) -> assert false
 | TySchemeDirt (dirt_param,a) -> assert false
end 
 
and refresh_target_dirty (ty_sbst, dirt_sbst) (t,d)=  
 		let (t_ty_sbst, t_dirt_sbst), t' =  refresh_target_ty (ty_sbst,dirt_sbst) t in
 		let temp_ty_sbst = t_ty_sbst @ ty_sbst  in 
 		let temp_dirt_sbst= t_dirt_sbst @ dirt_sbst in 
 		let (d_ty_sbst, d_dirt_sbst), d' = refresh_target_dirt(temp_ty_sbst,temp_dirt_sbst) d in 
 		(d_ty_sbst,d_dirt_sbst) ,(t',d')

and refresh_target_dirt (ty_sbst, dirt_sbst) t = 
 begin match t with 
 | SetVar(set,x) -> 
    begin match OldUtils.lookup x dirt_sbst with
    | Some x' -> (ty_sbst,dirt_sbst), Types.SetVar(set,x')
    | None -> 
      let y = (Params.fresh_dirt_param ()) in
      ( ty_sbst, (OldUtils.update x y dirt_sbst )) , SetVar(set,y)
   end
 | SetEmpty set -> ((ty_sbst, dirt_sbst) , (Types.SetEmpty set))
end


let rec print_c_list = function 
[] -> Print.debug "---------------------"
| e::l -> Print.debug "%t" (Typed.print_omega_ct e)  ; print_c_list l

let rec print_s_list = function 
[] -> Print.debug "---------------------"
| e::l -> Print.debug "%t" (print_sub e)  ; print_s_list l

let rec print_var_list = function
[] -> Print.debug "---------------------"
| e::l -> Print.debug "%t" (Params.print_ty_param e)  ; print_var_list l


let rec union_find_tyvar tyvar acc c_list = 
(*   Print.debug "In uf";	
  Print.debug "The Type Variable : %t" (Params.print_ty_param tyvar);
  Print.debug "The accumilator : -------------";
  print_var_list acc;
  print_c_list c_list;
  Print.debug "-------------end UF----------------"; *)
  begin match c_list with 
  | [] -> (tyvar::acc)
  | (x::xs) -> 
  	begin match x with 
  	| Typed.TyOmega (_,tycons) -> 
  		begin match tycons with
  		| (Types.Tyvar a, Types.Tyvar b) when (a = tyvar)->
  			if (List.mem b acc)
  			then union_find_tyvar tyvar acc xs 
  			else OldUtils.uniq (((union_find_tyvar b acc xs) @ (union_find_tyvar tyvar acc xs)))
  		| (Types.Tyvar b, Types.Tyvar a) when (a = tyvar)->
  			if (List.mem b acc)
  			then union_find_tyvar tyvar acc xs 
  			else OldUtils.uniq (((union_find_tyvar b acc xs) @ (union_find_tyvar tyvar acc xs)))
  		| _ -> union_find_tyvar tyvar acc xs
  		end 
   	| Typed.DirtyOmega(_,((a,_),(b,_))) -> 
  			union_find_tyvar tyvar acc ( (Typed.TyOmega((Params.fresh_ty_coercion_param ()), (a,b) )) :: xs)
  	| _ -> union_find_tyvar tyvar acc xs
  	end
  end


let rec fix_union_find fixpoint c_list =
  Print.debug "--------------start list-------";
  print_var_list fixpoint;
  Print.debug "---------------end list-------";
  let mapper = fun x ->
               begin match x with
               | Typed.TyOmega (_,tycons) -> 
                      begin match tycons with
                      | (Types.Tyvar a, Types.Tyvar b) when ( (List.mem a fixpoint) && (not (List.mem b fixpoint)))->
                            [b]
                      | (Types.Tyvar b, Types.Tyvar a) when ( (List.mem a fixpoint) && (not (List.mem b fixpoint)))->
                            [b]
                      | _ -> []    
                    end
               | Typed.DirtyOmega(_,((Types.Tyvar a,_),(Types.Tyvar b,_))) when ( (List.mem a fixpoint) && (not (List.mem b fixpoint))) ->
                  [b]
               | Typed.DirtyOmega(_,((Types.Tyvar b,_),(Types.Tyvar a,_))) when ( (List.mem a fixpoint) && (not (List.mem b fixpoint))) ->
                  [b]
               | _-> []
               end in
  let new_fixpoint = fixpoint @ OldUtils.flatten_map mapper c_list in 
  let sort_new_fixpoint = List.sort compare new_fixpoint in
  if (sort_new_fixpoint = fixpoint ) then sort_new_fixpoint else
  fix_union_find sort_new_fixpoint c_list



let rec dependent_constraints dep_list acc c_list = 
(*   Print.debug "In dc"; *)
  begin match c_list with 
  | [] -> acc
  | (x::xs) -> 
  	begin match x with 
  	| Typed.TyOmega (_,tycons) -> 
  		begin match tycons with
  		| (Types.Tyvar a, Types.Tyvar b) when (List.mem a dep_list && List.mem b dep_list)->
  			dependent_constraints dep_list (x :: acc) xs 
  		| _ -> dependent_constraints dep_list acc xs
  		end 
  	| _ -> dependent_constraints dep_list acc xs
  	end
  end


let rec unify(sub, paused, queue) =
 Print.debug "=============Start loop============";
 Print.debug "-----Subs-----";
 print_s_list sub;
 Print.debug "-----paused-----";
 print_c_list paused;
 Print.debug "-----queue-----";
 print_c_list queue;
 if (queue == []) then (sub,paused)
 else
 let cons::rest_queue = queue in 
 begin match cons with
 | Typed.TyOmega (omega,tycons) ->
 	begin match tycons with
 	| (x,y) when x=y -> 
 		let sub1 = CoerTyVarToTyCoercion (omega, Typed.ReflTy(x)) in
    Print.debug "=========End loop============";
 		unify (sub1::sub, paused, rest_queue)
 	| (Types.Tyvar a, Types.Tyvar b) ->
    Print.debug "=========End loop============";
 		unify (sub, (cons::paused), rest_queue)
 	| (Types.Arrow(a1,c1) , Types.Arrow(a2,c2)) ->
 	    let new_ty_coercion_var = Params.fresh_ty_coercion_param () in 
   		let new_dirty_coercion_var = Params.fresh_dirty_coercion_param () in
   		let new_ty_coercion_var_coer = Typed.TyCoercionVar new_ty_coercion_var in 
   		let new_dirty_coercion_var_coer = Typed.DirtyCoercionVar new_dirty_coercion_var in
   		let sub1 = CoerTyVarToTyCoercion (omega, Typed.ArrowCoercion (new_ty_coercion_var_coer,new_dirty_coercion_var_coer)) in 
   		let ty_cons = Typed.TyOmega(new_ty_coercion_var,(a2,a1)) in 
   		let dirty_cons = Typed.DirtyOmega(new_dirty_coercion_var,(c1,c2)) in
   		Print.debug "=========End loop============";
      unify ((sub1::sub), paused, (List.append [ty_cons;dirty_cons] rest_queue))
  | (Types.Handler(c1,d1) , Types.Handler(c2,d2)) ->
 	    let new_dirty_coercion_var = Params.fresh_dirty_coercion_param () in 
   		let new_dirty_coercion_var_2 = Params.fresh_dirty_coercion_param () in
   		let new_dirty_coercion_var_coer = Typed.DirtyCoercionVar new_dirty_coercion_var in 
   		let new_dirty_coercion_var_coer_2 = Typed.DirtyCoercionVar new_dirty_coercion_var_2 in
   		let sub1 = CoerTyVarToTyCoercion (omega, Typed.HandlerCoercion (new_dirty_coercion_var_coer,new_dirty_coercion_var_coer_2)) in 
   		let dirty_cons = Typed.DirtyOmega(new_dirty_coercion_var,(c2,c1)) in 
   		let dirty_cons_2 = Typed.DirtyOmega(new_dirty_coercion_var,(d1,d2)) in
   		Print.debug "=========End loop============";
      unify ((sub1::sub), paused, (List.append [dirty_cons;dirty_cons_2] rest_queue)) 
 	| (Types.Tyvar tv, a) ->
    unify_ty_vars (sub,paused,rest_queue) tv a cons
 	| ( a , Types.Tyvar tv) ->
 		unify_ty_vars (sub,paused,rest_queue) tv a cons
 	| _ -> assert false
 	end
 
 | Typed.DirtyOmega(omega,((t1,d1),(t2,d2))) ->
   let new_ty_coercion_var = Params.fresh_ty_coercion_param () in 
   let new_dirt_coercion_var = Params.fresh_dirt_coercion_param () in
   let new_ty_coercion_var_coer = Typed.TyCoercionVar new_ty_coercion_var in 
   let new_dirt_coercion_var_coer = Typed.DirtCoercionVar new_dirt_coercion_var in 
   let sub1 = CoerDirtyVartoDirtyCoercion(omega, Typed.BangCoercion(new_ty_coercion_var_coer,new_dirt_coercion_var_coer)) in 
   let ty_cons = Typed.TyOmega(new_ty_coercion_var,(t1,t2)) in 
   let dirt_cons = Typed.DirtOmega(new_dirt_coercion_var,(d1,d2)) in 
   Print.debug "=========End loop============";
   unify ((sub1::sub), paused, (List.append [ty_cons;dirt_cons] rest_queue))
 
 | Typed.DirtOmega(omega, dcons) ->
   begin match dcons with 
    | (Types.SetVar(s1,v1) ,Types.SetVar(s2,v2) ) ->
      if (Types.effect_set_is_empty s1) then 
      begin 
        Print.debug "=========End loop============";
        unify (sub ,(cons::paused), rest_queue)
        end 
      else begin 
        let diff_set = Types.effect_set_diff s1 s2 in
        let sub' = DirtVarToDirt(v2, Types.SetVar (diff_set, (Params.fresh_dirt_param ()))) in 
        let paused' = apply_sub [sub'] paused in 
        let new_cons = apply_sub [sub'] [(Typed.DirtOmega(omega, (Types.SetVar( (Types.empty_effect_set),v1 ) , Types.SetVar(s2,v2))))] in 
        Print.debug "=========End loop============";
        unify ((sub' :: sub), [] , ((new_cons @ paused') @ rest_queue ))
      end
   | _ -> Print.debug "=========End loop============";
        unify (sub ,(cons::paused), rest_queue)
   end 
 end 

and unify_ty_vars (sub,paused,rest_queue) tv a cons= 
	let free_a = free_target_ty a in 
(* 	let dependent_tyvars = (union_find_tyvar tv [] paused) in *)
  let dependent_tyvars = (fix_union_find [tv] paused) in 
	let s1 = set_of_list free_a in 
	let s2 = set_of_list dependent_tyvars in 
	if (not (STyVars.is_empty (STyVars.inter s1 s2))) then assert false 
	else
	let mapper_f = fun x -> let (_,_), a' = refresh_target_ty ([],[]) a in 
							TyVarToTy(x, a') in
	let sub' = List.map mapper_f dependent_tyvars in
	let paused' = dependent_constraints dependent_tyvars [] paused in
(*   Print.debug "Paused' = ";
  print_c_list paused'; 
  Print.debug "end Paused --"; *)
	let new_paused = OldUtils.diff paused paused' in 
	let sub_queue = apply_sub sub' rest_queue in 
	let sub_paused' = apply_sub sub' paused' in 
	let [cons'] = apply_sub sub' [cons] in 
	let new_queue = (sub_queue @ sub_paused') @ [cons'] in 
  Print.debug "=========End loops============";
	unify ( (sub @ sub') , new_paused, new_queue)