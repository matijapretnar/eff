module STyVars = Set.Make (struct
                             type t = Params.ty_param
                             let compare = compare
                           end);;
let set_of_list = List.fold_left (fun acc x -> STyVars.add x acc) STyVars.empty;;
open Types
type substitution =
   | CoerTyVarToTyCoercion of (Params.ty_coercion_param * Typed.ty_coercion) 
   | CoerDirtyVartoDirtyCoercion of (Params.dirty_coercion_param * Typed.dirty_coercion)
   | TyVarToTy of (Params.ty_param * Types.target_ty)

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
 	begin match Common.lookup x ty_sbst with
      | Some x' -> (ty_sbst,dirt_sbst) , Tyvar x'
      | None -> 
      	let y = (Params.fresh_ty_param ()) in
      	( (Common.update x y ty_sbst ), dirt_sbst) , Tyvar y
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
 | Empty -> ((ty_sbst, dirt_sbst) , Types.Empty)
 | DirtVar x ->  
	begin match Common.lookup x dirt_sbst with
    | Some x' -> (ty_sbst,dirt_sbst), DirtVar x'
    | None -> 
    	let y = (Params.fresh_dirt_param ()) in
    	( ty_sbst, (Common.update x y dirt_sbst )) , DirtVar y
   end
| Union (eff,d) -> let (ty_sbst', dirt_sbst'), d' = refresh_target_dirt (ty_sbst, dirt_sbst) d in 
				   (ty_sbst', dirt_sbst') , Union(eff,d') 
end


let rec union_find_tyvar tyvar acc c_list = 
  begin match c_list with 
  | [] -> acc
  | (x::xs) -> 
  	begin match x with 
  	| Typed.TyOmega (_,tycons) -> 
  		begin match tycons with
  		| (Types.Tyvar a, Types.Tyvar b) when (a == tyvar)->
  			if (List.mem b acc)
  			then union_find_tyvar tyvar acc xs 
  			else Common.uniq (((union_find_tyvar b acc c_list) @ (union_find_tyvar tyvar acc xs)))
  		| (Types.Tyvar b, Types.Tyvar a) when (a == tyvar)->
  			if (List.mem b acc)
  			then union_find_tyvar tyvar acc xs 
  			else Common.uniq (((union_find_tyvar b acc c_list) @ (union_find_tyvar tyvar acc xs)))
  		end 
  	| Typed.DirtyOmega(_,((a,_),(b,_))) -> 
  			union_find_tyvar tyvar acc ( (Typed.TyOmega((Params.fresh_ty_coercion_param ()), (a,b) )) :: c_list)
  	| _ -> union_find_tyvar tyvar acc xs
  	end
  end

let rec unify(sub, paused, queue) =
 if (queue == []) then (sub,paused)
 else
 let cons::rest_queue = queue in 
 begin match cons with
 | Typed.TyOmega (omega,tycons) ->
 	begin match tycons with
 	| (x,y) when x=y -> 
 		let sub1 = CoerTyVarToTyCoercion (omega, Typed.ReflTy(x)) in
 		let new_sub = List.append sub [sub1] in 
 		unify (new_sub, paused, rest_queue)
 	| (Types.Tyvar a, Types.Tyvar b) ->
 		unify (sub, (cons::paused), rest_queue)
 	| (Types.Arrow(a1,c1) , Types.Arrow(a2,c2)) ->
 	    let new_ty_coercion_var = Params.fresh_ty_coercion_param () in 
   		let new_dirty_coercion_var = Params.fresh_dirty_coercion_param () in
   		let new_ty_coercion_var_coer = Typed.TyCoercionVar new_ty_coercion_var in 
   		let new_dirty_coercion_var_coer = Typed.DirtyCoercionVar new_dirty_coercion_var in
   		let sub1 = CoerTyVarToTyCoercion (omega, Typed.ArrowCoercion (new_ty_coercion_var_coer,new_dirty_coercion_var_coer)) in 
   		let ty_cons = Typed.TyOmega(new_ty_coercion_var,(a2,a1)) in 
   		let dirty_cons = Typed.DirtyOmega(new_dirty_coercion_var,(c1,c2)) in
   		unify ((sub1::sub), paused, (List.append [ty_cons;dirty_cons] rest_queue))
   	| (Types.Handler(c1,d1) , Types.Handler(c2,d2)) ->
 	    let new_dirty_coercion_var = Params.fresh_dirty_coercion_param () in 
   		let new_dirty_coercion_var_2 = Params.fresh_dirty_coercion_param () in
   		let new_dirty_coercion_var_coer = Typed.DirtyCoercionVar new_dirty_coercion_var in 
   		let new_dirty_coercion_var_coer_2 = Typed.DirtyCoercionVar new_dirty_coercion_var_2 in
   		let sub1 = CoerTyVarToTyCoercion (omega, Typed.HandlerCoercion (new_dirty_coercion_var_coer,new_dirty_coercion_var_coer_2)) in 
   		let dirty_cons = Typed.DirtyOmega(new_dirty_coercion_var,(c2,c1)) in 
   		let dirty_cons_2 = Typed.DirtyOmega(new_dirty_coercion_var,(d1,d2)) in
   		unify ((sub1::sub), paused, (List.append [dirty_cons;dirty_cons_2] rest_queue)) 
 	| (Types.Tyvar tv, a) ->
 		let free_a = free_target_ty a in 
 		let dependent_tyvars = Common.diff (union_find_tyvar tv [] paused) [tv] in
 		let s1 = set_of_list free_a in 
 		let s2 = set_of_list dependent_tyvars in 
 		if (not (STyVars.is_empty (STyVars.inter s1 s2))) then assert false 
 		else
 		let mapper_f = fun x -> let (_,_), a' = refresh_target_ty ([],[]) a in 
 								TyVarToTy(x, a') in
 		let sub' = List.map mapper_f dependent_tyvars in
 		assert false 		
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
   unify ((sub1::sub), paused, (List.append [ty_cons;dirt_cons] rest_queue))
 | _ -> assert false 
 end 

