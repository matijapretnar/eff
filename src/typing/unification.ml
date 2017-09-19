open Types

type substitution =
   | CoerTyVarToTyCoercion of (Params.ty_coercion_param * Typed.ty_coercion) 
   | CoerDirtyVartoDirtyCoercion of (Params.dirty_coercion_param * Typed.dirty_coercion)
   | TyVarToTy of (Params.ty_param * Types.target_ty)

(* let rec free_target_ty t = 
 begin match t with 
 | Tyvar x -> ([x],[])
 | Arrow (a,c) -> (free_target_ty a) @ (free_target_dirty c)
 | Tuple tup -> List.flatten (List.map (free_target_ty) tup)
 | Handler (c1,c2) -> (free_target_dirty c1) @ (free_target_dirty c2)
 | PrimTy _ -> ([],[])
 | QualTy ( _, a) -> (free_target_ty a)
 | QualDirt ( _, a) -> (free_target_ty a)
 | TySchemeTy (ty_param,a) -> assert false
 | TySchemeDirt (dirt_param,a) -> assert false
 end
and
free_target_dirty (a,delta) = 
	let(freetys_a,freedirts_a) = free_target_ty a in 
	let(freetys_delta,freedirts_delta) = free_target_dirt delta in 
	((freetys_a @ freetys_delta), (freedirts_a @ freedirts_delta))
and
free_target_dirt d = ([],[])

 *)
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

