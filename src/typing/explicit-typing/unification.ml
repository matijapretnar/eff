module STyVars = Set.Make (struct
                             type t = Params.ty_param
                             let compare = compare
                           end);;
let set_of_list = List.fold_left (fun acc x -> STyVars.add x acc) STyVars.empty;;
open Types
open Typed
type substitution =
   | CoerTyVarToTyCoercion of (Params.ty_coercion_param * Typed.ty_coercion) 
   | CoerDirtVartoDirtCoercion of (Params.dirt_coercion_param * Typed.dirt_coercion)
   | TyVarToTy of (Params.ty_param * Types.target_ty)
   | DirtVarToDirt of (Params.dirt_param * Types.dirt)
   | SkelVarToSkel of (Params.skel_param * Types.skeleton)



let print_sub ?max_level c ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  begin match c with
  | CoerTyVarToTyCoercion (p, t) ->  print "%t :-coertyTotyCoer-> %t" 
                              (Params.print_ty_coercion_param p) (Typed.print_ty_coercion t)
  | CoerDirtVartoDirtCoercion (p,d) ->  print "%t :-coertyDirtoDirtCoer-> %t"
                              (Params.print_dirt_coercion_param p) (Typed.print_dirt_coercion d)
  | TyVarToTy (p,t) ->  print "%t :-tyvarToTargetty-> %t" 
                              (Params.print_ty_param p) (Types.print_target_ty t) 
  | DirtVarToDirt (p,d) ->  print "%t :-dirtvarToTargetdirt-> %t" 
                              (Params.print_dirt_param p) (Types.print_target_dirt d) 
  | SkelVarToSkel (p,s) ->  print "%t :-skelvarToSkeleton-> %t" 
                              (Params.print_skel_param p) (Types.print_skeleton s) 
  end




let rec apply_substitution s ci =
  begin match s with
  | [] -> ci
  | (s1::ss) -> 
      let subbed_term = apply_sub_comp s1 ci in 
      apply_substitution ss subbed_term
  end

and apply_substitution_exp s ei =
  begin match s with
  | [] -> ei
  | (s1::ss) -> 
      let subbed_term = apply_sub_exp s1 ei in 
      apply_substitution_exp ss subbed_term
  end

and apply_substitution_ty s ty1 =
  begin match s with
  | [] -> ty1
  | (s1::ss) -> 
      let subbed_term = apply_sub_ty s1 ty1 in 
      apply_substitution_ty ss subbed_term
  end

and apply_substitution_dirt s drt =
  begin match s with
  | [] -> drt
  | (s1::ss) -> 
      let subbed_term = apply_sub_dirt s1 drt in 
      apply_substitution_dirt ss subbed_term
  end

and apply_substitution_skel s ty1 =
  begin match s with
  | [] -> ty1
  | (s1::ss) -> 
      let subbed_term = apply_sub_skel s1 ty1 in 
      apply_substitution_skel ss subbed_term
  end

and apply_sub_comp sub c =
let c' = apply_sub_plain_comp sub c in
  Typed.annotate c' c.location
and apply_sub_plain_comp sub c =
  begin match c.term with 
  | Value e -> Value (apply_sub_exp sub e) 
  | LetVal (v1,e1,c1) -> LetVal (v1, (apply_sub_exp sub e1), (apply_sub_comp sub c1))
  | LetRec (l,c1) -> LetRec (l,c1)
  | Match (e,alist) -> Match (e,alist)
  | Apply (e1,e2) -> Apply ((apply_sub_exp sub e1), (apply_sub_exp sub e2))
  | Handle (e1,c1) -> Handle ((apply_sub_exp sub e1), (apply_sub_comp sub c1))
  | Call (effect,e1,abs) -> Call (effect, (apply_sub_exp sub e1), (apply_sub_abs_with_ty sub abs))
  | Op(ef,e1) -> Op (ef, (apply_sub_exp sub e1 ))
  | Bind (c1,a1) -> Bind ((apply_sub_comp sub c1), (apply_sub_abs sub a1))
  | CastComp (c1,dc1) -> CastComp ((apply_sub_comp sub c1), (apply_sub_dirtycoer sub dc1))
  | CastComp_ty (c1,tc1)-> CastComp_ty ( (apply_sub_comp sub c1) , (apply_sub_tycoer sub tc1) )
  | CastComp_dirt (c1,tc1)-> CastComp_dirt ( (apply_sub_comp sub c1) , (apply_sub_dirtcoer sub tc1) ) 
  end

and apply_sub_exp sub exp =
let e' = apply_sub_plain_exp sub exp in
  Typed.annotate e' (exp.location)
and apply_sub_plain_exp sub e =
  begin match e.term with 
  | Var v -> Var v
  | BuiltIn(s,i) -> BuiltIn (s,i)
  | Const c -> Const c 
  | Tuple elist -> Tuple (List.map (fun x -> apply_sub_exp sub x) elist)
  | Record r -> Record r 
  | Variant (lbl, e1) -> Variant (lbl, e1)
  | Lambda (pat,ty1,c1)-> Lambda (pat, (apply_sub_ty sub ty1), (apply_sub_comp sub c1))
  | Effect eff -> Effect eff
  | Handler h -> Handler (apply_sub_handler sub h)
  | BigLambdaTy(ty_param,sk,e1) -> BigLambdaTy( ty_param, (apply_sub_skel sub sk) , (apply_sub_exp sub e1))
  | BigLambdaDirt(dirt_param,e1) -> BigLambdaDirt (dirt_param, (apply_sub_exp sub e1))
  | BigLambdaSkel(skel_param,e1) -> BigLambdaSkel (skel_param, (apply_sub_exp sub e1))
  | CastExp (e1,tc1) -> CastExp ( (apply_sub_exp sub e1) , (apply_sub_tycoer sub tc1) )
  | ApplyTyExp (e1,tty) -> ApplyTyExp ( (apply_sub_exp sub e1), (apply_sub_ty sub tty))
  | LambdaTyCoerVar (tcp1,ct_ty1,e1) ->LambdaTyCoerVar (tcp1, ct_ty1, (apply_sub_exp sub e1))
  | LambdaDirtCoerVar (dcp1,ct_dirt1,e1) ->LambdaDirtCoerVar (dcp1, ct_dirt1, (apply_sub_exp sub e1))
  | ApplyDirtExp (e1,d1) -> ApplyDirtExp ((apply_sub_exp sub e1), (apply_sub_dirt sub d1))
  | ApplyTyCoercion (e1,tc1) -> ApplyTyCoercion ((apply_sub_exp sub e1), (apply_sub_tycoer sub tc1))
  | ApplyDirtCoercion (e1,dc1) -> ApplyDirtCoercion ((apply_sub_exp sub e1), (apply_sub_dirtcoer sub dc1))
  | ApplySkelExp (e1, s1) -> ApplySkelExp ((apply_sub_exp sub e1), (apply_sub_skel sub s1))
end

and apply_sub_abs sub abs = 
  let (p,c) = abs.term in 
  annotate (p, apply_sub_comp sub c) abs.location

and apply_sub_abs_with_ty sub abs = 
  let (p,t,c) = abs.term in 
  annotate (p, (apply_sub_ty sub t), apply_sub_comp sub c) abs.location

and apply_sub_abs2 sub abs2 = 
  let (p1,p2,c) = abs2.term in 
  annotate (p1, p2, apply_sub_comp sub c) abs2.location

and apply_sub_handler sub h =
  let eff_clauses = h.effect_clauses in 
  let new_value_clause = apply_sub_abs_with_ty sub h.value_clause in 
  let new_eff_clauses = OldUtils.assoc_map (fun abs2 ->apply_sub_abs2 sub abs2) eff_clauses in 
  { effect_clauses= new_eff_clauses;
    value_clause = new_value_clause;}

and apply_sub_tycoer sub ty_coer =
  begin match ty_coer with 
  | ReflTy tty -> ReflTy (apply_sub_ty sub tty)
  | ArrowCoercion(tycoer1,dirtycoer) -> ArrowCoercion (apply_sub_tycoer sub tycoer1, apply_sub_dirtycoer sub dirtycoer)
  | HandlerCoercion (dirtycoer1,dirtycoer2) -> 
        HandlerCoercion (apply_sub_dirtycoer sub dirtycoer1, apply_sub_dirtycoer sub dirtycoer2)
  | TyCoercionVar p ->
      begin match sub with 
      | CoerTyVarToTyCoercion (p',t_coer) when (p = p') -> t_coer
      | _ -> TyCoercionVar p
    end
  | SequenceTyCoer (ty_coer1,ty_coer2) -> SequenceTyCoer (apply_sub_tycoer sub ty_coer1, apply_sub_tycoer sub ty_coer2)
  | TupleCoercion tcl -> TupleCoercion (List.map (fun x-> apply_sub_tycoer sub x) tcl)
  | LeftArrow tc1 -> LeftArrow (apply_sub_tycoer sub tc1)
  | ForallTy (ty_param,ty_coer1) -> ForallTy (ty_param, apply_sub_tycoer sub ty_coer1)
  | ApplyTyCoer (ty_coer1,tty1) -> ApplyTyCoer (apply_sub_tycoer sub ty_coer1, apply_sub_ty sub tty1)
  | ForallDirt (dirt_param,ty_coer1) -> ForallDirt (dirt_param, apply_sub_tycoer sub ty_coer1)
  | ApplyDirCoer (ty_coer1,drt) -> ApplyDirCoer (apply_sub_tycoer sub ty_coer1, apply_sub_dirt sub drt)
  | PureCoercion dirty_coer1 -> PureCoercion (apply_sub_dirtycoer sub dirty_coer1)
  | ForallSkel (ty_param,ty_coer1) -> ForallSkel (ty_param, apply_sub_tycoer sub ty_coer1)
  | ApplySkelCoer (ty_coer1,sk1) -> ApplySkelCoer (apply_sub_tycoer sub ty_coer1, apply_sub_skel sub sk1)
  end

and apply_sub_dirtcoer sub dirt_coer = 
  begin match dirt_coer with 
  | ReflDirt d -> ReflDirt (apply_sub_dirt sub d)
  | DirtCoercionVar p ->
      begin match sub with 
      | CoerDirtVartoDirtCoercion (p' , dc) when (p' = p) -> dc
      | _ -> dirt_coer
    end
  | Empty d -> Empty (apply_sub_dirt sub d )
  | UnionDirt (es,dirt_coer1) -> UnionDirt (es, (apply_sub_dirtcoer sub dirt_coer1))
  | SequenceDirtCoer(dirt_coer1, dirt_coer2) -> 
        SequenceDirtCoer (apply_sub_dirtcoer sub dirt_coer1, apply_sub_dirtcoer sub dirt_coer2)
  | DirtCoercion (dirty_coer1) -> 
        DirtCoercion (apply_sub_dirtycoer sub dirty_coer1)
  end

and apply_sub_dirtycoer sub dirty_coer =
  begin match dirty_coer with 
  | BangCoercion (ty_coer,dirt_coer) -> BangCoercion (apply_sub_tycoer sub ty_coer, apply_sub_dirtcoer sub dirt_coer)
  | RightArrow ty_coer1 -> RightArrow (apply_sub_tycoer sub ty_coer1)
  | RightHandler ty_coer1 -> RightHandler (apply_sub_tycoer sub ty_coer1)
  | LeftHandler ty_coer1 -> LeftHandler (apply_sub_tycoer sub ty_coer1)
  | SequenceDirtyCoer(dirty_coer1,dirty_coer2) -> 
        SequenceDirtyCoer (apply_sub_dirtycoer sub dirty_coer1, apply_sub_dirtycoer sub dirty_coer2) 
  end

and apply_sub_ty sub ty = 
  begin match ty with 
  | Tyvar typ1 ->
        begin match sub with 
        | TyVarToTy (typ2,ttype) when (typ1 = typ2) -> ttype
        | _ -> ty
        end
  | Arrow (tty1,tty2) -> Arrow ((apply_sub_ty sub tty1),(apply_sub_dirty_ty sub tty2))
  | Tuple ttyl ->Tuple (List.map (fun x -> apply_sub_ty sub x) ttyl)
  | Handler (tydrty1,tydrty2) -> Handler ((apply_sub_dirty_ty sub tydrty1), (apply_sub_dirty_ty sub tydrty2) )
  | PrimTy _ -> ty
  | QualTy (ct_ty1,tty1) -> QualTy (apply_sub_ct_ty sub ct_ty1, apply_sub_ty sub tty1)
  | QualDirt (ct_drt1,tty1) -> QualDirt (apply_sub_ct_dirt sub ct_drt1,apply_sub_ty sub tty1 )
  | TySchemeTy (ty_param ,sk,tty1) -> TySchemeTy (ty_param, apply_sub_skel sub sk, apply_sub_ty sub tty1)
  | TySchemeDirt (dirt_param ,tty1) -> TySchemeDirt (dirt_param, apply_sub_ty sub tty1)
  end
and apply_sub_dirty_ty sub drty_ty = 
  let (ty1,drt1) = drty_ty in 
  ( (apply_sub_ty sub ty1), (apply_sub_dirt sub drt1))

and apply_sub_dirt sub1 drt =
  begin match drt with 
  | SetVar (eset,p) ->
      begin match sub1 with 
      | DirtVarToDirt (p', drt2) when (p = p')-> 
          begin match drt2 with 
          | SetVar (eset2,pp) ->
              let eset_union = EffectSet.union eset eset2 in 
              SetVar (eset_union,pp)
          | SetEmpty eset2 ->
              SetEmpty (EffectSet.union eset eset2)
          end
      | _ -> drt
      end
  | SetEmpty _ -> drt
  end

and apply_sub_skel sub sk =
  begin match sk with 
  | SkelVar p -> 
      begin match sub with 
      | SkelVarToSkel (skv,sk1) when (skv = p) -> sk1
      | _ -> sk
      end
  | PrimSkel _ -> sk
  | SkelArrow (sk1,sk2) -> SkelArrow ( (apply_sub_skel sub sk1) , (apply_sub_skel sub sk2)) 
  | SkelHandler (sk1,sk2) -> SkelHandler ( (apply_sub_skel sub sk1) , (apply_sub_skel sub sk2)) 
  | ForallSkel (p,sk1)->  ForallSkel (p, apply_sub_skel sub sk1)
  end
and apply_sub_ct_ty sub ct_ty1 = 
  let (ct_tya,ct_tyb) = ct_ty1 in 
  ( (apply_sub_ty sub ct_tya), (apply_sub_ty sub ct_tyb) )

and apply_sub_ct_dirt sub ct_drt =
  let (ct_tya,ct_tyb) = ct_drt in 
  ( (apply_sub_dirt sub ct_tya), (apply_sub_dirt sub ct_tyb) )


(* apply a single sub to a list of constraints *)
let apply_sub1 c_list sub1 =
  begin 
    match sub1 with
    | TyVarToTy (type_p,target_type) ->
       let mapper = fun cons ->
       	              begin 
                        match cons with 
                        | Typed.TyOmega (coer_p, (ty1,ty2)) ->
                           Typed.TyOmega (coer_p, (apply_sub_ty sub1 ty1, apply_sub_ty sub1 ty2))
(*
       	                | Typed.TyOmega (coer_p, (Tyvar tv,ty2)) when (type_p = tv) ->  
       			   Typed.TyOmega (coer_p, (target_type,ty2)) 
                        | Typed.TyOmega (coer_p, (ty2,Tyvar tv)) when (type_p = tv) ->  
       			   Typed.TyOmega (coer_p, (ty2,target_type)) 
 *)
       	                | _ -> cons
       	              end in
       List.map mapper c_list
    | DirtVarToDirt (type_p,target_dirt) ->
       let mapper = function Typed.DirtOmega (coerp,(drt1,drt2)) ->
                              Typed.DirtOmega (coerp,(apply_sub_dirt sub1 drt1,apply_sub_dirt sub1 drt2))
                           | Typed.TyOmega (coerp,(ty1,ty2)) ->
                              Typed.TyOmega (coerp,(apply_sub_ty sub1 ty1,apply_sub_ty sub1 ty2))
                           | cons -> cons
(*
                 function 
                          Typed.DirtOmega (coer_p,(SetVar (s1,dv) , d2)) when (dv = type_p) ->
                             begin match target_dirt with
                             | SetVar (diff_set, new_var) ->
                                let new_set =  EffectSet.union s1 diff_set in 
                                Typed.DirtOmega(coer_p,(SetVar(new_set,new_var),d2))
                             | SetEmpty diff_set ->
                                let new_set =  EffectSet.union s1 diff_set in 
                                Typed.DirtOmega(coer_p,(SetEmpty new_set,d2))
                             end
                        | Typed.DirtOmega (coer_p,(d2, SetVar (s1,dv) )) when (dv = type_p) ->
                             begin match target_dirt with
                             | SetVar (diff_set, new_var) ->
                                let new_set =  EffectSet.union s1 diff_set in 
                                Typed.DirtOmega(coer_p,(d2,SetVar(new_set,new_var)))
                             | SetEmpty diff_set ->
                                let new_set =  EffectSet.union s1 diff_set in 
                                Typed.DirtOmega(coer_p,(d2,SetEmpty(new_set)))
                             end
                        | cons -> cons
 *)
                      in 
       List.map mapper c_list
    | SkelVarToSkel (skel_var,skel) ->
       let mapper = fun cons ->
                      begin match cons with 
                      | Typed.TyvarHasSkel (tv, Types.SkelVar sv) when (skel_var = sv) ->
                         Typed.TyvarHasSkel (tv, skel)
                      | _ -> cons
                    end in
       List.map mapper c_list
    | _ -> c_list
  end

(* apply substitution-list to a list of constraints *)
let rec apply_sub sub c_list =
  List.fold_left apply_sub1 c_list sub

let rec free_skeleton sk = 
  begin match sk with 
  | SkelVar p -> [p]
  | PrimSkel _ -> []
  | SkelArrow (sk1,sk2) -> (free_skeleton sk1) @ (free_skeleton sk2) 
  | SkelHandler (sk1,sk2) -> (free_skeleton sk1) @ (free_skeleton sk2) 
  | ForallSkel (p,sk1)-> 
      let free_a = free_skeleton sk1 in 
      List.filter (fun x -> not (List.mem x [p])) free_a
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
 | TySchemeTy (ty_param,_,a) -> 
 	let free_a = free_target_ty a in 
 	List.filter (fun x -> not (List.mem x [ty_param])) free_a
 | TySchemeDirt (dirt_param,a) -> free_target_ty a 
 end
and
free_target_dirty (a,d) = free_target_ty a 

let rec print_c_list = function 
[] -> Print.debug "---------------------"
| e::l -> Print.debug "%t" (Typed.print_omega_ct e)  ; print_c_list l

let rec print_s_list = function 
[] -> Print.debug "---------------------"
| e::l -> Print.debug "%t" (print_sub e)  ; print_s_list l

let rec print_var_list = function
[] -> Print.debug "---------------------"
| e::l -> Print.debug "%t" (Params.print_ty_param e)  ; print_var_list l

let rec get_skel_of_tyvar tyvar clist = 
  Print.debug "getting skeleton of tyvar from list";
  Print.debug " Tyvar : %t" (Params.print_ty_param tyvar);
  Print.debug "Constraint list :";
  print_c_list clist;
  get_skel_of_tyvar_ tyvar clist
and get_skel_of_tyvar_ tyvar clist =
  begin match clist with
  | [] -> assert false 
  | (TyvarHasSkel (tv,skel))::_ when (tyvar = tv) -> skel
  | _::xs -> get_skel_of_tyvar_ tyvar xs
  end

let rec skeleton_of_target_ty tty conslist = 
  begin match tty with 
 | Tyvar x -> (get_skel_of_tyvar x conslist)
 | Arrow (a1,(a2,_)) -> SkelArrow (skeleton_of_target_ty a1 conslist, skeleton_of_target_ty a2 conslist)
 | Tuple tup -> assert false
 | Handler ((a1,_),(a2,_)) -> SkelHandler (skeleton_of_target_ty a1 conslist, skeleton_of_target_ty a2 conslist)
 | PrimTy pt -> PrimSkel pt 
  end


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
 | TySchemeTy (ty_param,_,a) -> assert false
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
 if (queue == []) then 
 begin 
 Print.debug "=============FINAL LOOP Result============";
  (sub,paused)
 end
 else
 let cons::rest_queue = queue in 
 begin match cons with
 (* α : τ *)
 | Typed.TyvarHasSkel (tvar,skel) ->
    begin match skel with 
    (* α : ς *)
    | SkelVar p ->
        Print.debug "=========End loop============";
        unify (sub , paused @ [cons] , rest_queue)
    (* α : int *)
    | PrimSkel ps -> 
        let sub1 = TyVarToTy (tvar, Types.PrimTy ps) in 
        Print.debug "=========End loop============";
        unify (sub @ [sub1], [], apply_sub [sub1] (rest_queue @ paused))
    (* α : τ₁ -> τ₂ *)
    | SkelArrow (sk1,sk2) ->
        let ty_p1 = Params.fresh_ty_param () in 
        let ty_p2 = Params.fresh_ty_param () in 
        let tvar1 = Types.Tyvar (ty_p1) in 
        let tvar2 = Types.Tyvar (ty_p2) in 
        let d_p1  = Params.fresh_dirt_param () in 
        let dvar1 = Types.SetVar (EffectSet.empty , d_p1) in 
        let sub1  = TyVarToTy (tvar, Types.Arrow (tvar1 , (tvar2,dvar1))) in 
        let cons1 = TyvarHasSkel (ty_p1,sk1) in 
        let cons2 = TyvarHasSkel (ty_p2,sk2) in
        Print.debug "=========End loop============";
        unify ( sub @ [sub1], [], [cons1;cons2] @ (apply_sub [sub1] (rest_queue @ paused) ) ) 
    (* α : τ₁ => τ₂ *)
    | SkelHandler (sk1,sk2) ->
        let ty_p1 = Params.fresh_ty_param () in 
        let ty_p2 = Params.fresh_ty_param () in 
        let tvar1 = Types.Tyvar (ty_p1) in 
        let tvar2 = Types.Tyvar (ty_p2) in 
        let d_p1 = Params.fresh_dirt_param () in 
        let dvar1 = Types.SetVar (EffectSet.empty , d_p1) in 
        let d_p2 = Params.fresh_dirt_param () in 
        let dvar2 = Types.SetVar (EffectSet.empty , d_p2) in 
        let sub1= TyVarToTy (tvar, Types.Handler ((tvar1,dvar1) , (tvar2,dvar2))) in 
        let cons1 = TyvarHasSkel (ty_p1,sk1) in 
        let cons2 = TyvarHasSkel (ty_p2,sk2) in
        Print.debug "=========End loop============";
        unify ( sub @ [sub1], [], [cons1;cons2] @ (apply_sub [sub1] (rest_queue @ paused) ) ) 
    | ForallSkel (p,sk1)-> assert false
    end
 
 (* τ₁ = τ₂ *)
 | Typed.SkelEq (sk1,sk2) ->
    begin match (sk1,sk2) with
    (* ς = ς *)
    | (SkelVar sp1, SkelVar sp2) when (sp1 = sp2) ->
        Print.debug "=========End loop============";
        unify (sub, paused, rest_queue)

    (* ς₁ = τ₂ *)
    | (SkelVar sp1, sk2a) when (not (List.mem sp1 (free_skeleton sk2a))) ->
        let sub1 = SkelVarToSkel (sp1,sk2a) in 
        Print.debug "=========End loop============";
        unify (sub @ [sub1], [] , apply_sub [sub1] (rest_queue @ paused))

    (* τ₁ = ς₂ *)
    | (sk2a, SkelVar sp1) when (not (List.mem sp1 (free_skeleton sk2a))) ->
        let sub1 = SkelVarToSkel (sp1,sk2a) in 
        Print.debug "=========End loop============";
        unify (sub @ [sub1], [] , apply_sub [sub1] (rest_queue @ paused))

    (* int = int *) 
    | (PrimSkel ps1, PrimSkel ps2) when (ps1 = ps2) ->
        Print.debug "=========End loop============";
        unify (sub, paused, rest_queue)

    (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *) 
    | (SkelArrow (ska,skb) , SkelArrow (skc,skd)) ->
        Print.debug "=========End loop============";
        unify (sub, paused, [Typed.SkelEq(ska,skc); Typed.SkelEq(skb,skd)] @ rest_queue)

    (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *) 
    | (SkelHandler (ska,skb) , SkelHandler (skc,skd)) ->
        Print.debug "=========End loop============";
        unify (sub, paused, [Typed.SkelEq(ska,skc); Typed.SkelEq(skb,skd)] @ rest_queue)
    | _ -> assert false
    end
 (* ω : A <= B *)
 | Typed.TyOmega (omega,tycons) ->
    begin match tycons with

    (* ω : A <= A *)
    | (x,y) when Types.types_are_equal x y ->
        let sub1 = CoerTyVarToTyCoercion (omega, Typed.ReflTy(x)) in
        Print.debug "=========End loop============";
 	unify (sub @ [sub1], paused, rest_queue)
    
    (* ω : α <= β *)
    (* TOM: I think this case is wrong because it does not propagate skeleton equality 
            and is otherwise correctly subsumed by one of the two type variable cases below 
            so we'd better get rid of it.

    | (Types.Tyvar a, Types.Tyvar b) ->
        Print.debug "=========End loop============";
 	unify (sub, (cons::paused), rest_queue)
    *)

    (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
    | (Types.Arrow(a1,(aa1,d1)) , Types.Arrow(a2,(aa2,d2))) ->
 	let new_ty_coercion_var = Params.fresh_ty_coercion_param () in 
        let new_ty_coercion_var_coer = Typed.TyCoercionVar new_ty_coercion_var in 
        let new_ty_coercion_var2 = Params.fresh_ty_coercion_param () in 
        let new_ty_coercion_var_coer2 = Typed.TyCoercionVar new_ty_coercion_var2 in
        let new_dirt_coercion_var = Params.fresh_dirt_coercion_param () in
        let new_dirt_coercion_var_coer = Typed.DirtCoercionVar new_dirt_coercion_var in
        let dirty_coercion_c = Typed.BangCoercion (new_ty_coercion_var_coer2, new_dirt_coercion_var_coer) in 
   	let sub1 = CoerTyVarToTyCoercion (omega, Typed.ArrowCoercion (new_ty_coercion_var_coer,dirty_coercion_c)) in 
   	let ty_cons = Typed.TyOmega(new_ty_coercion_var,(a2,a1)) in
        let ty2_cons = Typed.TyOmega (new_ty_coercion_var2,(aa1,aa2) ) in 
        let dirt_cons = Typed.DirtOmega(new_dirt_coercion_var,(d1,d2) )in 
   	Print.debug "=========End loop============";
        unify (sub @ [sub1], paused, (List.append [ty_cons;ty2_cons;dirt_cons] rest_queue))

    (* ω : D₁ => C₁ <= D₂ => C₂ *)
    | (Types.Handler((a1,d1),(a11,d11)) , Types.Handler((a2,d2),(a22,d22))) ->
        let new_ty_coercion_var_1 = Params.fresh_ty_coercion_param () in
        let new_dirt_coercion_var_2 = Params.fresh_dirt_coercion_param () in 
        let new_ty_coercion_var_3 = Params.fresh_ty_coercion_param () in 
        let new_dirt_coercion_var_4 = Params.fresh_dirt_coercion_param () in 
        let new_ty_coercion_var_coer_1 = Typed.TyCoercionVar new_ty_coercion_var_1 in 
        let new_dirt_coercion_var_coer_2 = Typed.DirtCoercionVar new_dirt_coercion_var_2 in 
        let new_ty_coercion_var_coer_3 = Typed.TyCoercionVar new_ty_coercion_var_3 in 
        let new_dirt_coercion_var_coer_4 = Typed.DirtCoercionVar new_dirt_coercion_var_4 in
        let sub1 = CoerTyVarToTyCoercion (omega, Typed.HandlerCoercion ( Typed.BangCoercion (new_ty_coercion_var_coer_1,new_dirt_coercion_var_coer_2),
                                                                         Typed.BangCoercion (new_ty_coercion_var_coer_3,new_dirt_coercion_var_coer_4))) in
        let cons1 = Typed.TyOmega(new_ty_coercion_var_1, (a2,a1)) in 
        let cons2 = Typed.DirtOmega(new_dirt_coercion_var_2, (d2,d1)) in 
        let cons3 = Typed.TyOmega(new_ty_coercion_var_3, (a11,a22)) in
        let cons4 = Typed.DirtOmega(new_dirt_coercion_var_4, (d11,d22)) in 
   	Print.debug "=========End loop============";
        unify (sub @ [sub1], paused, (List.append [cons1;cons2;cons3;cons4] rest_queue)) 

    (* ω : α <= A *)
    | (Types.Tyvar tv, a) ->
        (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
        let skel_tv = get_skel_of_tyvar tv (paused @ rest_queue) in 
        let skel_a = skeleton_of_target_ty a (paused @ rest_queue) in 
        if skel_tv = skel_a 
          then 
            begin 
              Print.debug "=========End loop============";
              unify(sub, cons :: paused , rest_queue)
            end
          else
            begin
              Print.debug "=========End loop============";
              unify(sub, cons :: paused , (SkelEq(skel_tv,skel_a)) :: rest_queue)
            end

    (* ω : A <= α *)
    | (a , Types.Tyvar tv) ->
 	(* unify_ty_vars (sub,paused,rest_queue) tv a cons *)
        let skel_tv = get_skel_of_tyvar tv (paused @ rest_queue) in 
        let skel_a = skeleton_of_target_ty a (paused @ rest_queue) in 
        if skel_tv = skel_a 
          then 
            begin 
              Print.debug "=========End loop============";
              unify(sub, cons :: paused , rest_queue)
            end
          else
            begin
              Print.debug "=========End loop============";
              unify(sub, cons :: paused , (SkelEq(skel_tv,skel_a)) :: rest_queue)
            end
    | _ -> assert false
    end
 
 (* ω : Δ₁ <= Δ₂ *)
 | Typed.DirtOmega(omega, dcons) ->
    begin match dcons with 

    (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *) 
    | (Types.SetVar(s1,v1) ,Types.SetVar(s2,v2) ) ->
      if (Types.EffectSet.is_empty s1) then 
      begin 
        Print.debug "=========End loop============";
        unify (sub ,(cons::paused), rest_queue)
        end 
      else begin 
        let omega'    = Params.fresh_dirt_coercion_param() in
        let diff_set  = Types.EffectSet.diff s1 s2 in
        let union_set = Types.EffectSet.union s1 s2 in
        let sub'      = [ DirtVarToDirt(v2, Types.SetVar (diff_set, (Params.fresh_dirt_param ())))
                        ; CoerDirtVartoDirtCoercion(omega, Typed.UnionDirt (s1, DirtCoercionVar omega'))] in 
        let new_cons  = (Typed.DirtOmega(omega', (Types.SetVar( (Types.EffectSet.empty),v1) , Types.SetVar(union_set,v2)))) in 
        Print.debug "=========End loop============";
        unify (sub @ sub', [] , apply_sub sub' ((new_cons :: paused) @ rest_queue ))
      end

    (* ω : Ø <= Δ₂ *) 
   | (Types.SetEmpty s1, d) when (Types.EffectSet.is_empty s1) ->
      let sub1 = CoerDirtVartoDirtCoercion(omega,(Typed.Empty d)) in 
      Print.debug "=========End loop============";
      unify(sub @ [sub1], paused, rest_queue)

    (* ω : δ₁ <= Ø *) 
   | (Types.SetVar (s1,v1), Types.SetEmpty s2) when ((Types.EffectSet.is_empty s1) && (Types.EffectSet.is_empty s2) ) ->
      let sub1 = [CoerDirtVartoDirtCoercion(omega,(Typed.Empty (Types.SetEmpty Types.EffectSet.empty))) ; 
                  DirtVarToDirt(v1, (Types.SetEmpty Types.EffectSet.empty))] in 
      Print.debug "=========End loop============";
      unify( (sub @ sub1), [], apply_sub sub1 (paused @ rest_queue))

    (* ω : O₁ <= O₂ *) 
   | (Types.SetEmpty s1, Types.SetEmpty s2)->
      if(Types.EffectSet.subset s1 s2) then
      begin 
        let sub1 = CoerDirtVartoDirtCoercion (omega, Typed.UnionDirt ( s2, (Typed.Empty (Types.SetEmpty (Types.EffectSet.diff s2 s1))))) in 
        Print.debug "=========End loop============";
        unify( sub @ [sub1], paused, rest_queue ) 
      end
      else assert false
   
    (* ω : O₁ <= O₂ ∪ δ₂ *) 
   | (Types.SetEmpty s1, Types.SetVar(s2,v2)) ->
     let v2' = Params.fresh_dirt_param () in
     let sub1 = [ CoerDirtVartoDirtCoercion (omega, Typed.UnionDirt ( s1, (Typed.Empty (Types.SetVar(Types.EffectSet.diff s2 s1, v2')))));
                  DirtVarToDirt(v2, Types.SetVar ( (Types.EffectSet.diff s1 s2) ,  v2'))] in 
      Print.debug "=========End loop============";
      unify( (sub @ sub1), [], apply_sub sub1 (paused @ rest_queue))    
 
   | _ -> Print.debug "=========End loop============";
        unify (sub ,(cons::paused), rest_queue)
   end 
 end 

and unify_ty_vars (sub,paused,rest_queue) tv a cons= 
  let dependent_tyvars = (fix_union_find [tv] paused) in 
       let free_a = free_target_ty a in
(*     let dependent_tyvars = (union_find_tyvar tv [] paused) in *)
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
