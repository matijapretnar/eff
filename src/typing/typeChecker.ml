open Typed
open Types
open Unification

type ('term, 'ttype) target_term = {
  term: 'term;
  target_type: 'ttype;
  location: Location.t;
};;


type checker_state = {
  term_vars : (Typed.variable, Types.target_ty) OldUtils.assoc;
  type_vars : Params.ty_param list;
  dirt_vars : Params.dirt_param list;
  omega_ty  : (Params.ty_coercion_param ,  Types.ct_ty) OldUtils.assoc;
  omega_dirt: (Params.dirt_coercion_param ,  Types.ct_dirt) OldUtils.assoc;
  omega_dirty: (Params.dirty_coercion_param , (Types.target_dirty * Types.target_dirty) ) OldUtils.assoc;
} ;;

let extend_state_ty_vars st ty_var = 
    {st with type_vars = (ty_var::st.type_vars)}

let extend_state_term_vars st t_var tty = 
    {st with term_vars = ((t_var,tty)::st.term_vars)}

let extend_state_dirt_vars st dirt_var = 
    {st with dirt_vars = dirt_var::st.dirt_vars}

let extend_state_omega_ty st tcp ctty =
   {st with omega_ty = (tcp,ctty) :: st.omega_ty}


let extend_state_omega_dirt st tcp ctdrt =
   {st with omega_dirt = (tcp,ctdrt) :: st.omega_dirt}


let new_checker_state = 
{
  term_vars = [];
  type_vars = [];
  dirt_vars = [];
  omega_ty = [];
  omega_dirt = [];
  omega_dirty = [];
}


let rec type_check_comp st c =  
  begin match c with 
  | Value e -> 
      let ty1 = type_check_exp st e.term in 
      (ty1,SetEmpty (empty_effect_set))
   | LetVal (v1,e1,c1) ->
      let t_v = type_check_exp st e1.term in 
      let st' = extend_state_term_vars st v1 t_v in 
      type_check_comp st' c1.term

  | LetRec (l,c1) -> assert false 
  | Match (e,alist) -> assert false
  | Apply (e1,e2) -> 
      let t_e1 = type_check_exp st e1.term in 
      let Types.Arrow(ty_1,dty_1) = t_e1 in 
      let ty_e2 = type_check_exp st e2.term in 
      if (ty_1 = ty_e2) then 
      dty_1 
      else
      assert false
 | Handle (e1,c1) ->
      let t_e1 = type_check_exp st e1.term in 
      let Types.Handler(dty_1,dty_2) = t_e1 in 
      let ty_c1 = type_check_comp st c1.term in 
      if (dty_1 = ty_c1) then 
      dty_2 
      else
      assert false 
  | Call( (eff, (eff_in,eff_out)) ,e2, abs ) ->
      let e2_ty = type_check_exp st e2.term in 
      begin match  e2_ty with 
      | eff_in ->  
              let (x,c1) = abs.term in 
              let Typed.PVar p = x.term in 
              let st' = extend_state_term_vars st p eff_out in 
              let (final_ty,final_dirt) = type_check_comp st' c1.term in
              begin match Types.is_effect_member eff final_dirt with
              | true -> (final_ty,final_dirt)
              | _ -> assert false
              end 
      |_-> assert false
    end
       

  | Op(ef,e1) -> assert false
  | Bind (c1,a1) -> 
      let (c1_ty,c1_drt) = type_check_comp st c1.term in 
      let (x,c2) = a1.term in 
      let Typed.PVar p = x.term in 
      let st' = extend_state_term_vars st p c1_ty in 
      let (c2_ty,c2_drt) = type_check_comp st' c2.term in 
      if (c1_drt = c2_drt) then 
          (c2_ty,c2_drt)
      else assert false 
  | CastComp (c1,dc) -> 
      let c1_drty_ty = type_check_comp st c1.term in 
      let (dc1_1,dc_2) = type_check_dirty_coercion st dc in 
      if (c1_drty_ty = dc1_1) then dc_2 else assert false
  | CastComp_ty (c1,tc1)-> assert false
  | CastComp_dirt (c1,tc1)-> assert false
  end


and type_check_exp st e =
begin match e with 
  | Var v -> 
      begin match (OldUtils.lookup v st.term_vars) with
      | Some ty -> ty
      | _ -> assert false
    end
  | BuiltIn(s,i) -> assert false
  | Const const -> 
      begin match const with
        | Integer _ ->  Types.PrimTy IntTy
        | String _ -> Types.PrimTy StringTy
        | Boolean _ -> Types.PrimTy BoolTy
        | Float _ -> Types.PrimTy FloatTy
      end 
  | Tuple elist -> assert false
  | Record r -> assert false 
  | Variant (lbl, e1) -> assert false
  | Lambda (pat,ty1,c1)-> 
      let PVar p = pat.term in 
      let ty1' = type_check_ty st ty1 in 
      let st' = extend_state_term_vars st p ty1 in
      let c_ty = type_check_comp st' c1.term in 
      Types.Arrow (ty1',c_ty) 
 
  | Effect (eff,(eff_in,eff_out)) -> 
      Types.Arrow(eff_in, (eff_out, Types.SetEmpty (list_to_effect_set [eff])))

  | Handler h -> assert false
  | BigLambdaTy(ty_param,e1) -> 
      let st' = extend_state_ty_vars st ty_param in 
      let e1_ty = type_check_exp st' e1.term in 
      TySchemeTy (ty_param, Types.PrimSkel Types.IntTy, e1_ty)
  | BigLambdaDirt(dirt_param,e1) ->
      let st' = extend_state_dirt_vars st dirt_param in 
      let e1_ty = type_check_exp st' e1.term in 
      TySchemeDirt (dirt_param,e1_ty) 
   | CastExp (e1,tc1) -> 
      let e1_ty = type_check_exp st e1.term in 
      let (tc1a,tc1b) = type_check_ty_coercion st tc1 in 
      if (tc1a = e1_ty) then tc1b else assert false
  | ApplyTyExp (e1,tty) ->
      let (Types.TySchemeTy (p_e1,_,ty_e1)) = type_check_exp st e1.term in 
      let tty1 = type_check_ty st tty in
      let sub = Unification.TyVarToTy (p_e1,tty1) in
      Unification.apply_sub_ty sub ty_e1 
  | ApplyDirtExp (e1,d1) ->
      let (Types.TySchemeDirt (p_e1,ty_e1)) = type_check_exp st e1.term in 
      let tty1 = type_check_dirt st d1 in
      let sub = Unification.DirtVarToDirt (p_e1,tty1) in
      Unification.apply_sub_ty sub ty_e1
  | LambdaTyCoerVar (tcp1,ct_ty1,e1) ->
      let st' = extend_state_omega_ty st tcp1 ct_ty1 in 
      let e1_ty = type_check_exp st' e1.term in 
      let ct_ty1' = type_check_ty_cons st ct_ty1 in 
      Types.QualTy(ct_ty1',e1_ty)

  | LambdaDirtCoerVar (dcp1,ct_dirt1,e1) ->
      let st' = extend_state_omega_dirt st dcp1 ct_dirt1 in 
      let e1_ty = type_check_exp st' e1.term in 
      let ct_dirt1' = type_check_dirt_cons st ct_dirt1 in 
      Types.QualDirt(ct_dirt1',e1_ty)
  | ApplyTyCoercion (e1,tc1) ->
      let tc1' = type_check_ty_coercion st tc1 in 
      let QualTy (cons,e1_ty) = type_check_exp st e1.term in 
      if(tc1' = cons) then e1_ty else assert false

  | ApplyDirtCoercion (e1,dc1) ->
      let dc1' = type_check_dirt_coercion st dc1 in 
      let QualDirt (cons,e1_ty) = type_check_exp st e1.term in 
      if(dc1' = cons) then e1_ty else assert false
end

and type_check_ty_coercion st ty_coer = 
  begin match ty_coer with 
  | ReflTy tty -> (tty,tty)
  | ArrowCoercion(tycoer1,dirtycoer) ->
      let (t_2,t_1) = type_check_ty_coercion st tycoer1 in 
      let (c_1,c_2) = type_check_dirty_coercion st dirtycoer in 
      (Types.Arrow(t_1,c_1), Types.Arrow(t_2,c_2))
  
  | HandlerCoercion (dirtycoer1,dirtycoer2) -> 
      let (c_3,c_1) = type_check_dirty_coercion st dirtycoer1 in 
      let (c_2,c_4) = type_check_dirty_coercion st dirtycoer2 in 
      (Types.Handler(c_1,c_2), Types.Handler(c_3,c_4)) 
  | TyCoercionVar p ->
      begin match (OldUtils.lookup p st.omega_ty) with 
      | None -> assert false
      | Some pi -> pi
    end
  | SequenceTyCoer (ty_coer1,ty_coer2) -> 
      let (t1,t2) = type_check_ty_coercion st ty_coer1 in 
      let (t2,t3) = type_check_ty_coercion st ty_coer2 in 
      (t1,t3)
  | TupleCoercion tcl -> assert false
  | LeftArrow tc1 -> 
      let ( Types.Arrow(t1,_), Types.Arrow(t2,_) ) = type_check_ty_coercion st tc1 in 
      (t2,t1)

  | ForallTy (ty_param,ty_coer1) -> 
      let new_st = extend_state_ty_vars st ty_param in
      let (t1,t2) = type_check_ty_coercion new_st ty_coer1 in 
      (Types.TySchemeTy (ty_param,Types.PrimSkel Types.IntTy,t1) , Types.TySchemeTy (ty_param,Types.PrimSkel Types.IntTy,t2))

  | ApplyTyCoer (ty_coer1,tty1) -> 
      let (Types.TySchemeTy (ty_param1,_,t1) , Types.TySchemeTy (ty_param2,_,t2)) = type_check_ty_coercion st ty_coer1 in 
      let tt = type_check_ty st tty1 in
      let sub = Unification.TyVarToTy(ty_param1,tt) in 
      if(ty_param1 = ty_param2) then 
      (Unification.apply_sub_ty sub t1, Unification.apply_sub_ty sub t2)
      else
      assert false

  | ForallDirt (dirt_param,ty_coer1) -> 
      let new_st = extend_state_dirt_vars st dirt_param in
      let (t1,t2) = type_check_ty_coercion new_st ty_coer1 in 
      (Types.TySchemeDirt (dirt_param,t1) , Types.TySchemeDirt (dirt_param,t2))

  | ApplyDirCoer (ty_coer1,drt) ->
      let (Types.TySchemeDirt (drt_param1,t1) , Types.TySchemeDirt (drt_param2,t2)) = type_check_ty_coercion st ty_coer1 in 
      let tt = type_check_dirt st drt in
      let sub = Unification.DirtVarToDirt(drt_param1,tt) in 
      if(drt_param1 = drt_param2) then 
      (Unification.apply_sub_ty sub t1, Unification.apply_sub_ty sub t2)
      else
      assert false
  
  | PureCoercion dirty_coer1 -> 
      let ((t1,_),(t2,_)) = type_check_dirty_coercion st dirty_coer1 in 
      (t1,t2)

  | QualTyCoer (ty_cons, ty_coer1) ->
      let (tc1,tc2) = type_check_ty_cons st ty_cons in 
      let (t1,t2) = type_check_ty_coercion st ty_coer1 in 
      ( QualTy((tc1,tc2),t1) , QualTy((tc1,tc2),t2) )
  
  | QualDirtCoer (dirt_cons,ty_coer1) -> 
      let _ = type_check_dirt_cons st dirt_cons in 
      let (t1,t2) = type_check_ty_coercion st ty_coer1 in 
      (QualDirt(dirt_cons,t1) , QualDirt(dirt_cons,t2))
  
  | ApplyQualTyCoer (ty_coer1,ty_coer_applied) ->
      let ty_coer_applied_cons = type_check_ty_coercion st ty_coer_applied in
      let ( QualTy(cons1,t1) , QualTy(cons2,t2) ) = type_check_ty_coercion st ty_coer1 in 
      if (cons1 = cons2 && cons2 = ty_coer_applied_cons) then (t1,t2) else assert false
  
  | ApplyQualDirtCoer (ty_coer1,dirt_coer_applied) ->
      let dirt_coer_applied_cons = type_check_dirt_coercion st dirt_coer_applied in
      let ( QualDirt(cons1,t1) , QualDirt(cons2,t2) ) = type_check_ty_coercion st ty_coer1 in 
      if (cons1 = cons2 && cons2 = dirt_coer_applied_cons) then (t1,t2) else assert false
  end

and type_check_dirty_coercion st dirty_coer =
  begin match dirty_coer with
  | BangCoercion (tc,dc) -> 
      let (t1,t2) = type_check_ty_coercion st tc in 
      let (d1,d2) = type_check_dirt_coercion st dc in 
      ((t1,d1),(t2,d2))
  | RightArrow tc ->
      let ( Types.Arrow(_,c1), Types.Arrow(_,c2) ) = type_check_ty_coercion st tc in 
      (c1,c2)
  | RightHandler tc -> 
      let ( Types.Handler(_,c1), Types.Handler(_,c2) ) = type_check_ty_coercion st tc in 
      (c1,c2)
  | LeftHandler tc ->
      let ( Types.Handler(c2,_), Types.Handler(c1,_) ) = type_check_ty_coercion st tc in 
      (c1,c2)
  | SequenceDirtyCoer(dc1,dc2) ->
      let (t1,t2) = type_check_dirty_coercion st dc1 in 
      let (t2,t3) = type_check_dirty_coercion st dc2 in 
      (t1,t3)
  end

and type_check_dirt_coercion st dirt_coer = 
  begin match dirt_coer with
  | ReflDirt d -> (d,d)
  | DirtCoercionVar p ->
      begin match (OldUtils.lookup p st.omega_dirt) with 
      | None -> assert false
      | Some pi -> pi
    end
  | Empty d ->
        let d' = type_check_dirt st d in  
        ( SetEmpty (Types.empty_effect_set), d')
  | UnionDirt (es,dirt_coer1) ->
        let (dc_a,dc_b) = type_check_dirt_coercion st dirt_coer1 in 
        let dc_a' = 
          begin match dc_a with 
          | SetVar (es1,v) -> SetVar ((effect_set_union es es1),v)
          | SetEmpty (es1) -> SetEmpty(effect_set_union es es1)
          end in 
        let dc_b' = 
          begin match dc_b with 
          | SetVar (es1,v) -> SetVar ((effect_set_union es es1),v)
          | SetEmpty (es1) -> SetEmpty(effect_set_union es es1)
          end in 
       (dc_a',dc_b')
  | SequenceDirtCoer(dc1, dc2) -> 
        let (t1,t2) = type_check_dirt_coercion st dc1 in 
        let (t2,t3) = type_check_dirt_coercion st dc2 in 
        (t1,t3)
  | DirtCoercion (dirty_coer1) -> 
        let ((_,t1),(_,t2)) = type_check_dirty_coercion st dirty_coer1 in 
        (t1,t2)
  end

and type_check_ty_cons st (t1,t2) =
  let t1' = type_check_ty st t1 in 
  let t2' = type_check_ty st t2 in 
  (t1',t2') 

and type_check_dirt_cons st (d1,d2) =
  let d1' = type_check_dirt st d1 in 
  let d2' = type_check_dirt st d2 in 
  (d1',d2') 

and type_check_dirt st d =
  begin match d with 
  | SetEmpty eset when (effect_set_is_empty eset)-> d
  | SetEmpty _ ->
      d
  | SetVar(_,v) ->
      if List.mem v st.dirt_vars then 
        d
      else 
        assert false
  end

and type_check_ty st ty =
  begin match ty with 
  | Tyvar typ1 when( List.mem typ1 st.type_vars) -> ty
  | Arrow (tty1,tty2) ->
      let _ = type_check_ty st tty1 in 
      let _ = type_check_dirty_ty st tty2 in 
      ty 

  | Tuple ttyl ->Tuple (List.map (fun x -> type_check_ty st x) ttyl)
  | Handler (tty1,tty2) ->
      let _ = type_check_dirty_ty st tty1 in 
      let _ = type_check_dirty_ty st tty2 in 
      ty 
  | PrimTy _ -> ty
  | QualTy (ct_ty1,tty1) ->
    let _ = type_check_ty_cons st ct_ty1 in 
    let _ = type_check_ty st tty1 in 
    ty  
  | QualDirt (ct_ty1,tty1) ->
    let _ = type_check_dirt_cons st ct_ty1 in 
    let _ = type_check_ty st tty1 in 
    ty  
  | TySchemeTy (ty_param ,_,tty1) -> 
      let st' = extend_state_ty_vars st ty_param in 
      let _ = type_check_ty st' tty1 in 
      ty 
  | TySchemeDirt (dirt_param ,tty1) ->
      let st' = extend_state_dirt_vars st dirt_param in 
      let _ = type_check_ty st' tty1 in 
      ty 
  | _ -> assert false
end

and type_check_dirty_ty st (ty,drt) = 
  let _ = type_check_ty st ty in 
  let _ = type_check_dirt st drt in 
  (ty,drt)

