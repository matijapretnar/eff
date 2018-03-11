open Types
open Typed
module STyParams = Set.Make (Params.Ty)

let set_of_list =
  List.fold_left (fun acc x -> STyParams.add x acc) STyParams.empty


type substitution =
  | CoerTyParamToTyCoercion of (Params.TyCoercion.t * Typed.ty_coercion)
  | CoerDirtVartoDirtCoercion of (Params.DirtCoercion.t * Typed.dirt_coercion)
  | TyParamToTy of (Params.Ty.t * Types.target_ty)
  | DirtVarToDirt of (Params.Dirt.t * Types.dirt)
  | SkelParamToSkel of (Params.Skel.t * Types.skeleton)

let print_sub ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | CoerTyParamToTyCoercion (p, t) ->
      print "%t :-coertyTotyCoer-> %t"
        (Params.TyCoercion.print p)
        (Typed.print_ty_coercion t)
  | CoerDirtVartoDirtCoercion (p, d) ->
      print "%t :-coertyDirtoDirtCoer-> %t"
        (Params.DirtCoercion.print p)
        (Typed.print_dirt_coercion d)
  | TyParamToTy (p, t) ->
      print "%t :-tyvarToTargetty-> %t" (Params.Ty.print p)
        (Types.print_target_ty t)
  | DirtVarToDirt (p, d) ->
      print "%t :-dirtvarToTargetdirt-> %t" (Params.Dirt.print p)
        (Types.print_target_dirt d)
  | SkelParamToSkel (p, s) ->
      print "%t :-skelvarToSkeleton-> %t" (Params.Skel.print p)
        (Types.print_skeleton s)


let rec print_s_list = function
  | [] -> Print.debug "---------------------"
  | e :: l ->
      Print.debug "%t" (print_sub e) ;
      print_s_list l


let apply_sub_dirt sub drt =
  match drt.row with
  | ParamRow p -> (
    match sub with
    | DirtVarToDirt (p', drt2) when p = p' ->
        Types.add_effects drt.effect_set drt2
    | _ -> drt )
  | EmptyRow -> drt


let rec apply_sub_skel sub sk =
  match sk with
  | SkelParam p -> (
    match sub with SkelParamToSkel (skv, sk1) when skv = p -> sk1 | _ -> sk )
  | PrimSkel _ -> sk
  | SkelArrow (sk1, sk2) ->
      SkelArrow (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | SkelHandler (sk1, sk2) ->
      SkelHandler (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | ForallSkel (p, sk1) -> ForallSkel (p, apply_sub_skel sub sk1)


let rec apply_sub_ty sub ty =
  match ty with
  | TyParam typ1 -> (
    match sub with
    | TyParamToTy (typ2, ttype) when typ1 = typ2 -> ttype
    | _ -> ty )
  | Arrow (tty1, tty2) ->
      Arrow (apply_sub_ty sub tty1, apply_sub_dirty_ty sub tty2)
  | Tuple ttyl -> Tuple (List.map (fun x -> apply_sub_ty sub x) ttyl)
  | Handler (tydrty1, tydrty2) ->
      Handler (apply_sub_dirty_ty sub tydrty1, apply_sub_dirty_ty sub tydrty2)
  | PrimTy _ -> ty
  | QualTy (ct_ty1, tty1) ->
      QualTy (apply_sub_ct_ty sub ct_ty1, apply_sub_ty sub tty1)
  | QualDirt (ct_drt1, tty1) ->
      QualDirt (apply_sub_ct_dirt sub ct_drt1, apply_sub_ty sub tty1)
  | TySchemeTy (ty_param, sk, tty1) ->
      TySchemeTy (ty_param, apply_sub_skel sub sk, apply_sub_ty sub tty1)
  | TySchemeDirt (dirt_param, tty1) ->
      TySchemeDirt (dirt_param, apply_sub_ty sub tty1)
  | TySchemeSkel (skvar, ty) -> TySchemeSkel (skvar, apply_sub_ty sub ty)


and apply_sub_dirty_ty sub (ty, drt) =
  (apply_sub_ty sub ty, apply_sub_dirt sub drt)


and apply_sub_ct_ty sub (ty1, ty2) =
  (apply_sub_ty sub ty1, apply_sub_ty sub ty2)


and apply_sub_ct_dirt sub (drt1, drt2) =
  (apply_sub_dirt sub drt1, apply_sub_dirt sub drt2)


let rec apply_sub_tycoer sub ty_coer =
  match ty_coer with
  | ReflTy tty -> ReflTy (apply_sub_ty sub tty)
  | ArrowCoercion (tycoer1, dirtycoer) ->
      ArrowCoercion
        (apply_sub_tycoer sub tycoer1, apply_sub_dirtycoer sub dirtycoer)
  | HandlerCoercion (dirtycoer1, dirtycoer2) ->
      HandlerCoercion
        (apply_sub_dirtycoer sub dirtycoer1, apply_sub_dirtycoer sub dirtycoer2)
  | TyCoercionVar p -> (
    match sub with
    | CoerTyParamToTyCoercion (p', t_coer) when p = p' -> t_coer
    | _ -> TyCoercionVar p )
  | SequenceTyCoer (ty_coer1, ty_coer2) ->
      SequenceTyCoer
        (apply_sub_tycoer sub ty_coer1, apply_sub_tycoer sub ty_coer2)
  | TupleCoercion tcl ->
      TupleCoercion (List.map (fun x -> apply_sub_tycoer sub x) tcl)
  | LeftArrow tc1 -> LeftArrow (apply_sub_tycoer sub tc1)
  | ForallTy (ty_param, ty_coer1) ->
      ForallTy (ty_param, apply_sub_tycoer sub ty_coer1)
  | ApplyTyCoer (ty_coer1, tty1) ->
      ApplyTyCoer (apply_sub_tycoer sub ty_coer1, apply_sub_ty sub tty1)
  | ForallDirt (dirt_param, ty_coer1) ->
      ForallDirt (dirt_param, apply_sub_tycoer sub ty_coer1)
  | ApplyDirCoer (ty_coer1, drt) ->
      ApplyDirCoer (apply_sub_tycoer sub ty_coer1, apply_sub_dirt sub drt)
  | PureCoercion dirty_coer1 ->
      PureCoercion (apply_sub_dirtycoer sub dirty_coer1)
  | ForallSkel (ty_param, ty_coer1) ->
      ForallSkel (ty_param, apply_sub_tycoer sub ty_coer1)
  | ApplySkelCoer (ty_coer1, sk1) ->
      ApplySkelCoer (apply_sub_tycoer sub ty_coer1, apply_sub_skel sub sk1)


and apply_sub_dirtcoer sub dirt_coer =
  match dirt_coer with
  | ReflDirt d -> ReflDirt (apply_sub_dirt sub d)
  | DirtCoercionVar p -> (
    match sub with
    | CoerDirtVartoDirtCoercion (p', dc) when p' = p -> dc
    | _ -> dirt_coer )
  | Empty d -> Empty (apply_sub_dirt sub d)
  | UnionDirt (es, dirt_coer1) ->
      UnionDirt (es, apply_sub_dirtcoer sub dirt_coer1)
  | SequenceDirtCoer (dirt_coer1, dirt_coer2) ->
      SequenceDirtCoer
        (apply_sub_dirtcoer sub dirt_coer1, apply_sub_dirtcoer sub dirt_coer2)
  | DirtCoercion dirty_coer1 ->
      DirtCoercion (apply_sub_dirtycoer sub dirty_coer1)


and apply_sub_dirtycoer sub dirty_coer =
  match dirty_coer with
  | BangCoercion (ty_coer, dirt_coer) ->
      BangCoercion
        (apply_sub_tycoer sub ty_coer, apply_sub_dirtcoer sub dirt_coer)
  | RightArrow ty_coer1 -> RightArrow (apply_sub_tycoer sub ty_coer1)
  | RightHandler ty_coer1 -> RightHandler (apply_sub_tycoer sub ty_coer1)
  | LeftHandler ty_coer1 -> LeftHandler (apply_sub_tycoer sub ty_coer1)
  | SequenceDirtyCoer (dirty_coer1, dirty_coer2) ->
      SequenceDirtyCoer
        ( apply_sub_dirtycoer sub dirty_coer1
        , apply_sub_dirtycoer sub dirty_coer2 )


let rec apply_sub_comp sub c =
  let c' = apply_sub_plain_comp sub c in
  Print.debug "apply_sub_comp: %t %t" (print_sub sub) (print_computation c) ;
  Typed.annotate c' c.location


and apply_sub_plain_comp sub c =
  match c.term with
  | Value e -> Value (apply_sub_exp sub e)
  | LetVal (e1, (p, ty, c1)) ->
      LetVal
        (apply_sub_exp sub e1, (p, apply_sub_ty sub ty, apply_sub_comp sub c1))
  | LetRec (l, c1) -> assert false (* LetRec (l, c1) *)
  | Match (e, alist) ->
      Match (apply_sub_exp sub e, List.map (apply_sub_abs sub) alist)
  | Apply (e1, e2) -> Apply (apply_sub_exp sub e1, apply_sub_exp sub e2)
  | Handle (e1, c1) -> Handle (apply_sub_exp sub e1, apply_sub_comp sub c1)
  | Call (effect, e1, abs) ->
      Call (effect, apply_sub_exp sub e1, apply_sub_abs_with_ty sub abs)
  | Op (ef, e1) -> Op (ef, apply_sub_exp sub e1)
  | Bind (c1, a1) -> Bind (apply_sub_comp sub c1, apply_sub_abs sub a1)
  | CastComp (c1, dc1) ->
      CastComp (apply_sub_comp sub c1, apply_sub_dirtycoer sub dc1)
  | CastComp_ty (c1, tc1) ->
      CastComp_ty (apply_sub_comp sub c1, apply_sub_tycoer sub tc1)
  | CastComp_dirt (c1, tc1) ->
      CastComp_dirt (apply_sub_comp sub c1, apply_sub_dirtcoer sub tc1)


and apply_sub_exp sub exp =
  let e' = apply_sub_plain_exp sub exp in
  Print.debug "apply_sub_exp: %t %t" (print_sub sub) (print_expression exp) ;
  Typed.annotate e' exp.location


and apply_sub_plain_exp sub e =
  match e.term with
  | Var v -> Var v
  | BuiltIn (s, i) -> BuiltIn (s, i)
  | Const c -> Const c
  | Tuple elist -> Tuple (List.map (fun x -> apply_sub_exp sub x) elist)
  | Record r -> Record r
  | Variant (lbl, e1) -> Variant (lbl, e1)
  | Lambda (pat, ty1, c1) ->
      Lambda (pat, apply_sub_ty sub ty1, apply_sub_comp sub c1)
  | Effect eff -> Effect eff
  | Handler h -> Handler (apply_sub_handler sub h)
  | BigLambdaTy (ty_param, sk, e1) ->
      BigLambdaTy (ty_param, apply_sub_skel sub sk, apply_sub_exp sub e1)
  | BigLambdaDirt (dirt_param, e1) ->
      BigLambdaDirt (dirt_param, apply_sub_exp sub e1)
  | BigLambdaSkel (skel_param, e1) ->
      BigLambdaSkel (skel_param, apply_sub_exp sub e1)
  | CastExp (e1, tc1) ->
      CastExp (apply_sub_exp sub e1, apply_sub_tycoer sub tc1)
  | ApplyTyExp (e1, tty) ->
      ApplyTyExp (apply_sub_exp sub e1, apply_sub_ty sub tty)
  | LambdaTyCoerVar (tcp1, (ty1, ty2), e1) ->
      LambdaTyCoerVar
        ( tcp1
        , (apply_sub_ty sub ty1, apply_sub_ty sub ty2)
        , apply_sub_exp sub e1 )
  | LambdaDirtCoerVar (dcp1, (d1, d2), e1) ->
      LambdaDirtCoerVar
        ( dcp1
        , (apply_sub_dirt sub d1, apply_sub_dirt sub d2)
        , apply_sub_exp sub e1 )
  | ApplyDirtExp (e1, d1) ->
      ApplyDirtExp (apply_sub_exp sub e1, apply_sub_dirt sub d1)
  | ApplyTyCoercion (e1, tc1) ->
      ApplyTyCoercion (apply_sub_exp sub e1, apply_sub_tycoer sub tc1)
  | ApplyDirtCoercion (e1, dc1) ->
      ApplyDirtCoercion (apply_sub_exp sub e1, apply_sub_dirtcoer sub dc1)
  | ApplySkelExp (e1, s1) ->
      ApplySkelExp (apply_sub_exp sub e1, apply_sub_skel sub s1)


and apply_sub_abs sub abs =
  let p, c = abs.term in
  annotate (p, apply_sub_comp sub c) abs.location


and apply_sub_abs_with_ty sub abs =
  let p, t, c = abs.term in
  annotate (p, apply_sub_ty sub t, apply_sub_comp sub c) abs.location


and apply_sub_abs2 sub abs2 =
  let p1, p2, c = abs2.term in
  annotate (p1, p2, apply_sub_comp sub c) abs2.location


and apply_sub_handler sub h =
  let eff_clauses = h.effect_clauses in
  let new_value_clause = apply_sub_abs_with_ty sub h.value_clause in
  let new_eff_clauses =
    OldUtils.assoc_map (fun abs2 -> apply_sub_abs2 sub abs2) eff_clauses
  in
  {effect_clauses= new_eff_clauses; value_clause= new_value_clause}


let rec apply_substitution s c =
  List.fold_left (fun c s -> apply_sub_comp s c) c s


and apply_substitution_exp s ei =
  List.fold_left (fun ei s -> apply_sub_exp s ei) ei s


and apply_substitution_ty s ty1 =
  List.fold_left (fun ty1 s -> apply_sub_ty s ty1) ty1 s


and apply_substitution_dirt s drt =
  List.fold_left (fun drt s -> apply_sub_dirt s drt) drt s


and apply_substitution_skel s ty1 =
  List.fold_left (fun ty1 s -> apply_sub_skel s ty1) ty1 s


(* apply a single sub to a list of constraints *)
let apply_sub1 c_list sub1 =
  match sub1 with
  | TyParamToTy (type_p, target_type) ->
      let mapper cons =
        match cons with
        | Typed.TyOmega (coer_p, (ty1, ty2)) ->
            Typed.TyOmega
              (coer_p, (apply_sub_ty sub1 ty1, apply_sub_ty sub1 ty2))
        (*
       	                | Typed.TyOmega (coer_p, (TyParam tv,ty2)) when (type_p = tv) ->  
       			   Typed.TyOmega (coer_p, (target_type,ty2)) 
                        | Typed.TyOmega (coer_p, (ty2,TyParam tv)) when (type_p = tv) ->  
       			   Typed.TyOmega (coer_p, (ty2,target_type)) 
 *)
        | _ ->
            cons
      in
      List.map mapper c_list
  | DirtVarToDirt (type_p, target_dirt) ->
      let mapper = function
        | Typed.DirtOmega (coerp, (drt1, drt2)) ->
            Typed.DirtOmega
              (coerp, (apply_sub_dirt sub1 drt1, apply_sub_dirt sub1 drt2))
        | Typed.TyOmega (coerp, (ty1, ty2)) ->
            Typed.TyOmega
              (coerp, (apply_sub_ty sub1 ty1, apply_sub_ty sub1 ty2))
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
  | SkelParamToSkel (skel_var, skel) ->
      let mapper cons =
        match cons with
        | Typed.TyParamHasSkel (tv, Types.SkelParam sv) when skel_var = sv ->
            Typed.TyParamHasSkel (tv, skel)
        | _ -> cons
      in
      List.map mapper c_list
  | _ -> c_list


(* apply substitution-list to a list of constraints *)
let rec apply_sub sub c_list = List.fold_left apply_sub1 c_list sub

let rec print_c_list = function
  | [] -> Print.debug "---------------------"
  | e :: l ->
      Print.debug "%t" (Typed.print_omega_ct e) ;
      print_c_list l


let rec print_var_list = function
  | [] -> Print.debug "---------------------"
  | e :: l ->
      Print.debug "%t" (Params.Ty.print e) ;
      print_var_list l


let rec get_skel_of_tyvar tyvar clist =
  Print.debug "getting skeleton of tyvar from list" ;
  Print.debug " TyParam : %t" (Params.Ty.print tyvar) ;
  Print.debug "Constraint list :" ;
  print_c_list clist ;
  get_skel_of_tyvar_ tyvar clist


and get_skel_of_tyvar_ tyvar clist =
  match clist with
  | [] -> assert false
  | (TyParamHasSkel (tv, skel)) :: _ when tyvar = tv -> skel
  | _ :: xs -> get_skel_of_tyvar_ tyvar xs


let rec skeleton_of_target_ty tty conslist =
  match tty with
  | TyParam x -> get_skel_of_tyvar x conslist
  | Arrow (a1, (a2, _)) ->
      SkelArrow
        (skeleton_of_target_ty a1 conslist, skeleton_of_target_ty a2 conslist)
  | Tuple tup -> assert false
  | Handler ((a1, _), (a2, _)) ->
      SkelHandler
        (skeleton_of_target_ty a1 conslist, skeleton_of_target_ty a2 conslist)
  | PrimTy pt -> PrimSkel pt


let rec fix_union_find fixpoint c_list =
  Print.debug "--------------start list-------" ;
  print_var_list fixpoint ;
  Print.debug "---------------end list-------" ;
  let mapper x =
    match x with
    | Typed.TyOmega (_, tycons) -> (
      match tycons with
      | Types.TyParam a, Types.TyParam b
        when List.mem a fixpoint && not (List.mem b fixpoint) ->
          [b]
      | Types.TyParam b, Types.TyParam a
        when List.mem a fixpoint && not (List.mem b fixpoint) ->
          [b]
      | _ -> [] )
    | _ -> []
  in
  let new_fixpoint = fixpoint @ OldUtils.flatten_map mapper c_list in
  let sort_new_fixpoint = List.sort compare new_fixpoint in
  if sort_new_fixpoint = fixpoint then sort_new_fixpoint
  else fix_union_find sort_new_fixpoint c_list


let rec dependent_constraints dep_list acc c_list =
  (*   Print.debug "In dc"; *)
  match c_list with
  | [] -> acc
  | x :: xs ->
    match x with
    | Typed.TyOmega (_, tycons) -> (
      match tycons with
      | Types.TyParam a, Types.TyParam b
        when List.mem a dep_list && List.mem b dep_list ->
          dependent_constraints dep_list (x :: acc) xs
      | _ -> dependent_constraints dep_list acc xs )
    | _ -> dependent_constraints dep_list acc xs


let ty_param_has_skel_step sub paused cons rest_queue tvar skel =
  match skel with
  (* α : ς *)
  | SkelParam p -> (sub, paused @ [cons], rest_queue)
  (* α : int *)
  | PrimSkel ps ->
      let sub1 = TyParamToTy (tvar, Types.PrimTy ps) in
      (sub @ [sub1], [], apply_sub [sub1] (rest_queue @ paused))
  (* α : τ₁ -> τ₂ *)
  | SkelArrow (sk1, sk2) ->
      let tvar1, cons1 = Typed.fresh_ty_with_skel sk1
      and tvar2, cons2 = Typed.fresh_ty_with_skel sk2
      and dvar1 = Types.fresh_dirt () in
      let sub1 = TyParamToTy (tvar, Types.Arrow (tvar1, (tvar2, dvar1))) in
      ( sub @ [sub1]
      , []
      , [cons1; cons2] @ apply_sub [sub1] (rest_queue @ paused) )
  (* α : τ₁ => τ₂ *)
  | SkelHandler (sk1, sk2) ->
      let tvar1, cons1 = Typed.fresh_ty_with_skel sk1
      and tvar2, cons2 = Typed.fresh_ty_with_skel sk2
      and dvar1 = Types.fresh_dirt ()
      and dvar2 = Types.fresh_dirt () in
      let sub1 =
        TyParamToTy (tvar, Types.Handler ((tvar1, dvar1), (tvar2, dvar2)))
      in
      ( sub @ [sub1]
      , []
      , [cons1; cons2] @ apply_sub [sub1] (rest_queue @ paused) )
  | ForallSkel (p, sk1) -> assert false


and skel_eq_step sub paused cons rest_queue sk1 sk2 =
  match (sk1, sk2) with
  (* ς = ς *)
  | SkelParam sp1, SkelParam sp2 when sp1 = sp2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ *)
  | SkelParam sp1, sk2a
    when not (List.mem sp1 (free_skeleton sk2a)) ->
      let sub1 = SkelParamToSkel (sp1, sk2a) in
      (sub @ [sub1], [], apply_sub [sub1] (rest_queue @ paused))
  (* τ₁ = ς₂ *)
  | sk2a, SkelParam sp1
    when not (List.mem sp1 (free_skeleton sk2a)) ->
      let sub1 = SkelParamToSkel (sp1, sk2a) in
      (sub @ [sub1], [], apply_sub [sub1] (rest_queue @ paused))
  (* int = int *)
  | PrimSkel ps1, PrimSkel ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | SkelArrow (ska, skb), SkelArrow (skc, skd) ->
      ( sub
      , paused
      , [Typed.SkelEq (ska, skc); Typed.SkelEq (skb, skd)] @ rest_queue )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | SkelHandler (ska, skb), SkelHandler (skc, skd) ->
      ( sub
      , paused
      , [Typed.SkelEq (ska, skc); Typed.SkelEq (skb, skd)] @ rest_queue )
  | _ -> assert false


and ty_omega_step sub paused cons rest_queue omega = function
  (* ω : A <= A *)
  | x, y when Types.types_are_equal x y ->
      let sub1 = CoerTyParamToTyCoercion (omega, Typed.ReflTy x) in
      (sub @ [sub1], paused, rest_queue)
  (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
  | Types.Arrow (a1, (aa1, d1)), Types.Arrow (a2, (aa2, d2)) ->
      let new_ty_coercion_var_coer, ty_cons = fresh_ty_coer (a2, a1)
      and dirty_coercion_c, ty2_cons, dirt_cons =
        fresh_dirty_coer ((aa1, d1), (aa2, d2))
      in
      let sub1 =
        CoerTyParamToTyCoercion
          ( omega
          , Typed.ArrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c) )
      in
      ( sub @ [sub1]
      , paused
      , List.append [ty_cons; ty2_cons; dirt_cons] rest_queue )
  (* ω : D₁ => C₁ <= D₂ => C₂ *)
  | Types.Handler (drty11, drty12), Types.Handler (drty21, drty22) ->
      let drty_coer1, cons1, cons2 = fresh_dirty_coer (drty21, drty11)
      and drty_coer2, cons3, cons4 = fresh_dirty_coer (drty12, drty22) in
      let sub1 =
        CoerTyParamToTyCoercion
          (omega, Typed.HandlerCoercion (drty_coer1, drty_coer2))
      in
      ( sub @ [sub1]
      , paused
      , List.append [cons1; cons2; cons3; cons4] rest_queue )
  (* ω : α <= A /  ω : A <= α *)
  | Types.TyParam tv, a
   |a, Types.TyParam tv ->
      (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
      let skel_tv = get_skel_of_tyvar tv (paused @ rest_queue) in
      let skel_a = skeleton_of_target_ty a (paused @ rest_queue) in
      if skel_tv = skel_a then (sub, cons :: paused, rest_queue)
      else (sub, cons :: paused, SkelEq (skel_tv, skel_a) :: rest_queue)
  | _ -> assert false


and dirt_omega_step sub paused cons rest_queue omega dcons =
  match dcons with
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | {effect_set= s1; row= ParamRow v1}, {effect_set= s2; row= ParamRow v2} ->
      if Types.EffectSet.is_empty s1 then (sub, cons :: paused, rest_queue)
      else
        let omega' = Params.DirtCoercion.fresh () in
        let diff_set = Types.EffectSet.diff s1 s2 in
        let union_set = Types.EffectSet.union s1 s2 in
        let sub' =
          [ DirtVarToDirt
              ( v2
              , let open Types in
                {effect_set= diff_set; row= ParamRow (Params.Dirt.fresh ())} )
          ; CoerDirtVartoDirtCoercion
              (omega, Typed.UnionDirt (s1, DirtCoercionVar omega')) ]
        in
        let new_cons =
          Typed.DirtOmega
            ( omega'
            , ( Types.{effect_set= Types.EffectSet.empty; row= ParamRow v1}
              , Types.{effect_set= union_set; row= ParamRow v2} ) )
        in
        (sub @ sub', [], apply_sub sub' (new_cons :: paused @ rest_queue))
  (* ω : Ø <= Δ₂ *)
  | {effect_set= s1; row= EmptyRow}, d
    when Types.EffectSet.is_empty s1 ->
      let sub1 = CoerDirtVartoDirtCoercion (omega, Typed.Empty d) in
      (sub @ [sub1], paused, rest_queue)
  (* ω : δ₁ <= Ø *)
  | {effect_set= s1; row= ParamRow v1}, {effect_set= s2; row= EmptyRow}
    when Types.EffectSet.is_empty s1 && Types.EffectSet.is_empty s2 ->
      let sub1 =
        [ CoerDirtVartoDirtCoercion (omega, Typed.Empty Types.empty_dirt)
        ; DirtVarToDirt (v1, Types.empty_dirt) ]
      in
      (sub @ sub1, [], apply_sub sub1 (paused @ rest_queue))
  (* ω : O₁ <= O₂ *)
  | {effect_set= s1; row= EmptyRow}, {effect_set= s2; row= EmptyRow} ->
      if Types.EffectSet.subset s1 s2 then
        let sub1 =
          CoerDirtVartoDirtCoercion
            ( omega
            , Typed.UnionDirt
                ( s2
                , Typed.Empty (Types.closed_dirt (Types.EffectSet.diff s2 s1))
                ) )
        in
        (sub @ [sub1], paused, rest_queue)
      else assert false
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | {effect_set= s1; row= EmptyRow}, {effect_set= s2; row= ParamRow v2} ->
      let v2' = Params.Dirt.fresh () in
      let sub1 =
        [ CoerDirtVartoDirtCoercion
            ( omega
            , Typed.UnionDirt
                ( s1
                , Typed.Empty
                    Types.{effect_set= EffectSet.diff s2 s1; row= ParamRow v2'}
                ) )
        ; DirtVarToDirt
            (v2, Types.{effect_set= EffectSet.diff s1 s2; row= ParamRow v2'})
        ]
      in
      (sub @ sub1, [], apply_sub sub1 (paused @ rest_queue))
  | _ -> (sub, cons :: paused, rest_queue)


let rec unify (sub, paused, queue) =
  Print.debug "=============Start loop============" ;
  Print.debug "-----Subs-----" ;
  print_s_list sub ;
  Print.debug "-----paused-----" ;
  print_c_list paused ;
  Print.debug "-----queue-----" ;
  print_c_list queue ;
  match queue with
  | [] ->
      Print.debug "=============FINAL LOOP Result============" ;
      (sub, paused)
  | cons :: rest_queue ->
      let new_state =
        match cons with
        (* α : τ *)
        | Typed.TyParamHasSkel (tvar, skel) ->
            ty_param_has_skel_step sub paused cons rest_queue tvar skel
        (* τ₁ = τ₂ *)
        | Typed.SkelEq (sk1, sk2) ->
            skel_eq_step sub paused cons rest_queue sk1 sk2
        (* ω : A <= B *)
        | Typed.TyOmega (omega, tycons) ->
            ty_omega_step sub paused cons rest_queue omega tycons
        (* ω : Δ₁ <= Δ₂ *)
        | Typed.DirtOmega (omega, dcons) ->
            dirt_omega_step sub paused cons rest_queue omega dcons
      in
      Print.debug "=========End loop============" ;
      unify new_state
