open Types
open Typed
module STyParams = Set.Make (Params.Ty)

let set_of_list =
  List.fold_left (fun acc x -> STyParams.add x acc) STyParams.empty

type substitutions = 
  { type_param_to_type_coercions: (Params.TyCoercion.t, Typed.ty_coercion) Assoc.t
  ; type_param_to_type: (Params.Ty.t, Types.target_ty) Assoc.t
  ; dirt_var_to_dirt_coercions: (Params.DirtCoercion.t, Typed.dirt_coercion) Assoc.t
  ; dirt_var_to_dirt: (Params.Dirt.t, Types.dirt) Assoc.t
  ; skel_param_to_skel: (Params.Skel.t, Types.skeleton) Assoc.t
  }

(*type substitution =
  | CoerTyParamToTyCoercion of (Params.TyCoercion.t * Typed.ty_coercion)
  | CoerDirtVartoDirtCoercion of (Params.DirtCoercion.t * Typed.dirt_coercion)
  | TyParamToTy of (Params.Ty.t * Types.target_ty)
  | DirtVarToDirt of (Params.Dirt.t * Types.dirt)
  | SkelParamToSkel of (Params.Skel.t * Types.skeleton)
*)
let subsEmpty = 
  { type_param_to_type_coercions= Assoc.empty
  ; dirt_var_to_dirt_coercions= Assoc.empty
  ; type_param_to_type= Assoc.empty
  ; dirt_var_to_dirt= Assoc.empty
  ; skel_param_to_skel= Assoc.empty
  }

let a_to_e f a b = 
  f a b subsEmpty

let add_param_coercion param t_coercion subs = 
  {subs with type_param_to_type_coercions= Assoc.update param t_coercion subs.type_param_to_type_coercions}

let add_param_coercion_e = a_to_e add_param_coercion

let add_type_sub param target_ty subs = 
  {subs with type_param_to_type= Assoc.update param target_ty subs.type_param_to_type}

let add_type_sub_e = a_to_e add_type_sub

let add_var_coercion var d_coercion subs = 
  {subs with dirt_var_to_dirt_coercions= Assoc.update var d_coercion subs.dirt_var_to_dirt_coercions}

let add_var_coercion_e = a_to_e add_var_coercion

let add_var_dirt_sub param t_coercion subs = 
  {subs with dirt_var_to_dirt= Assoc.update param t_coercion subs.dirt_var_to_dirt}

let add_var_dirt_sub_e = a_to_e add_var_dirt_sub

let add_skel_sub param t_coercion subs = 
  {subs with skel_param_to_skel= Assoc.update param t_coercion subs.skel_param_to_skel}

let add_skel_sub_e = a_to_e add_skel_sub

let merge_subs sub1 sub2 = 
  { type_param_to_type_coercions= Assoc.concat sub1.type_param_to_type_coercions sub2.type_param_to_type_coercions
  ; type_param_to_type= Assoc.concat sub1.type_param_to_type sub2.type_param_to_type
  ; dirt_var_to_dirt_coercions= Assoc.concat sub1.dirt_var_to_dirt_coercions sub2.dirt_var_to_dirt_coercions
  ; dirt_var_to_dirt= Assoc.concat sub1.dirt_var_to_dirt sub2.dirt_var_to_dirt
  ; skel_param_to_skel= Assoc.concat sub1.skel_param_to_skel sub2.skel_param_to_skel
  }

let printy ?at_level ppf = Print.print ?at_level ppf

let print_type_coercion p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-coertyTotyCoer-> %t"
    (Params.TyCoercion.print p)
    (Typed.print_ty_coercion t)

let print_type_param_to_type p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-tyvarToTargetty-> %t" 
    (Params.Ty.print p)
    (Types.print_target_ty t)

let print_dirt_var_sub p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-dirtvarToTargetdirt-> %t" (Params.Dirt.print p)
        (Types.print_target_dirt t)

let print_dirt_var_coercion p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-coertyDirtoDirtCoer-> %t"
    (Params.DirtCoercion.print p)
    (Typed.print_dirt_coercion t)

let print_skel_param_sub p t ppf =
  Print.print ppf "substitution: ";
  printy ppf "%t :-skelvarToSkeleton-> %t" (Params.Skel.print p)
        (Types.print_skeleton t)

let print_subs ?max_level (subs: substitutions)= 
  List.map (fun (x,y) -> (Print.debug "%t" (print_type_coercion x y))) (Assoc.to_list subs.type_param_to_type_coercions);
  List.map (fun (x,y) -> (Print.debug "%t" (print_type_param_to_type x y))) (Assoc.to_list subs.type_param_to_type);
  List.map (fun (x,y) -> (Print.debug "%t" (print_dirt_var_sub x y))) (Assoc.to_list subs.dirt_var_to_dirt);
  List.map (fun (x,y) -> (Print.debug "%t" (print_dirt_var_coercion x y))) (Assoc.to_list subs.dirt_var_to_dirt_coercions);
  List.map (fun (x,y) -> (Print.debug "%t" (print_skel_param_sub x y))) (Assoc.to_list subs.skel_param_to_skel)

let print_s_list subs = 
  print_subs subs

let rec apply_sub_dirt sub drt =
  match drt.row with
  | ParamRow p -> (
    match Assoc.lookup p sub.dirt_var_to_dirt with
    | Some drt2 ->
        apply_sub_dirt sub (Types.add_effects drt.effect_set drt2)
    | None -> drt )
  | EmptyRow -> drt


let rec apply_sub_skel sub sk =
  match sk with
  | SkelParam p -> (
    match Assoc.lookup p sub.skel_param_to_skel with 
      | Some sk1 -> apply_sub_skel sub sk1
      | None -> sk
  )
  | PrimSkel _ -> sk
  | SkelArrow (sk1, sk2) ->
      SkelArrow (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | SkelHandler (sk1, sk2) ->
      SkelHandler (apply_sub_skel sub sk1, apply_sub_skel sub sk2)
  | ForallSkel (p, sk1) -> ForallSkel (p, apply_sub_skel sub sk1)
  (* Really consider other cases *)
  | SkelApply (t,l) -> SkelApply (t, List.map (apply_sub_skel sub) l)

let rec apply_sub_ty (sub: substitutions) ty =
  match ty with
  | TyParam typ1 -> (
    match Assoc.lookup typ1 sub.type_param_to_type with
        | Some ttype -> apply_sub_ty sub ttype (* We don't assume that substitutions are fully expanded *)
        | None -> ty )
  | Arrow (tty1, tty2) ->
      Arrow (apply_sub_ty sub tty1, apply_sub_dirty_ty sub tty2)
  | Apply (ty_name, tys) -> Apply (ty_name, List.map (apply_sub_ty sub) tys)
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
    match Assoc.lookup p sub.type_param_to_type_coercions with
      | Some t_coer -> apply_sub_tycoer sub t_coer
      | None -> TyCoercionVar p
  )
  | SequenceTyCoer (ty_coer1, ty_coer2) ->
      SequenceTyCoer
        (apply_sub_tycoer sub ty_coer1, apply_sub_tycoer sub ty_coer2)
  | TupleCoercion tcl ->
      TupleCoercion (List.map (fun x -> apply_sub_tycoer sub x) tcl)
  | ApplyCoercion (ty_name, tcl) ->
      ApplyCoercion (ty_name, List.map (fun x -> apply_sub_tycoer sub x) tcl)
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
    match Assoc.lookup p sub.dirt_var_to_dirt_coercions with
    | Some dc -> apply_sub_dirtcoer sub dc
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
  match c with
  | Value e -> Value (apply_sub_exp sub e)
  | LetVal (e1, abs) ->
      LetVal (apply_sub_exp sub e1, apply_sub_abs_with_ty sub abs)
  | LetRec ([(var, ty, e1)], c1) ->
      LetRec
        ( [(var, apply_sub_ty sub ty, apply_sub_exp sub e1)]
        , apply_sub_comp sub c1 )
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


and apply_sub_exp sub e =
  match e with
  | Var v -> Var v
  | BuiltIn (s, i) -> BuiltIn (s, i)
  | Const c -> Const c
  | Tuple elist -> Tuple (List.map (fun x -> apply_sub_exp sub x) elist)
  | Variant (lbl, e1) -> Variant (lbl, apply_sub_exp sub e1)
  | Lambda abs -> Lambda (apply_sub_abs_with_ty sub abs)
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


and apply_sub_abs sub (p, c) = (p, apply_sub_comp sub c)

and apply_sub_abs_with_ty sub (p, t, c) =
  (p, apply_sub_ty sub t, apply_sub_comp sub c)


and apply_sub_abs2 sub (p1, p2, c) = (p1, p2, apply_sub_comp sub c)

and apply_sub_handler sub h =
  let eff_clauses = h.effect_clauses in
  let new_value_clause = apply_sub_abs_with_ty sub h.value_clause in
  let new_eff_clauses =
    Assoc.map (fun abs2 -> apply_sub_abs2 sub abs2) eff_clauses
  in
  {effect_clauses= new_eff_clauses; value_clause= new_value_clause}


let rec apply_substitution = apply_sub_comp

and apply_substitution_exp = apply_sub_exp

and apply_substitution_ty = apply_sub_ty

and apply_substitution_dirt = apply_sub_dirt

and apply_substitution_skel = apply_sub_skel

let rec apply_sub1 subs cons =
  match cons with
  | Typed.TyOmega (coer_p, (ty1, ty2)) -> (
      Typed.TyOmega (coer_p, (apply_sub_ty subs ty1, apply_sub_ty subs ty2))
  )
  | Typed.DirtOmega (coer_p, (drt1, drt2)) -> (
    Typed.DirtOmega (coer_p, (apply_sub_dirt subs drt1, apply_sub_dirt subs drt2))
  )
  | Typed.TyParamHasSkel (tv, sp) -> (
    Typed.TyParamHasSkel (tv, (apply_sub_skel subs sp))
  )
  | _ -> cons

let apply_sub subs c_list = List.map (apply_sub1 subs) c_list

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
  | Apply (ty_name, tys) ->
      SkelApply
        (ty_name, List.map (fun ty -> skeleton_of_target_ty ty conslist) tys)
  | Tuple tup ->
      SkelTuple (List.map (fun ty -> skeleton_of_target_ty ty conslist) tup)
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


let ty_param_has_skel_step sub paused cons rest_queue tvar skel =
  match skel with
  (* α : ς *)
  | SkelParam p -> (sub, Typed.add_to_constraints cons paused, rest_queue)
  (* α : int *)
  | PrimSkel ps ->
      let k = tvar in
      let v = Types.PrimTy ps in
      let sub1 = add_type_sub_e k v in
      (add_type_sub tvar (Types.PrimTy ps) sub, [], apply_sub sub1 (Typed.add_list_to_constraints paused rest_queue))
  (* α : τ₁ -> τ₂ *)
  | SkelArrow (sk1, sk2) ->
      let tvar1, cons1 = Typed.fresh_ty_with_skel sk1
      and tvar2, cons2 = Typed.fresh_ty_with_skel sk2
      and dvar1 = Types.fresh_dirt () in
      let k = tvar in
      let v = Types.Arrow (tvar1, (tvar2, dvar1)) in
      let sub1 = add_type_sub_e k v in
      ( add_type_sub k v sub 
      , []
      , Typed.add_to_constraints cons1 (apply_sub sub1 (Typed.add_list_to_constraints paused rest_queue)) |> Typed.add_to_constraints cons2)
  (* α : τ₁ x τ₂ ... *)
  | SkelTuple sks ->
      let tvars, conss =
        List.fold_right
          (fun sk (tvars, conss) ->
            let tvar, cons = Typed.fresh_ty_with_skel sk in
            (tvar :: tvars, cons :: conss) )
          sks ([], [])
      in
      let k = tvar in
      let v = Types.Tuple tvars in
      let sub1 = add_type_sub_e k v in
      (add_type_sub k v sub, [], 
      add_list_to_constraints (apply_sub sub1 (add_list_to_constraints paused rest_queue) ) conss )
  (* α : ty_name (τ₁, τ₂, ...) *)
  | SkelApply (ty_name, sks) ->
      let tvars, conss =
        List.fold_right
          (fun sk (tvars, conss) ->
            let tvar, cons = Typed.fresh_ty_with_skel sk in
            (tvar :: tvars, cons :: conss) )
          sks ([], [])
      in
      let k = tvar in
      let v = Types.Apply (ty_name, tvars) in
      let sub1 = add_type_sub_e k v in
      (add_type_sub k v sub, [], add_list_to_constraints (apply_sub sub1 (add_list_to_constraints paused rest_queue) ) conss)
  (* α : τ₁ => τ₂ *)
  | SkelHandler (sk1, sk2) ->
      let tvar1, cons1 = Typed.fresh_ty_with_skel sk1
      and tvar2, cons2 = Typed.fresh_ty_with_skel sk2
      and dvar1 = Types.fresh_dirt ()
      and dvar2 = Types.fresh_dirt () in
      let k = tvar in
      let v = Types.Handler ((tvar1, dvar1), (tvar2, dvar2)) in
      let sub1 = add_type_sub_e k v
      in
      ( add_type_sub k v sub
      , []
      , Typed.add_to_constraints cons1 (apply_sub sub1 (Typed.add_list_to_constraints paused rest_queue)) |> Typed.add_to_constraints cons2 )
  | ForallSkel (p, sk1) -> failwith __LOC__


and skel_eq_step sub paused cons rest_queue sk1 sk2 =
  match (sk1, sk2) with
  (* ς = ς *)
  | SkelParam sp1, SkelParam sp2 when sp1 = sp2 -> (sub, paused, rest_queue)
  (* ς₁ = τ₂ / τ₁ = ς₂ *)
  | SkelParam sp1, sk2a
   |sk2a, SkelParam sp1
    when not (List.mem sp1 (free_skeleton sk2a)) ->
      let k = sp1 in
      let v = sk2a in
      let sub1 = add_skel_sub_e k v in
      (add_skel_sub k v sub, [], apply_sub sub1 (add_list_to_constraints paused rest_queue)  )
  (* int = int *)
  | PrimSkel ps1, PrimSkel ps2 when ps1 = ps2 -> (sub, paused, rest_queue)
  (* τ₁₁ -> τ₁₂ = τ₂₁ -> τ₂₂ *)
  | SkelArrow (ska, skb), SkelArrow (skc, skd) ->
      ( sub
      , paused
      , add_list_to_constraints [Typed.SkelEq (ska, skc); Typed.SkelEq (skb, skd)] rest_queue )
  (* τ₁₁ => τ₁₂ = τ₂₁ => τ₂₂ *)
  | SkelHandler (ska, skb), SkelHandler (skc, skd) ->
      ( sub
      , paused
      , add_list_to_constraints [Typed.SkelEq (ska, skc); Typed.SkelEq (skb, skd)] rest_queue )
  | SkelApply (ty_name1, sks1), SkelApply (ty_name2, sks2)
    when ty_name1 = ty_name2 && List.length sks1 = List.length sks2 ->
      ( sub
      , paused
      , add_list_to_constraints (List.map2 (fun sk1 sk2 -> Typed.SkelEq (sk1, sk2)) sks1 sks2)
        rest_queue )
  | _ -> failwith __LOC__


and ty_omega_step sub paused cons rest_queue omega =
  let loc = Location.unknown in
  function
    (* ω : A <= A *)
    | x, y when Types.types_are_equal x y ->
        let k = omega in
        let v = Typed.ReflTy x in
        (add_param_coercion k v sub, paused, rest_queue)
    (* ω : A₁ -> C₁ <= A₂ -> C₂ *)
    | Types.Arrow (a1, dirty1), Types.Arrow (a2, dirty2) ->
        let new_ty_coercion_var_coer, ty_cons = fresh_ty_coer (a2, a1)
        and dirty_coercion_c, dirty_cons = fresh_dirty_coer (dirty1, dirty2) in
        let k = omega in
        let v =  Typed.ArrowCoercion (new_ty_coercion_var_coer, dirty_coercion_c)
        in
        (add_param_coercion k v sub, paused, add_to_constraints ty_cons rest_queue |> add_to_constraints dirty_cons)
    (* ω : A₁ x A₂ x ... <= B₁ x B₂ x ...  *)
    | Types.Tuple tys, Types.Tuple tys'
      when List.length tys = List.length tys' ->
        let coercions, conss =
          List.fold_right2
            (fun ty ty' (coercions, conss) ->
              let coercion, ty_cons = fresh_ty_coer (ty, ty') in
              (coercion :: coercions, ty_cons :: conss) )
            tys tys' ([], [])
        in
        let k = omega in
        let v = Typed.TupleCoercion coercions 
        in
        (add_param_coercion k v sub, paused, add_list_to_constraints conss rest_queue)
    (* ω : ty (A₁,  A₂,  ...) <= ty (B₁,  B₂,  ...) *)
    (* we assume that all type parameters are positive *)
    | Types.Apply (ty_name1, tys1), Types.Apply (ty_name2, tys2)
      when ty_name1 = ty_name2 && List.length tys1 = List.length tys2 ->
        let coercions, conss =
          List.fold_right2
            (fun ty ty' (coercions, conss) ->
              let coercion, ty_cons = fresh_ty_coer (ty, ty') in
              (coercion :: coercions, ty_cons :: conss) )
            tys1 tys2 ([], [])
        in
        let k = omega in
        let v = Typed.ApplyCoercion (ty_name1, coercions) 
        in
        (add_param_coercion k v sub, paused, add_list_to_constraints conss rest_queue)
    (* ω : D₁ => C₁ <= D₂ => C₂ *)
    | Types.Handler (drty11, drty12), Types.Handler (drty21, drty22) ->
        let drty_coer1, drty_cons1 = fresh_dirty_coer (drty21, drty11)
        and drty_coer2, drty_cons2 = fresh_dirty_coer (drty12, drty22) in
        let k = omega in
        let v = Typed.HandlerCoercion (drty_coer1, drty_coer2)
        in
        (add_param_coercion k v sub, paused, add_to_constraints drty_cons1 rest_queue |> add_to_constraints drty_cons2)
    (* ω : α <= A /  ω : A <= α *)
    | Types.TyParam tv, a
     |a, Types.TyParam tv ->
        (*unify_ty_vars (sub,paused,rest_queue) tv a cons*)
        let skel_tv = get_skel_of_tyvar tv (paused @ rest_queue) in
        let skel_a = skeleton_of_target_ty a (paused @ rest_queue) in
        if skel_tv = skel_a then (sub, cons :: paused, rest_queue)
        else (sub, add_to_constraints cons paused, add_to_constraints (SkelEq (skel_tv, skel_a)) rest_queue)
    | a, b ->
        Print.debug "can't solve subtyping for types: %t and %t"
          (print_target_ty a) (print_target_ty b) ;
        assert false


and dirt_omega_step sub paused cons rest_queue omega dcons =
  match dcons with
  (* ω : O₁ ∪ δ₁ <= O₂ ∪ δ₂ *)
  | {effect_set= s1; row= ParamRow v1}, {effect_set= s2; row= ParamRow v2} ->
      if Types.EffectSet.is_empty s1 then (sub, cons :: paused, rest_queue)
      else
        let omega' = Params.DirtCoercion.fresh () in
        let diff_set = Types.EffectSet.diff s1 s2 in
        let union_set = Types.EffectSet.union s1 s2 in
        let k0 = v2 in
        let v0 = let open Types in
                {effect_set= diff_set; row= ParamRow (Params.Dirt.fresh ())} in
        let k1' = omega in
        let v1' = Typed.UnionDirt (s1, DirtCoercionVar omega') in
        let sub' = add_var_dirt_sub_e k0 v0 |> add_var_coercion k1' v1'
        in
        let new_cons =
          Typed.DirtOmega
            ( omega'
            , ( Types.{effect_set= Types.EffectSet.empty; row= ParamRow v1}
              , Types.{effect_set= union_set; row= ParamRow v2} ) )
        in
        (merge_subs sub sub', [], apply_sub sub' (add_list_to_constraints paused rest_queue |> add_to_constraints new_cons))
  (* ω : Ø <= Δ₂ *)
  | {effect_set= s1; row= EmptyRow}, d
    when Types.EffectSet.is_empty s1 ->
      let k = omega in
      let v = Typed.Empty d in
      (add_var_coercion k v sub, paused, rest_queue)
  (* ω : δ₁ <= Ø *)
  | {effect_set= s1; row= ParamRow v1}, {effect_set= s2; row= EmptyRow}
    when Types.EffectSet.is_empty s1 && Types.EffectSet.is_empty s2 ->
      let k0 = omega in
      let v0 = Typed.Empty Types.empty_dirt in
      let k1' = v1 in
      let v1' = Types.empty_dirt in
      let sub1 = add_var_coercion_e k0 v0 |> add_var_dirt_sub k1' v1'
      in
      (merge_subs sub sub1, [], apply_sub sub1 (add_list_to_constraints paused rest_queue))
  (* ω : O₁ <= O₂ *)
  | {effect_set= s1; row= EmptyRow}, {effect_set= s2; row= EmptyRow} ->
      assert (Types.EffectSet.subset s1 s2) ;
      let k = omega in
      let v = Typed.UnionDirt
              (s2, Typed.Empty (Types.closed_dirt (Types.EffectSet.diff s2 s1)))
      in
      (add_var_coercion k v sub, paused, rest_queue)
  (* ω : O₁ <= O₂ ∪ δ₂ *)
  | {effect_set= s1; row= EmptyRow}, {effect_set= s2; row= ParamRow v2} ->
      let v2' = Params.Dirt.fresh () in
      let k0 = omega in 
      let v0 = Typed.UnionDirt
                ( s1
                , Typed.Empty
                    Types.{effect_set= EffectSet.diff s2 s1; row= ParamRow v2'}
                )  in
      let k1 = v2 in 
      let v1 = Types.{effect_set= EffectSet.diff s1 s2; row= ParamRow v2'} in
      let sub1 = add_var_coercion_e k0 v0 |> add_var_dirt_sub k1 v1
      in
      (merge_subs sub sub1, [], apply_sub sub1 (add_list_to_constraints paused rest_queue))
  | _ -> (sub, cons :: paused, rest_queue)


let dirty_omega_step sub paused cons rest_queue (omega1, omega2) drtycons =
  let (ty1, drt1), (ty2, drt2) = drtycons in
  let ty_cons = TyOmega (omega1, (ty1, ty2))
  and dirt_cons = DirtOmega (omega2, (drt1, drt2)) in
  let sub', paused', rest_queue' =
    ty_omega_step sub paused ty_cons rest_queue omega1 (ty1, ty2)
  in
  dirt_omega_step sub' paused' dirt_cons rest_queue' omega2 (drt1, drt2)


let rec unify ((sub: substitutions), paused, queue) =
  Print.debug "=============Start loop============" ;
  Print.debug "-----Subs-----" ;
  print_s_list sub;
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
        (* ω : A ! Δ₁ <= B ! Δ₂ *)
        | Typed.DirtyOmega (omega, drtycons) ->
            dirty_omega_step sub paused cons rest_queue omega drtycons
      in
      Print.debug "=========End loop============" ;
      unify new_state


let rec apply_sub_to_type ty_subs dirt_subs ty =
  match ty with
  | Types.TyParam p -> (
    match Assoc.lookup p ty_subs with
    | Some p' -> Types.TyParam p'
    | None -> ty )
  | Types.Arrow (a, (b, d)) ->
      Types.Arrow
        ( apply_sub_to_type ty_subs dirt_subs a
        , (apply_sub_to_type ty_subs dirt_subs b, apply_sub_to_dirt dirt_subs d)
        )
  | Types.Tuple ty_list ->
      Types.Tuple
        (List.map (fun x -> apply_sub_to_type ty_subs dirt_subs x) ty_list)
  | Types.Handler ((a, b), (c, d)) ->
      Types.Handler
        ( (apply_sub_to_type ty_subs dirt_subs a, apply_sub_to_dirt dirt_subs b)
        , (apply_sub_to_type ty_subs dirt_subs c, apply_sub_to_dirt dirt_subs d)
        )
  | Types.PrimTy _ -> ty
  | Types.Apply (ty_name, tys) ->
      Types.Apply (ty_name, List.map (apply_sub_to_type ty_subs dirt_subs) tys)
  | _ -> failwith __LOC__

and apply_sub_to_dirt dirt_subs drt =
  match drt.row with
  | Types.ParamRow p -> (
    match Assoc.lookup p dirt_subs with
    | Some p' -> {drt with row= Types.ParamRow p'}
    | None -> drt )
  | Types.EmptyRow -> drt
