(** Syntax of the core language. *)

type e_ty = 
  | ETyvar of Params.ETy.t
  | Arrow of e_ty * e_ty
  | Tuple of e_ty list
  | Handler of e_ty * e_ty
  | PrimTy of prim_ty
  | TySchemeTy of Params.ETy.t  * e_ty

 and 
 prim_ty =
 | IntTy
 | BoolTy
 | StringTy
 | FloatTy

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type effect = OldUtils.effect * (Types.target_ty * Types.target_ty)

type 'term annotation = {
  term: 'term;
  location: Location.t;
}


type e_pattern = e_plain_pattern annotation
and e_plain_pattern =
  | PEVar of variable
  | PEAs of e_pattern * variable
  | PETuple of e_pattern list
  | PERecord of (OldUtils.field, e_pattern) OldUtils.assoc
  | PEVariant of OldUtils.label * e_pattern option
  | PEConst of Const.t
  | PENonbinding


let annotate t loc = {
  term = t;
  location = loc;
}

(** Pure expressions *)
type e_expression = e_plain_expression annotation
and e_plain_expression =
  | EVar of variable
  | EBuiltIn of string * int
  | EConst of Const.t
  | ETuple of e_expression list
  | ERecord of (OldUtils.field, e_expression) OldUtils.assoc
  | EVariant of OldUtils.label * e_expression option
  | ELambda of (e_pattern * Types.skeleton * e_computation)
  | EEffect of effect
  | EHandler of e_handler
  | EBigLambdaSkel of Params.Skel.t * e_expression
  | EApplySkelExp of e_expression * Types.skeleton

(** Impure computations *)
and e_computation = e_plain_computation annotation
and e_plain_computation =
  | EValue of e_expression
  | ELetVal of e_pattern * e_expression * e_computation 
  | EApply of e_expression * e_expression
  | EHandle of e_expression * e_computation
  | ECall of effect * e_expression * e_abstraction_with_ty
  | EBind of e_computation * e_abstraction


(** Handler definitions *)
and e_handler = {
  effect_clauses : (effect, e_abstraction2) OldUtils.assoc;
  value_clause : e_abstraction_with_ty;
}
(** Abstractions that take one argument. *)
and e_abstraction = (e_pattern * e_computation) annotation

and e_abstraction_with_ty = (e_pattern * Types.skeleton * e_computation) annotation

(** Abstractions that take two arguments. *)
and e_abstraction2 = (e_pattern * e_pattern * e_computation) annotation

let rec typed_to_erasure_ty sub typed_ty = 
  begin match typed_ty with
  | Types.Tyvar p -> 
      begin match OldUtils.lookup p sub with
      | Some x' -> x'
      | None -> assert false
    end
  | Types.Arrow (t1, (t2, drt)) -> 
      let t1' = typed_to_erasure_ty sub t1 in 
      let t2' = typed_to_erasure_ty sub t2 in 
      Types.SkelArrow (t1', t2')
  | Types.Tuple tys -> assert false
  | Types.Handler ((t1, drt1), (t2, drt2)) ->
      let t1' = typed_to_erasure_ty sub t1 in 
      let t2' = typed_to_erasure_ty sub t2 in 
      Types.SkelHandler (t1', t2')
  | Types.PrimTy p -> Types.PrimSkel p 
  | Types.QualTy (_,tty) -> typed_to_erasure_ty sub tty 
  | Types.QualDirt (_,tty) -> typed_to_erasure_ty sub tty 
  | Types.TySchemeTy (p,sk,tty) ->
      let sub' = (p,sk):: sub in 
      typed_to_erasure_ty sub' tty 
  | Types.TySchemeDirt (p,tty) -> typed_to_erasure_ty sub tty 
  | Types.TySchemeSkel (p,tty) -> Types.ForallSkel (p, (typed_to_erasure_ty sub tty))
  end


let rec typed_to_erasure_exp sub {Typed.term=exp; Typed.location=loc} = 
  let e' = typed_to_erasure_exp' sub exp in 
  annotate e' loc
and typed_to_erasure_exp' sub tt =
  begin match tt with 
  | Typed.Var v -> EVar v
  | Typed.BuiltIn (s,i) -> assert false
  | Typed.Const c -> EConst c
  | Typed.Tuple elist -> ETuple (List.map ( fun x -> typed_to_erasure_exp sub x ) elist)
  | Typed.Lambda (p,tty,co) -> 
      ELambda (typed_to_erasure_pattern p, typed_to_erasure_ty sub tty, typed_to_erasure_comp sub co)

  | Typed.Effect e -> EEffect e
  | Typed.Handler h -> 
      let (e_pat,tty,v_comp) = (h.value_clause).term in
      let op_c = h.effect_clauses in 
      let new_vc = typed_to_erasure_abs_with_ty sub (h.value_clause) in 
      let new_op_c =
          OldUtils.map (fun (eff, e_a2) -> 
                        let new_e_a2 = typed_to_erasure_abs_2 sub e_a2 in 
                        (eff, new_e_a2)) op_c in 
      let new_h = 
        {
          value_clause = new_vc;
          effect_clauses = new_op_c;
        } in 
      EHandler new_h
  | Typed.BigLambdaTy (tp,sk,e) -> 
      let sub1 = sub @ [(tp,sk)] in
      (typed_to_erasure_exp sub1 e).term 

  | BigLambdaDirt (_,e) -> typed_to_erasure_exp' sub e.term 
  | BigLambdaSkel (sk_p,e) -> EBigLambdaSkel (sk_p, typed_to_erasure_exp sub e)
  | CastExp (e,_) -> typed_to_erasure_exp' sub e.term 
  | ApplyTyExp (e,_) -> typed_to_erasure_exp' sub e.term 
  | LambdaTyCoerVar (_,_,e) -> typed_to_erasure_exp' sub e.term 
  | LambdaDirtCoerVar  (_,_,e) -> typed_to_erasure_exp' sub e.term 
  | ApplyDirtExp (e,_) -> typed_to_erasure_exp' sub e.term 
  | ApplySkelExp (e,s) -> EApplySkelExp (typed_to_erasure_exp sub e, s) 
  | ApplyTyCoercion (e,_) -> typed_to_erasure_exp' sub e.term
  | ApplyDirtCoercion (e,_) -> typed_to_erasure_exp' sub e.term
  
  end


and typed_to_erasure_comp sub {Typed.term=comp; Typed.location=loc} = 
  let c' = typed_to_erasure_comp' sub comp in 
  annotate c' loc
and typed_to_erasure_comp' sub tt =
  begin match tt with 
  | Typed.Value e -> EValue (typed_to_erasure_exp sub e)
  | Typed.LetVal (e,(p,_ty,c)) -> 
      let p' = typed_to_erasure_pattern p in
      let e' = typed_to_erasure_exp sub e in 
      let c' = typed_to_erasure_comp sub c in 
      ELetVal (p',e',c')
  | Typed.Apply (e1,e2) -> 
      let e1' = typed_to_erasure_exp sub e1 in 
      let e2' = typed_to_erasure_exp sub e2 in 
      EApply (e1', e2')
  | Typed.Handle (e,c) ->
      let e' = typed_to_erasure_exp sub e in 
      let c' = typed_to_erasure_comp sub c in
      EHandle(e' ,c')
  | Typed.Call (eff, e, abs) ->
      let e' = typed_to_erasure_exp sub e in 
      let abs' = typed_to_erasure_abs_with_ty sub abs in 
      ECall(eff, e', abs')
  | Typed.Bind (c,a) ->
      let c' = typed_to_erasure_comp sub c in 
      let a' = typed_to_erasure_abs sub a in 
      EBind (c',a')
  | Typed.CastComp (c,_) -> typed_to_erasure_comp' sub (c.term) 
  | Typed.CastComp_ty (c,_) -> typed_to_erasure_comp' sub (c.term) 
  | Typed.CastComp_dirt (c,_) -> typed_to_erasure_comp' sub (c.term) 
  end


and typed_to_erasure_abs_with_ty sub abs_w_ty =
    let (e_p,e_ty,e_c) = abs_w_ty.term in 
    annotate (typed_to_erasure_pattern e_p, typed_to_erasure_ty sub e_ty, typed_to_erasure_comp sub e_c) e_c.location
and typed_to_erasure_abs sub abs =
    let (e_p,e_c) = abs.term in 
    annotate (typed_to_erasure_pattern e_p, typed_to_erasure_comp sub e_c) e_c.location
and typed_to_erasure_abs_2 sub abs = 
    let (e_p1,e_p2,e_c) = abs.Typed.term in 
    annotate (typed_to_erasure_pattern e_p1, typed_to_erasure_pattern e_p2, typed_to_erasure_comp sub e_c) e_c.location
and typed_to_erasure_pattern p = 
  let loc = p.Typed.location in
  let pat =  match p.Typed.term with
    | Typed.PVar x -> PEVar x
    | Typed.PAs (p, x) -> PEAs (typed_to_erasure_pattern p, x)
    | Typed.PNonbinding -> PENonbinding
    | Typed.PConst const -> PEConst const
  in
  annotate pat loc
