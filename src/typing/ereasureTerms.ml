(** Syntax of the core language. *)

open EreasureTypes

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
  | Effect of effect
  | EHandler of e_handler
  | EBigLambdaTy of Params.skel_param * e_expression
  | ApplyTyExp of e_expression * EreasureTypes.e_ty

(** Impure computations *)
and e_computation = e_plain_computation annotation
and e_plain_computation =
  | EValue of e_expression
  | ELetVal of variable * e_expression * e_computation 
  | EApply of e_expression * e_expression
  | EHandle of e_expression * e_computation
  | ECall of effect * e_expression * e_abstraction
  | EBind of e_computation * e_abstraction


(** Handler definitions *)
and e_handler = {
  e_effect_clauses : (effect, e_abstraction2) OldUtils.assoc;
  e_value_clause : e_abstraction;
}

(** Abstractions that take one argument. *)
and e_abstraction = (e_pattern * Types.skeleton * e_computation) annotation

(** Abstractions that take two arguments. *)
and e_abstraction2 = (e_pattern * e_pattern * e_computation) annotation




let rec typed_to_ereasure_ty sub typed_ty = 
  begin match typed_ty with
  | Types.Tyvar p -> 
      begin match OldUtils.lookup p sub with
      | Some x' -> x'
      | None -> assert false
    end
  | Types.Arrow (t1, (t2, drt)) -> 
      let t1' = typed_to_ereasure_ty sub t1 in 
      let t2' = typed_to_ereasure_ty sub t2 in 
      Types.SkelArrow (t1', t2')
  | Types.Tuple tys -> assert false
  | Types.Handler ((t1, drt1), (t2, drt2)) ->
      let t1' = typed_to_ereasure_ty sub t1 in 
      let t2' = typed_to_ereasure_ty sub t2 in 
      Types.SkelHandler (t1', t2')
  | Types.PrimTy p -> Types.PrimSkel p 
  | Types.QualTy (_,tty) -> typed_to_ereasure_ty sub tty 
  | Types.QualDirt (_,tty) -> typed_to_ereasure_ty sub tty 
  | Types.TySchemeTy (p,sk,tty) ->
      let sub' = (p,sk):: sub in 
      typed_to_ereasure_ty sub' tty 
  | Types.TySchemeDirt (p,tty) -> typed_to_ereasure_ty sub tty 
  | Types.TySchemeSkel (p,tty) -> Types.ForallSkel (p, (typed_to_ereasure_ty sub tty))
  end


and typed_to_ereasure_exp sub {Typed.term=exp; Typed.location=loc} = 
  let e' = typed_to_ereasure_exp' sub exp in 
  annotate e' loc
and typed_to_ereasure_exp' sub tt =
  begin match tt with 
  | Typed.Var v -> EVar v
  | Typed.BuiltIn (s,i) -> assert false
  | Typed.Const c -> EConst c
  | Typed.Tuple elist -> ETuple (List.map ( fun x -> typed_to_ereasure_exp sub x ) elist)
  | Lambda (p,tty,co) -> assert false

  | Effect e -> assert false
  | Handler h -> assert false
  | Typed.BigLambdaTy (tp,sk,e) -> 
      let sub1 = sub @ [(tp,sk)] in
      (typed_to_ereasure_exp sub1 e).term 

(*   | BigLambdaDirt of Params.dirt_param * expression  
  | BigLambdaSkel of Params.skel_param * expression
  | CastExp of expression * ty_coercion
  | ApplyTyExp of expression * Types.target_ty
  | LambdaTyCoerVar of Params.ty_coercion_param * Types.ct_ty * expression 
  | LambdaDirtCoerVar of Params.dirt_coercion_param * Types.ct_dirt * expression 
  | ApplyDirtExp of expression * Types.dirt
  | ApplySkelExp of expression * Types.skeleton
  | ApplyTyCoercion of expression * ty_coercion
  | ApplyDirtCoercion of expression * dirt_coercion *)
  
  end


and typed_to_ereasure_comp sub {Typed.term=comp; Typed.location=loc} = 
  let c' = typed_to_ereasure_comp' sub comp in 
  annotate c' loc
and typed_to_ereasure_comp' sub tt =
  begin match tt with 
  | Typed.Value e -> EValue (typed_to_ereasure_exp sub e)
  | Typed.LetVal (v,e,c) -> 
      let e' = typed_to_ereasure_exp sub e in 
      let c' = typed_to_ereasure_comp sub c in 
      ELetVal (v,e',c')
  | Typed.Apply (e1,e2) -> 
      let e1' = typed_to_ereasure_exp sub e1 in 
      let e2' = typed_to_ereasure_exp sub e2 in 
      EApply (e1', e2')
  | Typed.Handle (e,c) ->
      let e' = typed_to_ereasure_exp sub e in 
      let c' = typed_to_ereasure_comp sub c in
      EHandle(e' ,c')
  | Typed.Call (eff, e, abs) ->
      let e' = typed_to_ereasure_exp sub e in 
      let abs' = typed_to_ereasure_abs_with_ty sub abs in 
      ECall(eff, e', abs')
  | Typed.Bind (c,a) ->
      let c' = typed_to_ereasure_comp sub c in 
      let a' = typed_to_ereasure_abs sub a in 
      EBind (c',a')
  | Typed.CastComp (c,_) -> typed_to_ereasure_comp' sub (c.term) 
  | Typed.CastComp_ty (c,_) -> typed_to_ereasure_comp' sub (c.term) 
  | Typed.CastComp_dirt (c,_) -> typed_to_ereasure_comp' sub (c.term) 
  end


and typed_to_ereasure_abs_with_ty = assert false
and typed_to_ereasure_abs = assert false

