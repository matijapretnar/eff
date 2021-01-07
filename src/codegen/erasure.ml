(** Syntax of the core language. *)

module Variable = Symbol.Make (Symbol.String)
module EffectMap = Map.Make (String)

type variable = Variable.t

type effect = CoreTypes.Effect.t * (Types.target_ty * Types.target_ty)

type e_pattern =
  | PEVar of variable
  | PEAs of e_pattern * variable
  | PETuple of e_pattern list
  | PERecord of (CoreTypes.field, e_pattern) Assoc.t
  | PEVariant of CoreTypes.label * e_pattern option
  | PEConst of Const.t
  | PENonbinding

(** Pure expressions *)
type e_expression =
  | EVar of variable
  | EBuiltIn of string * int
  | EConst of Const.t
  | ETuple of e_expression list
  | ERecord of (CoreTypes.field, e_expression) Assoc.t
  | EVariant of CoreTypes.label * e_expression option
  | ELambda of e_abstraction_with_ty
  | EEffect of effect
  | EHandler of e_handler
  | EBigLambdaSkel of CoreTypes.SkelParam.t * e_expression
  | EApplySkelExp of e_expression * Types.skeleton

(** Impure computations *)
and e_computation =
  | EValue of e_expression
  | ELetVal of e_pattern * e_expression * e_computation
  | EApply of e_expression * e_expression
  | EHandle of e_expression * e_computation
  | ECall of effect * e_expression * e_abstraction_with_ty
  | EBind of e_computation * e_abstraction
  | EMatch of e_expression * e_abstraction list
  | ELetRec of (variable * Types.skeleton * e_expression) list * e_computation

and e_handler = {
  effect_clauses : (effect, e_abstraction2) Assoc.t;
  value_clause : e_abstraction_with_ty;
}
(** Handler definitions *)

and e_abstraction = e_pattern * e_computation
(** Abstractions that take one argument. *)

and e_abstraction_with_ty = e_pattern * Types.skeleton * e_computation

and e_abstraction2 = e_pattern * e_pattern * e_computation
(** Abstractions that take two arguments. *)

let rec typed_to_erasure_ty sub typed_ty =
  match typed_ty with
  | Types.TyParam p -> (
      match Assoc.lookup p sub with Some x' -> x' | None -> assert false)
  | Types.Arrow (t1, (t2, drt)) ->
      let t1' = typed_to_erasure_ty sub t1 in
      let t2' = typed_to_erasure_ty sub t2 in
      Types.SkelArrow (t1', t2')
  | Types.Tuple tys -> Types.SkelTuple (List.map (typed_to_erasure_ty sub) tys)
  | Types.Handler ((t1, drt1), (t2, drt2)) ->
      let t1' = typed_to_erasure_ty sub t1 in
      let t2' = typed_to_erasure_ty sub t2 in
      Types.SkelHandler (t1', t2')
  | Types.PrimTy p -> Types.PrimSkel p
  | Types.QualTy (_, tty) -> typed_to_erasure_ty sub tty
  | Types.QualDirt (_, tty) -> typed_to_erasure_ty sub tty
  | Types.TySchemeTy (p, sk, tty) ->
      let sub' = Assoc.update p sk sub in
      typed_to_erasure_ty sub' tty
  | Types.TySchemeDirt (p, tty) -> typed_to_erasure_ty sub tty
  | Types.TySchemeSkel (p, tty) ->
      Types.ForallSkel (p, typed_to_erasure_ty sub tty)

let rec typed_to_erasure_exp sub tt =
  match tt with
  | Typed.Var v -> EVar v
  | Typed.BuiltIn (s, i) -> failwith __LOC__
  | Typed.Const c -> EConst c
  | Typed.Tuple elist ->
      ETuple (List.map (fun x -> typed_to_erasure_exp sub x) elist)
  | Typed.Lambda abs -> ELambda (typed_to_erasure_abs_with_ty sub abs)
  | Typed.Effect e -> EEffect e
  | Typed.Handler h ->
      let e_pat, tty, v_comp = h.value_clause in
      let op_c = h.effect_clauses in
      let new_vc = typed_to_erasure_abs_with_ty sub h.value_clause in
      let new_op_c =
        Assoc.kmap
          (fun (eff, e_a2) ->
            let new_e_a2 = typed_to_erasure_abs_2 sub e_a2 in
            (eff, new_e_a2))
          op_c
      in
      let new_h = { value_clause = new_vc; effect_clauses = new_op_c } in
      EHandler new_h
  | Typed.BigLambdaTy (tp, sk, e) ->
      let sub1 = Assoc.concat sub (Assoc.update tp sk Assoc.empty) in
      typed_to_erasure_exp sub1 e
  | BigLambdaDirt (_, e) -> typed_to_erasure_exp sub e
  | BigLambdaSkel (sk_p, e) -> EBigLambdaSkel (sk_p, typed_to_erasure_exp sub e)
  | CastExp (e, _) -> typed_to_erasure_exp sub e
  | ApplyTyExp (e, _) -> typed_to_erasure_exp sub e
  | LambdaTyCoerVar (_, _, e) -> typed_to_erasure_exp sub e
  | LambdaDirtCoerVar (_, _, e) -> typed_to_erasure_exp sub e
  | ApplyDirtExp (e, _) -> typed_to_erasure_exp sub e
  | ApplySkelExp (e, s) -> EApplySkelExp (typed_to_erasure_exp sub e, s)
  | ApplyTyCoercion (e, _) -> typed_to_erasure_exp sub e
  | ApplyDirtCoercion (e, _) -> typed_to_erasure_exp sub e

and typed_to_erasure_comp sub tt =
  match tt with
  | Typed.Value e -> EValue (typed_to_erasure_exp sub e)
  | Typed.LetVal (e, (p, _, c)) ->
      let p' = typed_to_erasure_pattern p in
      let e' = typed_to_erasure_exp sub e in
      let c' = typed_to_erasure_comp sub c in
      ELetVal (p', e', c')
  | Typed.Apply (e1, e2) ->
      let e1' = typed_to_erasure_exp sub e1 in
      let e2' = typed_to_erasure_exp sub e2 in
      EApply (e1', e2')
  | Typed.Handle (e, c) ->
      let e' = typed_to_erasure_exp sub e in
      let c' = typed_to_erasure_comp sub c in
      EHandle (e', c')
  | Typed.Call (eff, e, abs) ->
      let e' = typed_to_erasure_exp sub e in
      let abs' = typed_to_erasure_abs_with_ty sub abs in
      ECall (eff, e', abs')
  | Typed.Op (eff, e) -> failwith __LOC__
  | Typed.Bind (c, a) ->
      let c' = typed_to_erasure_comp sub c in
      let a' = typed_to_erasure_abs sub a in
      EBind (c', a')
  | Typed.Match (e, alist) ->
      let e' = typed_to_erasure_exp sub e in
      let alist' = List.map (typed_to_erasure_abs sub) alist in
      EMatch (e', alist')
  | Typed.CastComp (c, _) -> typed_to_erasure_comp sub c
  | Typed.CastComp_ty (c, _) -> typed_to_erasure_comp sub c
  | Typed.CastComp_dirt (c, _) -> typed_to_erasure_comp sub c
  | Typed.LetRec ([ (var, ty, e1) ], c1) ->
      ELetRec
        ( [ (var, typed_to_erasure_ty sub ty, typed_to_erasure_exp sub e1) ],
          typed_to_erasure_comp sub c1 )

and typed_to_erasure_abs_with_ty sub (e_p, e_ty, e_c) =
  ( typed_to_erasure_pattern e_p,
    typed_to_erasure_ty sub e_ty,
    typed_to_erasure_comp sub e_c )

and typed_to_erasure_abs sub (e_p, e_c) =
  (typed_to_erasure_pattern e_p, typed_to_erasure_comp sub e_c)

and typed_to_erasure_abs_2 sub (e_p1, e_p2, e_c) =
  ( typed_to_erasure_pattern e_p1,
    typed_to_erasure_pattern e_p2,
    typed_to_erasure_comp sub e_c )

and typed_to_erasure_pattern = function
  | Typed.PVar x -> PEVar x
  | Typed.PAs (p, x) -> PEAs (typed_to_erasure_pattern p, x)
  | Typed.PNonbinding -> PENonbinding
  | Typed.PConst const -> PEConst const
