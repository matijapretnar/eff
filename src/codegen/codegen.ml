(*type variable = string

type term =
  | Var of variable
  | Const of Syntax.const
  | Lambda of abstraction
  | Effect of Syntax.Effect.t
  | Handler of handler
  | Value of term
  | PureLetIn of variable * term * term
  | Bind of variable * term * term
  | Conditional of term * term * term
  | Apply of term * term
  | Handle of term * term
and abstraction = variable * term
and abstraction2 = variable * variable * term
and handler = {
  val_clause : abstraction;
  eff_clauses : abstraction2 Syntax.EffectMap.t
}
*)

type variable = Syntax.Variable.t * Type.ty
type effect = Syntax.Effect.t * Type.ty * Type.ty

(* Extended Untyped.for Untyped.Directed Optimizations *)

type expression =
  expression' * Type.ty
and expression' =
  | Var of variable
  | Const of Syntax.const
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler
  | PureLetIn of variable * expression * expression
  | PureLetRecIn of variable * abstraction * expression
  | PureConditional of expression * expression * expression
and computation =
  computation' * Type.dirty
and computation' =
  | Value of expression
  | Bind of variable * computation * computation
  | LetIn of variable * expression * computation
  | LetRecIn of variable * abstraction * computation
  | Conditional of expression * computation * computation
  | Apply of expression * expression
  | Handle of expression * computation
  | Call of effect * expression * abstraction
  | LetEffectIn of effect * computation
and abstraction = variable * computation
and pure_abstraction = variable * expression
and abstraction2 = variable * variable * computation
and handler = {
  val_clause : abstraction;
  eff_clauses : abstraction2 Syntax.EffectMap.t
}



(* context type to divide computations*)
type context = computation -> computation

let rec splitC  (c:computation) : (context * computation) = 
  begin match c with
  | (Handle (h,hc), hTy ) -> let (ctx, c') = splitC hc in
                             ( (fun x -> ((Handle (h,x), hTy ))), c')
  | _ -> ((fun x -> x ),c)
  end


module VariableSet = Set.Make(
  struct
    type t = variable
    let compare = Pervasives.compare
  end
  )

let rec freeVarsE ((e',t) : expression) : VariableSet.t =
  freeVarsE' e'
and freeVarsE' (e' : expression') : VariableSet.t =
  begin match e' with
  | PureLetIn (v,e1,e2) -> VariableSet.union (freeVarsE e1) (VariableSet.remove v (freeVarsE e2))
  | Var v -> VariableSet.singleton v
  | PureConditional (e1,e2,e3) -> VariableSet.union (freeVarsE e1) (VariableSet.union (freeVarsE e2) (freeVarsE e3))
  | Const _ -> VariableSet.empty
  | Lambda (x,c) -> VariableSet.remove x (freeVarsC c)
(*
  | PureLambda (x,e) -> VariableSet.remove x (freeVarsE e)
  | PureApply (e1,e2) -> VariableSet.union (freeVarsE e1) (freeVarsE e2) 
*)  
  | Effect _ -> VariableSet.empty
  | PureLetRecIn _ -> failwith "Not implemented yet"
  | Handler h -> freeVarsH h
  end
and freeVarsC ((c',dt) : computation) : VariableSet.t =
  freeVarsC' c'
and freeVarsC' (c' : computation') : VariableSet.t =
  begin match c' with
  | LetIn (v,e,c) -> VariableSet.union (freeVarsE e) (VariableSet.remove v (freeVarsC c))
  | Value e -> freeVarsE e
  | Bind (v,c1,c2) -> VariableSet.union (freeVarsC c1) (VariableSet.remove v (freeVarsC c2))
  | Conditional (e,c1,c2) -> VariableSet.union (freeVarsE e) (VariableSet.union (freeVarsC c1) (freeVarsC c2))
  | Apply (e1,e2) -> VariableSet.union (freeVarsE e1) (freeVarsE e2) 
  | Handle (e,c) -> VariableSet.union (freeVarsE e) (freeVarsC c)
  | Call (_,e1,e2) -> VariableSet.union (freeVarsE e1) (freeVarsA e2)
  | LetRecIn _ -> failwith "Not implemented yet"
  | LetEffectIn (_, c) -> freeVarsC c
  end
and freeVarsH { val_clause = (x,c) ; eff_clauses = m } =
  VariableSet.union (VariableSet.remove x (freeVarsC c))
                    (Syntax.EffectMap.fold (fun _ -> VariableSet.union) (Syntax.EffectMap.map freeVarsA2 m) VariableSet.empty)
and freeVarsA (x,c)  = 
  VariableSet.remove x (freeVarsC c)
and freeVarsA2 (x,y,c)  = 
  VariableSet.remove x (VariableSet.remove y (freeVarsC c))

let rec translate_expression e =
  let e' = match e.Typed.expr with
  | Typed.Var x -> Var x
  | Typed.Const c -> Const c
  | Typed.Lambda a -> Lambda (translate_abstraction a)
  | Typed.Effect eff -> Effect eff
  | Typed.Handler h -> Handler (translate_handler h)
  | Typed.PureLetIn _ -> failwith "Not implemented yet"
  | Typed.PureLetRecIn _ -> failwith "Not implemented yet"
  | Typed.PureConditional _ -> failwith "Not implemented yet"
  in
  (e', e.Typed.expr_ty)
and translate_computation c =
  let c' = match c.Typed.comp with
  | Typed.Value e -> Value (translate_expression e)
  | Typed.Bind (x, c1, c2) -> Bind (x, translate_computation c1, translate_computation c2)
  | Typed.Conditional (e, c1, c2) -> Conditional (translate_expression e, translate_computation c1, translate_computation c2)
  | Typed.Apply (e1, e2) -> Apply (translate_expression e1, translate_expression e2)
  | Typed.Handle (e, c) -> Handle (translate_expression e, translate_computation c)
  | Typed.LetIn _ -> failwith "Not implemented yet"
  | Typed.LetRecIn _ -> failwith "Not implemented yet"
  | Typed.LetEffectIn (eff, c) -> LetEffectIn (eff, translate_computation c)
  | Typed.Call _ -> failwith "Not implemented yet"
  in
  (c', c.Typed.comp_ty)
and translate_abstraction (x, c) =
  (x, translate_computation c)
and translate_abstraction2 (x1, x2, c) =
  (x1, x2, translate_computation c)
and translate_handler {Typed.val_clause=vc; Typed.eff_clauses=ecs} =
  {
    val_clause = translate_abstraction vc;
    eff_clauses = Syntax.EffectMap.map (fun (_, _, a) -> translate_abstraction2 a) ecs
  }

let rec substituteE (v : variable) (e1 : expression) ((e2',t) : expression) =
  (substituteE' v e1 e2', t)
and substituteE' (v : variable) (e1 : expression) (e2' : expression') =
  begin match e2' with
  | PureLetIn (w,ea,eb) when (v = w) -> PureLetIn (w, substituteE v e1 ea, eb)
  | PureLetIn (w,ea,eb)              -> PureLetIn (w, substituteE v e1 ea, substituteE v e1 eb)
  | Var w when (v = w)  ->  fst e1
  | Var w               ->  e2'
  | PureConditional (ea,eb,ec) -> PureConditional (substituteE v e1 ea, substituteE v e1 eb, substituteE v e1 ec)
  | Const _  -> e2'
  | Lambda a  -> Lambda (substituteA v e1 a)
(*  | PureLambda (w, e) when (w=v) -> e2'
  | PureLambda (w, e)            -> PureLambda (w, substituteE v e1 e)
  | PureApply (ea,eb) -> PureApply (substituteE v e1 ea, substituteE v e1 eb)
 *)
  | Effect _ -> e2'
  | Handler h -> 
     Handler { val_clause = substituteA v e1 h.val_clause
             ; eff_clauses = Syntax.EffectMap.map (substituteA2 v e1) h.eff_clauses }
  | PureLetRecIn _ -> failwith "Not implemented yet"
  end
and substituteC (v : variable) (e : expression) ((c,dt) : computation) =
  (substituteC' v e c, dt)
and substituteC' (v : variable) (e : expression) (c' : computation') =
  begin match c' with
  | LetIn (w,ea,cb) when (v = w) -> LetIn (w, substituteE v e ea, cb)
  | LetIn (w,ea,cb)              -> LetIn (w, substituteE v e ea, substituteC v e cb)
  | Value ea -> Value (substituteE v e ea)
  | Bind (w,ca,cb) when (v = w) -> Bind (w, substituteC v e ca, cb)
  | Bind (w,ca,cb)              -> Bind (w, substituteC v e ca, substituteC v e cb)
  | Conditional (ea,cb,cc) -> Conditional (substituteE v e ea, substituteC v e cb, substituteC v e cc)
  | Apply (ea,eb) -> Apply (substituteE v e ea, substituteE v e eb)
  | Handle (ea,cb) -> Handle (substituteE v e ea, substituteC v e cb)
  | Call (eff,ea,eb) -> Call (eff, substituteE v e ea, substituteA v e eb)
  | LetRecIn _ -> failwith "Not implemented yet"
  | LetEffectIn (eff, c) -> LetEffectIn (eff, substituteC v e c)
  end
and substituteA (v : variable) (e : expression) ((w,c) : abstraction) =
  if v = w 
    then (w, c)
    else (w, substituteC v e c)
and substituteA2 (v : variable) (e : expression) ((x,k,c) as a2: abstraction2) =
  if (v = x || v = k)
    then a2
    else (x,k,substituteC v e c)
  
  (* TODO *)

(*let _ = Header.run*)

(* REMARK: ORDER OF EVALUATION
     
-  We assume that the order of evaluation for expressions
   does not matter. For instance we are delaying the evaluation
   of handler expressions.

   If at a later point in time, we add diverging expressions (e.g.,
   in the form of recursive pure functions or a fixpoint combinator)
   we need to revisit this decision. 
   
 *)

(* REMARK: APPROXIMATION OF TYPES

   We are at various occasions approximating the types of subexpressions
   with less precise types from the overall expression. This should be
   revisited to obtain more accurate types.

 *)

let isAtomic (e,t) = 
  begin match e with
   | (Var _)   -> true
   | (Const _) -> true
   | (Effect _)  -> true
   | _         -> false
  end

let rec optimizeE = function
  | (e,t) -> (optimizeE'(e,t))
and optimizeE' = function
  | ( PureLetIn(v,e1,e2) ,ty ) 
  -> let e1' = optimizeE e1 in
     if isAtomic e1' 
       then optimizeE (substituteE v e1' e2)
       else begin match (optimizeE e2) with
       | (Const cons, _) -> (Const cons, ty)
       | e2' -> (PureLetIn(v,e1',e2') ,ty)
     end
  | ( Var x ,ty ) -> ( Var x , ty)
  | ( PureConditional(e1,e2,e3) ,ty ) -> ( PureConditional(optimizeE e1,optimizeE e2,optimizeE e3) , ty)
  | ( Const c ,ty ) -> ( Const c , ty)
  | ( Lambda a ,((Type.Function (inTy, (ouTy,dirt))) as ty)) ->  
          begin match (optimize_abstraction a) with
          | a'  -> ( Lambda a' , ty )
          end
  | ( Lambda a, ty ) ->
      print_string "Bad type for lambda!\n"; 
      ( Lambda a, ty )
  | (PureLetRecIn _, _) -> failwith "Not implemented yet"
(*
  | ( PureLambda a , ty ) -> 
        begin match optimize_pure_abstraction a with
        | (x , (PureApply (e , (Var y , _)) , _)) when (x = y && not (VariableSet.mem x (freeVarsE e))) -> e 
        | a' -> ( PureLambda a' , ty )
        end
  | ( PureApply (e1, e2) ,ty ) -> 
          begin match (optimizeE e1) with
          | (PureLambda (v,e) , _ ) as e1' -> let e2' = optimizeE e2 in
              if isAtomic e2' then optimizeE (substituteE v e2' e) else (PureApply (e1', e2'), ty)
          | e1' -> (PureApply (e1', optimizeE e2), ty)
          end
*)
  | ( Effect eff ,ty ) -> ( Effect eff , ty)
  | ( Handler h ,ty ) -> ( Handler (optimize_handler h) ,ty)
and optimizeC = function
  | (LetIn (v,e,c) , ty) -> 
      let e' = optimizeE e in
      if isAtomic e'
        then optimizeC (substituteC v e' c)
        else begin match optimizeC c with
             | (Value e2 , (vty,_)) -> optimizeC (Value (PureLetIn (v, e', e2) , vty) , ty )
             | (Apply ((Var w , _) , e2') , _) when (v = w && not (VariableSet.mem v (freeVarsE e))) 
             -> optimizeC (Apply (e' , e2') , ty)
             | c' ->  
              let (ctxt, c'') = splitC c' in
              begin match c'' with
              | (Apply ((Var w, _),  e7), dt'') when (v=w) -> optimizeC (ctxt (Apply (e', e7), dt''))
              | _ -> (LetIn (v, e', c') , ty)
              end
             end
  | (Value e,ty) -> (Value (optimizeE e),ty)
  | (Bind (v,c1,c2),ty) -> begin match (optimizeC c1) with
      | (Value v2, di) -> optimizeC (LetIn (v, v2, optimizeC c2) , ty)
      | (LetIn (vc,ec,cc), _) -> optimizeC (LetIn (vc, ec, (Bind (v, optimizeC cc, optimizeC c2) , ty) )  , ty )
      | (Bind (pi,c1i,c2i),di) -> optimizeC (Bind (pi, c1i, optimizeC (Bind (v, c2i, c2),ty)), ty) 
      | (Call (eff,e1,(((_ , pureTy), (_, dirtyTy)) as e2)), sty) -> 
                                           let y = (Untyped.fresh_variable (),pureTy )  in
                                           let vy = (Var y, pureTy)  in
                                           let application = (Apply ((Lambda e2, Type.Function (pureTy, dirtyTy)), vy), dirtyTy) in
                                           let body = (Bind (v, application, c2), ty) in 
                                           let abstr = (y, body) in
                                           optimizeC (Call (eff , e1, abstr) , ty)

(*    | (Apply ((Effect eff , effTy) , exp),aty) -> 
                       begin match (optimizeC c2) with
                       | (Apply ((Var vdup, _),k), _) when (vdup = v)-> optimizeC (Call (eff, exp, k) , ty)
                       | (Bind (vy, (Apply ( ( ( Var xvar, _) as vx),  ( (kcomp, Type.Function(kpureTy,kdirtyTy)) as k)  ), aTy), cc ),bTy)  when (xvar = v) ->
                                  let z = (Untyped.fresh_variable (), kpureTy )  in
                                  let vz = (Var z, kpureTy )  in
                                  let application =  (Apply (k, vz),  kdirtyTy)  in
                                  let lambda_body = (Bind (vy, application, cc) , bTy ) in
                                  let lambda = (Lambda (z, lambda_body) , Type.Function(kpureTy,bTy)) in
                                  optimizeC (Call (eff , exp, lambda) , ty )

                       | c2' -> (Bind (v, (Apply ((Effect eff , effTy) , exp),aty), c2'),ty)
                       end
*)                     
      | c -> (Bind (v, c, optimizeC c2),ty)
      end
  | (Conditional (e,c1,c2),ty) -> (Conditional (optimizeE e, optimizeC c1, optimizeC c2),ty)
  | (Apply (e1, e2),((ty,_) as dt)) -> 
        begin match optimizeE e1 with
        | ( Lambda (x, (Apply ((Var xv, _) , eapply), _ )) , _) when xv = x ->
                            optimizeC( (Apply  (e2, eapply) , dt) )

        | ( Lambda (x,(Value ev,vty)) , _ ) -> optimizeC(Value ( PureLetIn (x , e2 , ev), snd(ev)) ,  dt )
        | ( Lambda (x,c) , _ ) as e1' -> 
              let e2' = optimizeE e2 in
              if isAtomic e2' then optimizeC (substituteC x e2' c) else (Apply (e1', e2'), dt)

        | (Effect (((effstring,effTin,effTout)) as eff), effTy) -> 
                             let z = (Untyped.fresh_variable (), effTout )  in
                             let vz = (Var z, effTout )  in
                             let lambdadt = (effTout , Type.fresh_dirt ()) in 
                             let lambda_body = (Value vz, lambdadt) in
                             let abstr = (z,lambda_body) in 
                             optimizeC (Call ( eff , e2, abstr ) , dt)

        | e1' -> (Apply (e1' , optimizeE e2) , dt)
        end
  | (Handle (e, c),((pureTy,dirtyTy) as ty)) -> begin match (optimizeC c) with
          | (LetIn (v,e2,c2), lty) -> optimizeC ( LetIn (v , e2, (Handle ( e, c2) , ty )) , ty )
          | (Value v , vty)  -> begin match (optimizeE e) with
                              | (Handler h, hty) -> optimizeC (Apply ((Lambda h.val_clause, fst(snd(snd h.val_clause)) ) , v) , ty )
                              | e' ->  (Handle (e', (Value v , vty)) ,  ty) 
                              end   

          | (Call (((effstr,_,_) as eff), ((e_expr,e_exprTy) as ecall), ( ((_, kpureTy), (_ ,kdirtyTy)) as k) ) , scTy) -> 
                              begin match (optimizeE e) with 
                              | (Handler h , ( Type.Handler(hdirtyinTy, hdirtyoutTy) as hTy)) ->  
                                                      let value = Syntax.EffectMap.mem effstr h.eff_clauses in
                                                      if value then
                                                         let (x,y,eff_comp) = Syntax.EffectMap.find effstr h.eff_clauses in
                                                         let z = (Untyped.fresh_variable (),  kpureTy) in
                                                         let vz = (Var z,  kpureTy)  in
                                                         let apply = (Apply ((Lambda k, Type.Function (kpureTy, kdirtyTy)), vz), kdirtyTy) in
                                                         let handle = (Handle ((Handler h, hTy), apply), hdirtyoutTy  ) in
                                                         let lambda = (Lambda (z, handle) , Type.Function (kpureTy,hdirtyoutTy) ) in 
                                                         let letc_in = (LetIn (y, lambda , eff_comp) , snd(eff_comp) ) in
                                                         optimizeC ((LetIn (x,ecall,letc_in) , ty  ))
                                                      else
                                                         let z = (Untyped.fresh_variable (),  kpureTy)  in
                                                         let vz = (Var z,  kpureTy)  in
                                                         let application =  (Apply ((Lambda k, Type.Function (kpureTy, kdirtyTy)), vz), kdirtyTy )  in 
                                                         let lambda_body = (Handle ((Handler h, hTy) , application), hdirtyoutTy ) in
                                                         let abstr = (z,lambda_body) in 
                                                         optimizeC (Call (eff, ecall, abstr), ty)
                             | e' -> (Handle  (e',(Call (eff,ecall,k), scTy)) , ty)
                           end
          | c' -> (Handle (optimizeE e, c'),ty)
          end
  | (Call (eff,e1,e2) , ty ) -> (Call (eff, optimizeE e1, optimize_abstraction e2) , ty ) 
  | (LetRecIn _, _) -> failwith "Not implemented"
  | (LetEffectIn (eff, c), ty) -> (LetEffectIn (eff, optimizeC c), ty)

and optimize_abstraction (x, c) = (x, optimizeC c)
and optimize_pure_abstraction (x, e) = (x, optimizeE e)
and optimize_abstraction2 (x1, x2, c) = (x1, x2, optimizeC c)
and optimize_handler h = {
  val_clause = optimize_abstraction h.val_clause;
  eff_clauses = Syntax.EffectMap.map optimize_abstraction2 h.eff_clauses
}
