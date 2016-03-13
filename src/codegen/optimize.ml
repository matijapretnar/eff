(*
 To Do list for optimization :

  ==> (done) optimize sub_computation (LetRec)
  ==> (done) Optimize sub_expression (Record/Variant) 
  ==> (done) Freevarse (Records/ Variants)
  ==> (done) Beta reduction with variables occur only once & not in a binder
      (let-in apply) (pure_let-in pure_apply) (bind)
  ==> (done) free_vars letrec
  ==> (done) occurrences (patterns/variants)
  ==> (donefix all pattern matching warnings and not halt when pattern is not var (PRIORITY)
  ==> (done)Substitution for LetRec
  ==> Make regression tests

  ==> (let x = e in e1) e2 -> let x = e in e1 e2
  ==> (done) effect clauses in handlers substitution
  ==> handler occurrences

  ==> (done) effect eff ===> fun param -> call eff param (fun result -> value result)
  ==> (done in const cases) match beta reduction

  ==> (done)A bug related to handlers patterns, patterns bound twice which is not correct (check choice.ml)
  ==> Handlers inline.

*)




open Typed


let unary_inlinable f ty1 ty2 = 
  let x = Typed.Variable.fresh "x"
  and loc = Location.unknown in
  let drt = Type.fresh_dirt () in
  let p = {
    term = (Pattern.Var x, loc);
    location = loc;
    scheme = Scheme.simple ty1
  } in
  pure_lambda ~loc @@
    pure_abstraction ~loc p @@
      pure_apply ~loc
        (built_in ~loc f (Scheme.simple (Type.Arrow (ty1, (ty2, drt)))))
        (var ~loc x (Scheme.simple ty1))

let binary_inlinable f ty1 ty2 ty =
  let x1 = Typed.Variable.fresh "x1"
  and x2 = Typed.Variable.fresh "x2"
  and loc = Location.unknown
  and drt = Type.fresh_dirt () in
  let p1 = {
    term = (Pattern.Var x1, loc);
    location = loc;
    scheme = Scheme.simple ty1
  }
  and p2 = {
    term = (Pattern.Var x2, loc);
    location = loc;
    scheme = Scheme.simple ty2
  } in
  lambda ~loc @@
    abstraction ~loc p1 @@
      value ~loc @@
        lambda ~loc @@
          abstraction ~loc p2 @@
            value ~loc @@
              pure_apply ~loc (
                pure_apply ~loc
                  (built_in ~loc f (Scheme.simple (Type.Arrow (ty1, (Type.Arrow (ty2, (ty, drt)), drt)))))
                  (var ~loc x1 (Scheme.simple ty1))
              ) (var ~loc x2 (Scheme.simple ty2))

let inlinable_definitions = [
  (* Do not inline them because they are polymorphic *)
  (* ("=", binary_inlinable "Pervasives.(=)" ? ? Type.bool_ty); *)
  (* ("<", binary_inlinable "Pervasives.(<)" ? ? Type.bool_ty); *)
  ("~-", unary_inlinable "Pervasives.(~-)" Type.int_ty Type.int_ty);
  ("+", binary_inlinable "Pervasives.(+)" Type.int_ty Type.int_ty Type.int_ty);
  ("*", binary_inlinable "Pervasives.( * )" Type.int_ty Type.int_ty Type.int_ty);
  ("-", binary_inlinable "Pervasives.(-)" Type.int_ty Type.int_ty Type.int_ty);
  ("mod", binary_inlinable "Pervasives.(mod)" Type.int_ty Type.int_ty Type.int_ty);
  ("~-.", unary_inlinable "Pervasives.(~-.)" Type.float_ty Type.float_ty);
  ("+.", binary_inlinable "Pervasives.(+.)" Type.float_ty Type.float_ty Type.float_ty);
  ("*.", binary_inlinable "Pervasives.( *. )" Type.float_ty Type.float_ty Type.float_ty);
  ("-.", binary_inlinable "Pervasives.(-.)" Type.float_ty Type.float_ty Type.float_ty);
  ("/.", binary_inlinable "Pervasives.(/.)" Type.float_ty Type.float_ty Type.float_ty);
  ("/", binary_inlinable "Pervasives.(/)" Type.int_ty Type.int_ty Type.int_ty);
  ("float_of_int", unary_inlinable "Pervasives.(float_of_int)" Type.int_ty Type.float_ty);
  ("^", binary_inlinable "Pervasives.(^)" Type.string_ty Type.string_ty Type.string_ty);
  ("string_length", unary_inlinable "Pervasives.(string_length)" Type.string_ty Type.int_ty)
  ]

let inlinable = ref []


let make_var_from_pattern p =  begin match fst (p.term) with 
                                | Pattern.Var z ->  var ~loc:p.location z p.scheme
                                | Pattern.As (_,x) -> var ~loc:p.location x p.scheme
                                | _ -> failwith "MATCHED A non var PATTERN" 
                              end


let make_expression_from_pattern p = 
                            begin match fst (p.term) with
                            | Pattern.Var z -> var ~loc:p.location z p.scheme
                            | Pattern.Tuple [] -> tuple ~loc:p.location []
                            | _ -> failwith "matched a non var or unit pattern"
                          end

let make_var_counter =
  let count = ref (0) in
  fun () ->
    incr count;
    !count

let make_var_from_counter scheme = 
      let counter_string = string_of_int (make_var_counter ()) in
      let x = Typed.Variable.fresh ("fresh_pattern_" ^ counter_string) in
      var ~loc:Location.unknown x scheme

let make_pattern_from_var v = 
        let (Var va) = v.term in
    {term = (Pattern.Var va, Location.unknown);
    location = Location.unknown;
    scheme = v.scheme}


let refresh_pattern p =
      begin match fst (p.term) with
      | Pattern.Var x -> let counter_string = string_of_int (make_var_counter ()) in
                         let y = Typed.Variable.fresh ("fresh_pattern_" ^ counter_string) in 
                         {term = (Pattern.Var y, Location.unknown);
                          location = Location.unknown;
                          scheme = p.scheme}
      
      | Pattern.As (c,x) -> failwith "Pattern can not be refreshed for now"
      | Pattern.Tuple [] -> p
      | Pattern.Tuple lst -> failwith "Pattern can not be refreshed for now"
      | Pattern.Record _ -> failwith "Pattern can not be refreshed for now"
      | Pattern.Variant _ -> failwith "Pattern can not be refreshed for now"
      | Pattern.Const _ -> failwith "Pattern can not be refreshed for now"
      | Pattern.Nonbinding -> failwith "Pattern can not be refreshed for now"
    end


module VariableSet = Set.Make(
  struct
    type t = variable
    let compare = Pervasives.compare
  end
  )


let rec is_pure_comp c = 
  begin match c.term with
  | Value e -> true
  | Let (li,cf) -> is_pure_comp cf
  
  | LetRec (li, c1) -> let func = (fun (_,abs)-> let (_,c') = abs.term in 
                                    is_pure_comp c') in 
                        List.fold_right (&&) (List.map func li) (is_pure_comp c1)
  

  | Match (e, li) -> let func = fun a ->  fun b ->  
                                let (pt,ct) = a.term in 
                                (is_pure_comp ct) && b
                     in (List.fold_right  func li true)
                     
  | While (c1, c2) -> (is_pure_comp c1) && (is_pure_comp c2)
  | For (v, e1, e2, c1, b) -> is_pure_comp c1
  | Apply (e1, e2) -> (is_pure_exp e1) && (is_pure_exp e2)
  | Handle (e, c1) -> (is_pure_exp e) && (is_pure_comp c1)
  | Check c1 -> is_pure_comp c1
  | Call _ -> false
  | Bind (c1, a1) -> let (p1,cp1) = a1.term in
                           (is_pure_comp c1) && (is_pure_comp cp1)
  | LetIn (e, a) -> let (p1,cp1) = a.term in
                           (is_pure_exp e) && (is_pure_comp cp1)
  end 

and is_pure_exp e =
  begin match e.term with 
  | Var v  -> true
  | Const _ -> true
  | Tuple lst -> List.fold_right (&&) (List.map is_pure_exp lst) true
  | Lambda a -> let (p1,cp1) = a.term in
                           is_pure_comp cp1
  | Handler h -> true
  | Record lst -> true
  | Variant (label,exp) -> begin match (Common.option_map is_pure_exp exp) with 
                           | Some set -> set
                           | None -> true
                           end 
  | PureLambda pa -> let (p1,ep1) = pa.term in
                           is_pure_exp ep1
  | PureApply (e1,e2) -> (is_pure_exp e1) && (is_pure_exp e2)
  | PureLetIn (e,pa) -> let (p1,ep1) = pa.term in
                           (is_pure_exp e) && (is_pure_exp ep1)
  | BuiltIn _ -> true
  | Effect _->  true
    end



let rec free_vars_c c : VariableSet.t = 
  begin match c.term with 
  | Value e -> free_vars_e e
  | Let (li,cf) -> let func = (fun a ->  fun b ->  
                                let(ap,ac) = a in 
                                let pattern_vars = Pattern.pattern_vars (ap.term) in
                                let vars_set = VariableSet.of_list pattern_vars in
                                VariableSet.union (VariableSet.diff (free_vars_c ac) vars_set) b )in  
                    VariableSet.union (free_vars_c cf) (List.fold_right func li VariableSet.empty)
  
  | LetRec (li, c1) -> free_vars_let_rec li c1
  

  | Match (e, li) -> let func = fun a ->  fun b ->  
                                let (ap,ac) = a.term in 
                                let pattern_vars = Pattern.pattern_vars (ap.term) in
                                let vars_set = VariableSet.of_list pattern_vars in
                                VariableSet.union (VariableSet.diff (free_vars_c ac) vars_set) b 
                     in VariableSet.union (free_vars_e e) (List.fold_right func li VariableSet.empty)
                     
  | While (c1, c2) -> VariableSet.union (free_vars_c c1) (free_vars_c c2)
  | For (v, e1, e2, c1, b) -> VariableSet.remove v (free_vars_c c1)
  | Apply (e1, e2) -> VariableSet.union (free_vars_e e1) (free_vars_e e2)
  | Handle (e, c1) -> VariableSet.union (free_vars_e e) (free_vars_c c1)
  | Check c1 -> free_vars_c c1
  | Call (eff, e1, a1) ->  let(p1,cp1) = a1.term in 
                           let pattern_vars = Pattern.pattern_vars (p1.term) in
                           let vars_set = VariableSet.of_list pattern_vars in
                            VariableSet.union (free_vars_e e1) (VariableSet.diff (free_vars_c cp1) vars_set)

  | Bind (c1, a1) -> let(p1,cp1) = a1.term in 
                     let pattern_vars = Pattern.pattern_vars (p1.term) in
                     let vars_set = VariableSet.of_list pattern_vars in
                     VariableSet.union (free_vars_c c1) (VariableSet.diff (free_vars_c cp1) vars_set)

  | LetIn (e, a) ->  let(p1,cp1) = a.term in 
                     let pattern_vars = Pattern.pattern_vars (p1.term) in
                     let vars_set = VariableSet.of_list pattern_vars in
                            VariableSet.union (free_vars_e e) (VariableSet.diff (free_vars_c cp1) vars_set)
  end

and free_vars_e e : VariableSet.t = 
  begin match e.term with 
  | Var v  -> VariableSet.singleton v
  | Const _ -> VariableSet.empty
  | Tuple lst -> List.fold_right VariableSet.union (List.map free_vars_e lst ) VariableSet.empty
  | Lambda a -> let(p1,cp1) = a.term in 
                     let pattern_vars = Pattern.pattern_vars (p1.term) in
                     let vars_set = VariableSet.of_list pattern_vars in
                     VariableSet.diff (free_vars_c cp1) vars_set
  | Handler h -> free_vars_handler h
  | Record lst -> List.fold_right ( fun (_, set) -> fun b -> VariableSet.union set b ) (Common.assoc_map free_vars_e lst) VariableSet.empty
  | Variant (label,exp) -> begin match (Common.option_map free_vars_e exp) with 
                           | Some set -> set
                           | None -> VariableSet.empty
                           end 
  | PureLambda pa -> let(p1,ep1) = pa.term in 
                     let pattern_vars = Pattern.pattern_vars (p1.term) in
                     let vars_set = VariableSet.of_list pattern_vars in
                     VariableSet.diff (free_vars_e ep1) vars_set

  | PureApply (e1,e2) -> VariableSet.union (free_vars_e e1) (free_vars_e e2)

  | PureLetIn (e,pa) -> let(p1,ep1) = pa.term in 
                     let pattern_vars = Pattern.pattern_vars (p1.term) in
                     let vars_set = VariableSet.of_list pattern_vars in
                            VariableSet.union (free_vars_e e) (VariableSet.diff (free_vars_e ep1) vars_set)
  | BuiltIn _ -> VariableSet.empty
  | Effect _->  VariableSet.empty
    end

and free_vars_let_rec li c1 : VariableSet.t = 
                                    let var_binders_set = VariableSet.of_list (List.map (fun (v,_) -> v) li) in
                                    let func = (fun a ->  fun b ->  
                                                let(_,abs) = a in 
                                                let (ap,ac) = abs.term in
                                                let pattern_vars = Pattern.pattern_vars (ap.term) in
                                                let vars_set = VariableSet.of_list pattern_vars in
                                                VariableSet.union (VariableSet.diff (free_vars_c ac) vars_set) b )in
                                    let free_vars = List.fold_right func li (free_vars_c c1) in
                                    VariableSet.diff free_vars var_binders_set


and free_vars_handler h : VariableSet.t = let (pv,cv) = (h.value_clause).term in 
                                          let (pf,cf) = (h.finally_clause).term in
                                          let eff_list = h.effect_clauses in
                                          let pv_vars = VariableSet.of_list (Pattern.pattern_vars (pv.term)) in
                                          let pf_vars = VariableSet.of_list (Pattern.pattern_vars (pf.term)) in
                                          let func = fun a -> fun b ->
                                                    let (p1,p2,c) = (snd a).term in 
                                                    let p1_vars = Pattern.pattern_vars (p1.term) in 
                                                    let p2_vars = Pattern.pattern_vars (p2.term) in
                                                    let p_all_vars = VariableSet.of_list (p1_vars @ p2_vars) in  
                                          VariableSet.union (VariableSet.diff (free_vars_c c) p_all_vars ) b
                                          in
                                          VariableSet.union ( VariableSet.union 
                                                                (VariableSet.diff (free_vars_c cv) pv_vars) 
                                                                (VariableSet.diff (free_vars_c cf) pf_vars))
                                                            (List.fold_right func eff_list VariableSet.empty) 


let rec occurrences v c =

    begin match c.term with
  | Value e -> let (ep,ef) =  occurrences_e v e in (ep,ef)
  | Let (li,cf) -> failwith "occ found a let, all should turn to binds" 
                                  
  | LetRec (li, c1) -> let (binder,free) = occurrences_letrec v li c1 
                        in (binder,free) 

  | Match (e, li) -> let func = fun a ->  
                                let (pt,ct) = a.term in 
                                let (ctb,ctf) = occurrences v ct in 
                                if(List.mem v (Pattern.pattern_vars pt.term)) then (0,0)
                                else (ctb+ctf,0)
                  in let new_list = List.map func li in
                     let func2 = fun (b,f) -> fun (sb,sf) -> (b+sb,f+sf) in
                     let (resb,resf) = List.fold_right func2 new_list (0,0) in
                     let (be,fe) = occurrences_e v e in
                     (resb+be, resf+fe)
                     
  | While (c1, c2) -> let (c1b,c1f) = occurrences v c1 in
                      let (c2b,c2f) = occurrences v c2 in
                      (c1b+c2b , c1f+c2f)

  | For (vr, e1, e2, c1, b) -> let (e1b,e1f) = occurrences v c1 in
                               if (v == vr) then (0, 0)
                               else (e1b+e1f,0)

  | Apply (e1, e2) -> let (e1b,e1f) = occurrences_e v e1 in
                      let (e2b,e2f) = occurrences_e v e2 in
                      (e1b+e2b , e1f+e2f)
  
  | Handle (e, c1) -> let (e1b,e1f) = occurrences_e v e in
                      let (c2b,c2f) = occurrences v c1 in
                      (e1b+c2b , e1f+c2f)
  | Check c1 -> occurrences v c1
  | Call (eff, e1, a1) -> let (p1,cp1) = a1.term in
                           let (pe1,fe1) = occurrences_e v e1 in
                           let (pcp1,fcp1) = occurrences v cp1 in
                           if (List.mem v (Pattern.pattern_vars p1.term))  then (pe1, fe1 )
                         else
                              (pe1+pcp1+fcp1, fe1)

  | Bind (c1, a1) -> let (p1,cp1) = a1.term in
                           let (pc1,fc1) = occurrences v c1 in
                           let (pcp1,fcp1) = occurrences v cp1 in
                           if (List.mem v (Pattern.pattern_vars p1.term))  then (pc1, fc1 )
                         else
                              (pc1+pcp1+fcp1, fc1)
  | LetIn (e, a) -> let (p1,cp1) = a.term in
                           let (pe1,fe1) = occurrences_e v e in
                           let (pcp1,fcp1) = occurrences v cp1 in
                           if (List.mem v (Pattern.pattern_vars p1.term))  then (pe1, fe1 )
                         else
                              (pe1+pcp1+fcp1, fe1)
                            
  end

and occurrences_e v e = 
  begin match e.term with 
  | Var vr  -> if (v == vr) then (0,1) else (0,0)
  | Const _ -> (0,0)
  | Tuple lst -> 
                let func = fun a -> fun (sb,sf) -> let (pa,fa) = a in (pa+sb,fa+sf) in 
                List.fold_right func (List.map (occurrences_e v) lst ) (0,0)
  | Lambda a -> let (p1,cp1) = a.term in
                           let (pcp1,fcp1) = occurrences v cp1 in
                           if (List.mem v (Pattern.pattern_vars p1.term))  then (0, 0)
                         else
                              (pcp1+fcp1,0)
  | Handler h -> occurrences_handler v h
  | Record lst -> List.fold_right ( fun (_, (boc,foc)) -> fun (sb,sf) -> (sb+boc,foc+sf) ) 
                                  (Common.assoc_map (occurrences_e v) lst) (0,0)
  | Variant (label,exp) -> begin match (Common.option_map (occurrences_e v) exp) with 
                           | Some set -> set
                           | None -> (0,0)
                           end 
  | PureLambda pa -> let (p1,ep1) = pa.term in
                           let (pep1,fep1) = occurrences_e v ep1 in
                           if (List.mem v (Pattern.pattern_vars p1.term))  then (0, 0 )
                         else
                              (pep1+fep1,0)

  | PureApply (e1,e2) -> let (e1b,e1f) = occurrences_e v e1 in
                         let (e2b,e2f) = occurrences_e v e2 in
                         (e1b+e2b , e1f+e2f)

  | PureLetIn (e,pa) -> let (p1,ep1) = pa.term in
                           let (pe1,fe1) = occurrences_e v e in
                           let (pep1,fep1) = occurrences_e v ep1 in
                           if (List.mem v (Pattern.pattern_vars p1.term))  then (pe1,fe1 )
                         else
                              (pe1+pep1+fep1, fe1)
  | BuiltIn _ -> (0,0)
end

and occurrences_handler v h = (10,10) (*not implmented yet*)

and occurrences_letrec v li c =     let var_binders_set = (List.map (fun (vr,_) -> vr) li) in
                                    if(List.mem v var_binders_set ) then (0,0)
                                  else 
                                    let func = (fun a ->  fun (b0,f0) ->  
                                                let(_,abs) = a in 
                                                let (ap,ac) = abs.term in
                                                let pattern_vars = Pattern.pattern_vars (ap.term) in
                                                let (bo,fo) = occurrences v ac in
                                                if (List.mem v pattern_vars) 
                                                  then (b0,f0) 
                                                  else (bo+fo+b0,f0))
                                              in
                                    let (vr_bo,vr_fo) = List.fold_right func li (0,0) in
                                    let (vr_boc,vr_foc) = occurrences v c in
                                    (vr_bo+vr_boc,vr_fo+vr_foc)

and pattern_occurrences p c = let pvars = Pattern.pattern_vars (p.term) in 
                              let func = (fun a -> fun (sb,sf) -> 
                                          let (ba,fa) = occurrences a c in
                                          (ba+sb , fa+sf))
                            in List.fold_right func pvars (0,0)

and pattern_occurrences_e p e = let pvars = Pattern.pattern_vars (p.term) in 
                              let func = (fun a -> fun (sb,sf) -> 
                                          let (ba,fa) = occurrences_e a e in
                                          (ba+sb , fa+sf))
                            in List.fold_right func pvars (0,0)


let print_free_vars c = print_endline "in free vars print ";
  let fvc = free_vars_c c in 
  Print.debug "free vars of  %t  is" (CamlPrint.print_computation c);
  (VariableSet.iter (fun v -> (Print.debug "free var :  %t" (CamlPrint.print_variable v)))) fvc 

let is_atomic e = begin match e.term with 
                    | Var _ -> true
                    | Const _ -> true
                    | _ -> false
                  end

let is_var e = begin match e.term with
               | Var _ -> true
               | _ -> false
             end





let rec substitute_var_comp comp vr exp =
(*   Print.debug "Substituting %t" (CamlPrint.print_computation comp); *)
        let loc = Location.unknown in
        begin match comp.term with
          | Value e -> value ~loc:loc (substitute_var_exp e vr exp)
          | Let (li,cf) ->  failwith "Substituting in let, should all be changed to binds"
          
          | LetRec (li, c1) -> let bound_vars = List.map (fun (v,_) -> v) li in 
                               let func = (fun (v,a) -> 
                                              let (p,c) = a.term in
                                              let (p_vars) = Pattern.pattern_vars (p.term) in
                                              let p_vars_set = VariableSet.of_list p_vars in
                                              if ((List.mem vr p_vars) || (List.mem vr bound_vars))
                                                then (v,a)
                                              else
                                                 if ( VariableSet.equal (VariableSet.inter (p_vars_set) (free_vars_e exp)) VariableSet.empty ) 
                                                    then (v, (abstraction ~loc:loc p (substitute_var_comp c vr exp)))
                                                 else 
                                                    begin 
                                                    print_endline  "we do renaming (should never happen) with ";
                                                    let new_p= refresh_pattern p in 
                                                    let new_pe = make_expression_from_pattern new_p in 
                                                    let fresh_c = substitute_pattern_comp c (p.term) new_pe c in 
                                                     (v,(abstraction ~loc:loc new_p ( substitute_var_comp fresh_c vr exp)))
                                                    end
                                         ) in
                                if (List.mem vr bound_vars)
                                    then let_rec' ~loc:loc (List.map func li) c1
                                else
                                    let_rec' ~loc:loc (List.map func li) (substitute_var_comp c1 vr exp)


          | Match (e, li) -> let func = (fun a -> let (p,c) = a.term in 
                                         match fst (p.term) with 
                                         | Pattern.Const _-> a
                                         | _ -> 
                                         let temp_lambda = lambda ~loc:loc (abstraction ~loc:loc p c) in 
                                         let new_temp_lambda = substitute_var_exp temp_lambda vr exp in
                                         let (Lambda newa) = new_temp_lambda.term in
                                         newa) in
                            match' ~loc:loc (substitute_var_exp e vr exp) (List.map func li)
          | While (c1, c2) -> while' ~loc:loc (substitute_var_comp c1 vr exp) (substitute_var_comp c2 vr exp)
          | For (v, e1, e2, c1, b) -> for' ~loc:loc v (substitute_var_exp e1 vr exp) (substitute_var_exp e2 vr exp) (substitute_var_comp c1 vr exp) b
          | Apply (e1, e2) -> apply ~loc:loc (substitute_var_exp e1 vr exp) (substitute_var_exp e2 vr exp)
          | Handle (e, c1) -> handle ~loc:loc (substitute_var_exp e vr exp) (substitute_var_comp c1 vr exp)
          | Check c1 -> check ~loc:loc (substitute_var_comp c1 vr exp)
          | Call (eff, e1, a1) -> print_endline "matched with call in sub var";
                                  let (p,c1) = a1.term in
                                  let fp = refresh_pattern p in 
                                  let fpe = make_expression_from_pattern fp in 
                                  let new_abs = abstraction ~loc:loc fp (substitute_pattern_comp c1 (p.term) fpe c1)  in
                                  let new_lambda = (substitute_var_exp (lambda ~loc:loc new_abs) vr exp) in 
                                  let (Lambda new_a) = new_lambda.term in
                                  call ~loc:loc eff (substitute_var_exp e1 vr exp )  new_a
          
          | Bind (c1, a1) -> print_endline "matched with bind in sub var";
                             let (p,c) = a1.term in
                             let p_vars = Pattern.pattern_vars (p.term) in
                             let p_vars_set = VariableSet.of_list p_vars in
                             if (List.mem vr p_vars) 
                                                then  begin 
                                                      print_endline "matched vr is member in p of bind)";
                                                      bind ~loc:loc (substitute_var_comp c1 vr exp) a1
                                                end
                                 else if ( VariableSet.equal (VariableSet.inter (p_vars_set) (free_vars_e exp)) VariableSet.empty )
                                      then 
                                            begin 
                                            bind ~loc:loc (substitute_var_comp c1 vr exp) (abstraction ~loc:loc p (substitute_var_comp c vr exp))
                                            end
                                      else begin 
                                          print_endline  "we do renaming in bind(should never happen) with ";

                                           let new_p= refresh_pattern p in 
                                           let new_pe = make_expression_from_pattern new_p in 
                                           let fresh_c = substitute_pattern_comp c (p.term) new_pe c in 
                                          (*Print.debug "renaming %t to %t in %t" (CamlPrint.print_variable vr) (CamlPrint.print_variable fvar) (CamlPrint.print_computation c); *)
                                           bind ~loc:loc (substitute_var_comp c1 vr exp)
                                           (abstraction ~loc:loc new_p ( substitute_var_comp fresh_c vr exp))
                                         end


          | LetIn (e, a) -> print_endline "matched with letin in sub var";
                            let (p,c) = a.term in
                            let p_vars = Pattern.pattern_vars (p.term) in
                            let p_vars_set = VariableSet.of_list p_vars in
                            if (List.mem vr p_vars) then  begin 
                                                      let_in ~loc:loc (substitute_var_exp e vr exp) a
                                                end
                            else if ( VariableSet.equal (VariableSet.inter (p_vars_set) (free_vars_e exp)) VariableSet.empty )
                                 then 
                                      begin 
                                       print_endline "matched vr is member in p of let in)";
                                      let_in ~loc:loc (substitute_var_exp e vr exp) (abstraction ~loc:loc p (substitute_var_comp c vr exp))
                                      end
                                 else begin 
                                      print_endline  "we do renaming from let_in with ";
                                      let new_p= refresh_pattern p in 
                                      let new_pe = make_expression_from_pattern new_p in 
                                      let fresh_c = substitute_pattern_comp c (p.term) new_pe c in 
                                      let_in ~loc:loc (substitute_var_exp e vr exp)
                                       (abstraction ~loc:loc new_p ( substitute_var_comp fresh_c vr exp))
                                  end

          end
and substitute_var_exp e vr exp = 
  (* Print.debug "Substituting %t" (CamlPrint.print_expression e); *)
    let loc = Location.unknown in
    begin match e.term with 
      | Var v -> print_endline "matched with var in sub var"; 
                 if (v == vr) then  begin (*Print.debug "Substituting %t to %t " (CamlPrint.print_variable vr) (CamlPrint.print_expression exp); *)exp end 
               else e
      | Tuple lst -> let func = fun a -> substitute_var_exp a vr exp in
                     tuple ~loc:loc (List.map func lst) 
      | Record lst -> record ~loc:loc (Common.assoc_map (fun a -> substitute_var_exp a vr exp)  lst)
      | Variant (label,ex) ->  let func = (fun a -> substitute_var_exp a vr exp) in
                                variant ~loc:loc (label, (Common.option_map func ex)) 
                           
      | Lambda a -> print_endline "matched with lambda in sub var";
                    (*Print.debug "searching for  %t in %t to be sub. to %t" (CamlPrint.print_variable vr) (CamlPrint.print_abstraction a) (CamlPrint.print_expression exp) ;*) 
                    let (p,c) = a.term in 
                    let p_vars = Pattern.pattern_vars (p.term) in
                    let p_vars_set = VariableSet.of_list p_vars in
                    if (List.mem vr p_vars) then  begin  print_endline "matched vr is member in p of lambda)";  e end
                                 else if ( VariableSet.equal (VariableSet.inter (p_vars_set) (free_vars_e exp)) VariableSet.empty )
                                      then 
                                            begin 

                                            lambda ~loc:loc (abstraction ~loc:loc p (substitute_var_comp c vr exp))
                                            end
                                      else begin 
                                          print_endline  "we do renaming in lambda with ";
                                           let new_p= refresh_pattern p in 
                                           let new_pe = make_expression_from_pattern new_p in 
                                           let fresh_c = substitute_pattern_comp c (p.term) new_pe c in 
                                           
                                           lambda ~loc:loc (abstraction ~loc:loc new_p 
                                                           ( substitute_var_comp fresh_c vr exp))
                                         end

      | Handler h ->  print_endline "matched with handler in sub var"; (substitute_var_handler h vr exp)


      | PureLambda pa -> print_endline "matched with pure_lambda in sub var";
                    let (p,e) = pa.term in
                    let p_vars = Pattern.pattern_vars (p.term) in
                    let p_vars_set = VariableSet.of_list p_vars in
                    if (List.mem vr p_vars) then  begin  print_endline "matched vr is member in p of purelambda)"; e end
                                 else if ( VariableSet.equal (VariableSet.inter (p_vars_set) (free_vars_e exp)) VariableSet.empty )
                                      then 
                                            begin 
                                            pure_lambda ~loc:loc (pure_abstraction ~loc:loc p (substitute_var_exp e vr exp))
                                            end
                                      else begin 
                                           let new_p= refresh_pattern p in 
                                           let new_pe = make_expression_from_pattern new_p in 
                                           let fresh_e = substitute_pattern_exp e (p.term) new_pe e in 
                                           pure_lambda ~loc:loc (pure_abstraction ~loc:loc new_p 
                                                           ( substitute_var_exp fresh_e vr exp))
                                         end
      | PureApply (e1,e2) ->  pure_apply ~loc:loc (substitute_var_exp e1 vr exp) (substitute_var_exp e2 vr exp)
      
      | PureLetIn (e,pa) ->  print_endline "matched with letin in sub var";
                            let (p,e') = pa.term in
                            let p_vars = Pattern.pattern_vars (p.term) in
                            let p_vars_set = VariableSet.of_list p_vars in
                            if (List.mem vr p_vars) then  begin 
                                                      pure_let_in ~loc:loc (substitute_var_exp e vr exp) pa
                                                end
                            else if ( VariableSet.equal (VariableSet.inter (p_vars_set) (free_vars_e exp)) VariableSet.empty )
                                 then 
                                      begin 
                                      pure_let_in ~loc:loc (substitute_var_exp e vr exp) (pure_abstraction ~loc:loc p (substitute_var_exp e' vr exp))
                                      end
                                 else begin 
                                      print_endline  "we do renaming with ";
                                      let new_p= refresh_pattern p in 
                                      let new_pe = make_expression_from_pattern new_p in 
                                      let fresh_e = substitute_pattern_exp e (p.term) new_pe e in 
                                      pure_let_in ~loc:loc (substitute_var_exp e vr exp)
                                       (pure_abstraction ~loc:loc new_p ( substitute_var_exp fresh_e vr exp))
                                  end
      
      | _ -> e
    end

and substitute_var_handler h vr exp = let loc = Location.unknown in
                                      let (pv,cv) = (h.value_clause).term in 
                                      let (pf,cf) = (h.finally_clause).term in
                                      let eff_list = h.effect_clauses in
                                      let new_value_lambda = 
                                          (substitute_var_exp (lambda ~loc:loc (abstraction ~loc:loc pv cv) ) vr exp) in
                                      let new_final_lambda = 
                                          (substitute_var_exp (lambda ~loc:loc (abstraction ~loc:loc pf cf ) ) vr exp) in

                                      let func = fun a -> let (e,ab2) = a in
                                                 let (p1,p2,ck) = ab2.term in
                                                 let new_exp = (substitute_var_exp (pure_lambda ~loc:loc 
                                                                  (pure_abstraction ~loc:loc p1 
                                                                  (lambda ~loc:loc (abstraction ~loc:loc p2 ck)))) vr exp) in
                                                 let PureLambda panew = new_exp.term  in
                                                 let (p1new,temp_exp1)  = panew.term in
                                                 let Lambda anew = temp_exp1.term in
                                                 let (p2new,cknew) = anew.term in
                                                 (e, (abstraction2 ~loc:loc p1new p2new cknew)) in
                                      begin match new_value_lambda.term with
                                      | Lambda new_value_abstraction -> 
                                                begin match new_final_lambda.term with
                                                | Lambda new_final_abstraction -> 
                                                     handler ~loc:loc
                                                     {
                                                       effect_clauses =  List.map func eff_list;
                                                       value_clause = new_value_abstraction;
                                                       finally_clause = new_final_abstraction
                                                     }
                                                | _ -> failwith "substitute_var_handler error."
                                                  
                                                end
                                      | _ -> failwith "substitute_var_handler error."
                                    end
                                      
  

and substitute_pattern_comp c p exp maincomp = 
                           begin match fst p with
                              | Pattern.Var x -> optimize_comp (substitute_var_comp c x exp)
                              | Pattern.As (_,x) -> 
                                                    let (xbo,xfo) = occurrences x c in
                                                    if(xbo == 0 && xfo == 1) then
                                                    optimize_comp (substitute_var_comp c x exp)
                                                    else
                                                       maincomp
                              | Pattern.Tuple [] when (exp.term = Tuple [])-> c
                              | Pattern.Tuple lst -> begin match exp.term with
                                                    | Tuple elst -> optimize_comp (List.fold_right2 (fun pat -> fun exp -> fun co -> substitute_pattern_comp  co pat exp maincomp) lst elst c)
                                                    | _ ->  maincomp
                                                    end
                              | Pattern.Record _ -> maincomp
                              | Pattern.Variant _ ->  maincomp
                              | Pattern.Const _ ->  maincomp
                              | Pattern.Nonbinding ->  maincomp
                            end



and substitute_pattern_exp e p exp mainexp =
                          begin match fst p with
                              | Pattern.Var x -> optimize_expr (substitute_var_exp e x exp)
                              | Pattern.As (p,x) -> let (xbo,xfo) = occurrences_e x e in
                                                    if(xbo == 0 && xfo == 1) then
                                                     optimize_expr (substitute_var_exp e x exp)
                                                    else
                                                       mainexp
                              | Pattern.Tuple [] when (exp.term = Tuple [])-> e
                              | Pattern.Tuple lst -> begin match exp.term with
                                                    | Tuple elst -> optimize_expr(List.fold_right2 (fun pat -> fun exp -> fun co -> substitute_pattern_exp  co pat exp mainexp) lst elst e)
                                                    | _ ->  mainexp
                                                    end
                              | Pattern.Record _ ->  mainexp
                              | Pattern.Variant _ ->  mainexp
                              | Pattern.Const _ -> mainexp
                              | Pattern.Nonbinding -> mainexp
                            end


and refresh_comp c = match c.term with
           | Bind (c1,c2) ->  let (pa,ca) = c2.term in 
                              let newpa = refresh_pattern pa in 
                              let newpa_e = make_expression_from_pattern newpa in  
                              let new_ca = substitute_pattern_comp ca (pa.term) newpa_e c in 
                              bind ~loc:c.location (refresh_comp c1) (abstraction ~loc:c.location newpa ( refresh_comp new_ca))
            
            | LetIn (e,a) -> let (pa,ca)= a.term in
                             let newpa = refresh_pattern pa in 
                             let newpa_e = make_expression_from_pattern newpa in  
                             let new_ca = substitute_pattern_comp ca (pa.term) newpa_e c in 
                             let_in ~loc:c.location (refresh_exp e) (abstraction ~loc:c.location newpa (refresh_comp new_ca))

            | Let (li,c1) -> let func = fun (pa,co) -> (pa, refresh_comp co ) in
                               let' ~loc:c.location (List.map func li) (refresh_comp c1 )
            | LetRec (li, c1) -> let_rec' ~loc:c.location (List.map (fun (v,abs)-> let (p,comp) = abs.term in
                                                                                   (v, abstraction ~loc:c.location p (optimize_comp comp )))
                                                                                   li)  (refresh_comp c1 )
            | Match (e, li) -> match' ~loc:c.location (refresh_exp e) li
            | While (c1, c2) -> while' ~loc:c.location (refresh_comp c1 ) (optimize_comp c2 )
            | For (v, e1, e2, c1, b) -> for' ~loc:c.location v (refresh_exp e1) (refresh_exp e2) (refresh_comp c1 ) b
            | Apply (e1, e2) -> apply ~loc:c.location (refresh_exp e1) (refresh_exp e2)
            | Handle (e, c1) -> handle ~loc:c.location (refresh_exp e) (optimize_comp c1 )
            | Check c1 -> check ~loc:c.location (refresh_comp c1 )
            | Call (eff, e1, a1) -> call ~loc:c.location eff (refresh_exp e1)  a1 
            | Value e -> value ~loc:c.location (refresh_exp e)

and refresh_exp e = begin match e.term with 
                    | PureLambda a -> let (pa,ea) = a.term in 
                                      let panew = refresh_pattern pa in
                                      let panew_e = make_expression_from_pattern panew in 
                                      pure_lambda ~loc:e.location (
                                              pure_abstraction ~loc:e.location
                                                  panew 
                                                  (refresh_exp ( substitute_pattern_exp ea (pa.term) panew_e ea )))
                    | Lambda a -> let (pa,ca) = a.term in 
                                      let panew = refresh_pattern pa in
                                      let panew_e = make_expression_from_pattern panew in 
                                      lambda ~loc:e.location (
                                              abstraction ~loc:e.location
                                                  panew 
                                                  (refresh_comp ( substitute_pattern_comp ca (pa.term) panew_e ca )))
                    | PureLetIn (e1,pa) ->
                                let (ppa,ea) = pa.term in 
                                let newppa = refresh_pattern ppa in 
                             let newppa_e = make_expression_from_pattern newppa in  
                             let new_ea = substitute_pattern_exp ea (ppa.term) newppa_e e in 
                             pure_let_in ~loc:e.location (refresh_exp e1) (pure_abstraction ~loc:e.location newppa (refresh_exp new_ea))
                    | Handler h -> refresh_handler e 
                    | BuiltIn f -> e
                    | Record lst -> record ~loc:e.location (Common.assoc_map refresh_exp lst)
                    | Variant (label,exp) -> variant ~loc:e.location ( label , Common.option_map refresh_exp exp)
                    | Tuple lst -> tuple ~loc:e.location (List.map refresh_exp lst)
                    | PureApply (e1, e2)-> pure_apply ~loc:e.location (refresh_exp e1) (refresh_exp e2)
                    | PureLetIn (e1, pa) -> pure_let_in ~loc:e.location (optimize_expr e1) (optimize_pure_abstraction pa)
                    |_ -> e
                    end

and refresh_handler e = 
          begin match e.term with 
          | Handler h -> 
              let loc = Location.unknown in
              let (pv,cv) = (h.value_clause).term in 
              let (pf,cf) = (h.finally_clause).term in
              let eff_list = h.effect_clauses in
              
              let new_value_pattern = refresh_pattern pv in 
              let new_value_pattern_e = make_expression_from_pattern new_value_pattern in 
              let new_cv = substitute_pattern_comp cv (pv.term) new_value_pattern_e cv  in 

              let new_f_pattern = refresh_pattern pf in 
              let new_f_pattern_e = make_expression_from_pattern new_f_pattern in 
              let new_cf = substitute_pattern_comp cf (pf.term) new_f_pattern_e cf  in 
                  
              let func = fun a -> let (e,ab2) = a in
                         let (p1,p2,ck) = ab2.term in
                       (*  let p1new = refresh_pattern p1 in
                         let p1new_e = make_expression_from_pattern p1new in 
                         let p2new = refresh_pattern p2 in 
                         let p2new_e = make_expression_from_pattern p2new in 
                         let cknew = substitute_pattern_comp ( substitute_pattern_comp ck (p2.term) p2new_e ck false) (p1.term) p1new_e ck false in
                         let lst = List.append (Pattern.pattern_vars (p1new.term)) (Pattern.pattern_vars (p2new.term)) in 
                         *)
                        let temp_lambda = refresh_exp(pure_lambda ~loc:loc (pure_abstraction ~loc:loc p1 (lambda ~loc:loc (abstraction ~loc:loc p2 ck)))) in 
                        let (PureLambda pura) = temp_lambda.term in
                        let (p1new,lterm) = pura.term in 
                        let (Lambda aa) = lterm.term in 
                        let (p2new,cknew) = aa.term in 
                      
                         (e, (abstraction2 ~loc:loc p1new p2new ( cknew ))) in

              let h' = {
                         effect_clauses = List.map func eff_list;
                         value_clause = abstraction ~loc:cv.location new_value_pattern new_cv;
                         finally_clause = abstraction ~loc:cf.location new_f_pattern new_cf
                         }
                          in handler ~loc:Location.unknown h'
              
          | _ -> e
        end


and  optimize_comp c  = shallow_opt ( opt_sub_comp c) 


and shallow_opt c =

  (*Print.debug "Shallow optimizing %t" (CamlPrint.print_computation c);*)
  match c.term with

  | Let (pclist,c2) ->  let bind_comps =  (folder pclist c2) in 
                         optimize_comp (bind_comps) 

  | Match (e,lst) -> begin match e.term with
                    | Const cc -> let func = (fun a -> let (p,clst) = a.term in 
                                              begin match (fst p.term) with
                                              | Pattern.Const cp when (cc = cp) -> true
                                              | _ -> false
                                              end) in
                                  begin match (List.find func lst) with
                                  | abs -> let (_,c')= abs.term in 
                                            c'
                                  | _ -> c
                                  end
                    | _ -> c
                    end
  | Bind (c1, c2) ->
    let (pa,ca ) = c2.term in
    begin match c1.term with
    (*Bind x (Value e) c -> LetC x e c*)
    | Value e ->  let res = (let_in ~loc:c.location e c2)in
                  shallow_opt res
    | Bind (c3,c4) -> let (p2,cp2) = c4.term in 
                      let res = (bind ~loc:c.location c3 (abstraction ~loc:c.location p2 
                                              (shallow_opt (bind ~loc:c.location cp2 (abstraction ~loc:c.location pa ca))  ))) in 
                      shallow_opt res
    | LetIn(e,a) ->let (pal,cal) = a.term in
                   let newbind = shallow_opt (bind ~loc:c.location cal c2) in 
                   let let_abs = abstraction ~loc:c.location pal newbind in
                   let res = let_in ~loc:c.location e let_abs in
                   shallow_opt res

    | Apply(e1,e2) -> begin match e1.term with
                     | Effect ef -> begin match ca.term with 
                                   | Apply(e3,e4) -> 
                                          begin match e4.term with 
                                          | Var x -> begin match e3.term with
                                                     | Lambda k -> begin match (fst pa.term)  with
                                                                   | Pattern.Var pv when (pv = x) ->
                                                                       let res = (call ~loc:c.location ef e2 k) in 
                                                                       shallow_opt res
                                                                   | _-> c
                                                                 end
                                                     | _-> c
                                                     end
                                          |  _ ->  c  
                                          end
                                   | _ -> c
                                   end
                     | _ -> c
                     end                                   
    
    | Handle(h,ch)-> begin match h.term with
                     | Handler h -> begin match ch.term with
                                    | Value ve ->
                                      if (is_pure_comp ch) then
                                        begin 
                                        let newlambda = lambda ~loc:c.location h.value_clause in
                                        let res = (apply ~loc:c.location newlambda ve) in 
                                        optimize_comp res
                                        end
                                      else c
                                    | _ ->c
                                   end
                     | _ -> c
                   end
    | Call(eff,e,k) ->  let loc = Location.unknown in
                        let( _ , (input_k_ty , _) , _ ) = k.scheme in
                        let vz = (make_var_from_counter (Scheme.simple input_k_ty)) in
                        let pz = make_pattern_from_var vz in
                        let (p_k,c_k) = k.term in 
                        let fpk = refresh_pattern p_k in 
                        let efpk = make_expression_from_pattern fpk in 
                        let fck = substitute_pattern_comp c_k (p_k.term) efpk c_k  in 
                        let k_lambda = shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc fpk fck)) in
                        let inner_apply = shallow_opt (apply ~loc:loc k_lambda vz)   in
                        let inner_bind = shallow_opt (bind ~loc:loc inner_apply (abstraction ~loc:loc pa ca))   in
                        let res =  (call ~loc:loc eff e (abstraction ~loc:loc pz inner_bind)) in 
                        shallow_opt res
    | _ -> c
    end

  | Handle (e1,c1) ->
    (*Print.debug "handler computation : %t" (CamlPrint.print_computation c1);*)
    begin match c1.term with

    (*Handle h (LetC x e c) -> LetC (x e) (Handle c h)*)
    | LetIn (e2,a) -> let (p,c2) = a.term in 
                      let res = let_in ~loc:c.location e2 (abstraction ~loc:c.location p (shallow_opt (handle ~loc:c.location e1 c2) )) in 
                      shallow_opt res
    
    | Value v -> begin match e1.term with
    
                 (*Handle (Handler vc ocs) (Value v) -> Apply (Lambda vc) v *)
                 | Handler h -> let res = (apply ~loc:c.location ( shallow_opt_e (lambda ~loc:c.location h.value_clause)) v) in 
                                shallow_opt res 
                                
                 | _-> c
                 end

    | Call (eff,exp,k) -> 
                          begin match e1.term with
                          | Handler h -> 
                                let loc = Location.unknown in
                                let z = Typed.Variable.fresh "z" in 
                                let( _ , (input_k_ty , _) , _ ) = k.scheme in
                                let pz = {
                                          term = (Pattern.Var z, loc);
                                          location = loc;
                                          scheme = Scheme.simple input_k_ty
                                        } in
                                let vz = var ~loc:loc z (Scheme.simple input_k_ty) in
                                let (p_k,c_k) = k.term in 
                                let fpk = refresh_pattern p_k in 
                                let efpk = make_expression_from_pattern fpk in 
                                let fck = substitute_pattern_comp c_k (p_k.term) efpk c_k in 
                                let k_lambda = shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc fpk fck)) in
                                let e2_apply = shallow_opt (apply ~loc:loc k_lambda vz) in
                                let fresh_handler = refresh_handler e1 in 
                                let e2_handle = shallow_opt (handle ~loc:loc fresh_handler e2_apply) in
                                let e2_lambda = shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc pz e2_handle)) in
                                begin match Common.lookup eff h.effect_clauses with
                                        | Some result -> 
                                         (*let (p1,p2,cresult) = result.term in
                                          let e1_lamda =  shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc p2 cresult)) in
                                          let e1_purelambda = shallow_opt_e (pure_lambda ~loc:loc (pure_abstraction ~loc:loc p1 e1_lamda)) in
                                          let e1_pureapply = shallow_opt_e (pure_apply ~loc:loc e1_purelambda exp) in
                                          shallow_opt (apply ~loc:loc e1_pureapply e2_lambda)
                                        *)
                                          let (p1,p2,cresult) = result.term in
                                          let fp1 = refresh_pattern p1 in 
                                          let fp2 = refresh_pattern p2 in 
                                          let efp1 = make_expression_from_pattern fp1 in 
                                          let efp2 = make_expression_from_pattern fp2 in 
                                          let fcresult = substitute_pattern_comp (substitute_pattern_comp cresult (p2.term) efp2 cresult ) (p1.term) efp1 cresult in 
                                          let e1_lamda =  shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc fp2 fcresult)) in
                                          let e1_lambda_sub = substitute_pattern_comp fcresult (fp2.term) e2_lambda (value ~loc:c.location vz)  in
                                          let e1_lambda = shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc fp1 e1_lambda_sub)) in
                                          let res = (apply ~loc:loc e1_lambda exp) in 
                                          shallow_opt res   
                                        

                                        | None ->
                                          let call_abst = abstraction ~loc:loc pz e2_handle in
                                          let res = (call ~loc:loc eff exp call_abst ) in
                                          shallow_opt res
                                        end
                          | _-> c
                          end
    | _ -> c
    end
  | Apply (e1,e2) ->
     begin match e1.term with
     (*Apply (PureLambda a) e -> Value (PureApply (PureLambda a) e)*)
     | Lambda a ->
          let (p,c') = a.term in
          (*WARNING : Adhoc to remove the unit pattern and sub. with a var pattern to make it work *)
          if is_atomic e2
            then 
            substitute_pattern_comp c' (p.term) e2 c

          else 
          let (pbo,pfo) = (pattern_occurrences p c') in
          if (pbo == 0 && pfo < 2) then
          begin
              if (pfo == 0) then c' 
            else 
                substitute_pattern_comp c' (p.term) e2 c 
              end
          else 
          begin match c'.term with 
          | Value v -> let res = (value ~loc:c.location @@ 
              shallow_opt_e (pure_apply ~loc:c.location (shallow_opt_e (pure_lambda ~loc:e1.location (pure_abstraction ~loc:a.location p v))) e2))
              in shallow_opt res 
          | _ -> c
          end
     | PureLambda pure_abs ->    let res = (value ~loc:c.location 
                                 (shallow_opt_e (pure_apply ~loc:c.location (shallow_opt_e (pure_lambda ~loc:c.location pure_abs)) e2 )))
                                 in shallow_opt res  
     | _ -> c
     end
  
  | LetIn (e,a) ->
     let (p,cp) = a.term in
      if is_atomic e then 
          (*Print.debug "from let in : sub %t \n to \n %t \n in \n %t "(CamlPrint.print_variable vp) (CamlPrint.print_expression e) (CamlPrint.print_computation cp);*)
          let cres = (substitute_pattern_comp cp (p.term) e c ) in 
           (*Print.debug "To get\n %t" (CamlPrint.print_computation cres);*)
           cres
      else
      begin match cp.term with
      | Value e2 -> let res = (value ~loc:c.location ( shallow_opt_e (pure_let_in ~loc:c.location e (pure_abstraction ~loc:c.location p e2))))
                    in shallow_opt res 

      | _ ->        let (occ_b,occ_f) = pattern_occurrences p cp in
                    if( occ_b == 0 && occ_f < 2)
                    then 
                      substitute_pattern_comp cp (p.term) e c
                    else
                      c
     
      end

  | _ -> c

and optimize_abstraction abs = let (p,c) = abs.term in abstraction ~loc:abs.location p (optimize_comp c) 


and optimize_pure_abstraction abs = let (p,e) = abs.term in pure_abstraction ~loc:abs.location p (optimize_expr e)

and folder pclist cn = 
    let func = fun a ->  fun b ->  (bind ~loc:b.location (snd a) (abstraction ~loc:b.location (fst a) b ) )
    in  List.fold_right func pclist cn

and  optimize_expr e = shallow_opt_e (opt_sub_expr e)

and shallow_opt_e e = 
      begin match e.term with 
      | PureLetIn (ex,pa) -> let (p,ep) = pa.term in
                             if is_atomic ex then 
                                substitute_pattern_exp ep (p.term) ex e
                             else
                              let (occ_b,occ_f) = pattern_occurrences_e p ep in
                              if( occ_b == 0 && occ_f < 2)
                              then 
                                substitute_pattern_exp ep (p.term) ex e
                              else
                                e 
    | PureApply (e1,e2) -> 
            begin match e1.term with 
            | PureLambda pa -> 
                let (p,e') = pa.term in
                if is_atomic e2 
                then 
                  substitute_pattern_exp e' (p.term) e2 e
                else
                  let (pbo,pfo) = (pattern_occurrences_e p e') in
                  if (pbo == 0 && pfo < 2) then
                  begin
                      if (pfo == 0) then e' 
                    else 
                        substitute_pattern_exp e' (p.term) e2 e
                      end
                else e
                
            | _ -> e
            end
      | Effect eff ->  let (eff_name, (ty_par, ty_res)) = eff in 
                   let param = make_var_from_counter (Scheme.simple ty_par) in
                   let result = make_var_from_counter (Scheme.simple ty_res) in
                   let res_pat = make_pattern_from_var result in
                   let param_pat = make_pattern_from_var param in
                   let kincall = abstraction ~loc:e.location res_pat (value ~loc:e.location result) in
                   let call_cons = shallow_opt (call ~loc:e.location eff param kincall) in
                   optimize_expr (lambda ~loc:e.location (abstraction ~loc:e.location param_pat call_cons))
      | _ -> e
      end

and opt_sub_comp c =
  (* Print.debug "Optimizing %t" (CamlPrint.print_computation c); *)
  match c.term with
  | Value e -> value ~loc:c.location (optimize_expr e)
  | Let (li,c1) -> let func = fun (pa,co) -> (pa, optimize_comp co ) in
                    let' ~loc:c.location (List.map func li) (optimize_comp c1 )
  | LetRec (li, c1) -> let_rec' ~loc:c.location (List.map (fun (v,abs)-> let (p,comp) = abs.term in
                                                                         (v, abstraction ~loc:c.location p (optimize_comp comp )))
                                                                         li)  (optimize_comp c1 )
  | Match (e, li) -> match' ~loc:c.location (optimize_expr e) (List.map optimize_abstraction li)
  | While (c1, c2) -> while' ~loc:c.location (optimize_comp c1 ) (optimize_comp c2 )
  | For (v, e1, e2, c1, b) -> for' ~loc:c.location v (optimize_expr e1) (optimize_expr e2) (optimize_comp c1 ) b
  | Apply (e1, e2) -> apply ~loc:c.location (optimize_expr e1) (optimize_expr e2)
  | Handle (e, c1) -> handle ~loc:c.location (optimize_expr e) (optimize_comp c1 )
  | Check c1 -> check ~loc:c.location (optimize_comp c1 )
  | Call (eff, e1, a1) -> call ~loc:c.location eff (optimize_expr e1) (optimize_abstraction a1) 
  | Bind (c1, a1) -> bind ~loc:c.location (optimize_comp c1 ) (optimize_abstraction a1)
  | LetIn (e, a) -> let_in ~loc: c.location(optimize_expr e) (optimize_abstraction a)

and opt_sub_expr e =
  (* Print.debug "Optimizing %t" (CamlPrint.print_expression e); *)
  match e.term with
  | Const c -> const ~loc:e.location c
  | BuiltIn f -> e
  | Record lst -> record ~loc:e.location (Common.assoc_map optimize_expr lst)
  | Variant (label,exp) -> variant ~loc:e.location ( label , Common.option_map optimize_expr exp)
  | Tuple lst -> tuple ~loc:e.location (List.map optimize_expr lst)
  | Lambda a -> lambda ~loc:e.location (optimize_abstraction a)
  | PureLambda pa -> pure_lambda ~loc:e.location (optimize_pure_abstraction pa)
  | PureApply (e1, e2)-> pure_apply ~loc:e.location (optimize_expr e1) (optimize_expr e2)
  | PureLetIn (e1, pa) -> pure_let_in ~loc:e.location (optimize_expr e1) (optimize_pure_abstraction pa)
  | Handler h -> optimize_handler h
  | Effect eff ->  e
  | Var x -> 
      begin match Common.lookup x !inlinable with
      | Some d -> refresh_exp d
      | _ -> e
      end



and optimize_handler h = let (pv,cv) = (h.value_clause).term in 
                         let (pf,cf) = (h.finally_clause).term in
                         let eff_list = h.effect_clauses in
                         let func = fun a -> let (e,ab2) = a in
                                             let (p1,p2,ca) = ab2.term in
                                             (e, abstraction2 ~loc:ca.location p1 p2 (optimize_comp ca )) in
                         let h' = {
                         effect_clauses = List.map func eff_list;
                         value_clause = abstraction ~loc:cv.location pv (optimize_comp cv );
                         finally_clause = abstraction ~loc:cf.location pf (optimize_comp cf )
                         }
                          in handler ~loc:Location.unknown h'

let optimize_command = function
  | Typed.Computation c ->
      Some (Typed.Computation (optimize_comp c))
  | Typed.TopLet (defs, vars) -> 
      let defs' = Common.assoc_map optimize_comp defs in
      begin match defs' with
      | [(p, c)] ->
         begin match fst (p.term) with
            |  Pattern.Var x -> 
            begin match c.term with 
                 | Value e -> begin match (e.term) with 
                              | Handler _ -> inlinable := Common.update x e !inlinable ;
                              | _ -> ()
                            end
                | _-> ()
                 end
            | _ -> ()
            end
      | _ -> ()
      end;
      Some (Typed.TopLet (defs', vars))
  | Typed.TopLetRec (defs, vars) ->
      Some (Typed.TopLetRec (Common.assoc_map optimize_abstraction defs, vars))
  | (Typed.DefEffect _ | Typed.Reset | Typed.Quit | Typed.Use _ | Typed.Tydef _) as cmd ->
      Some cmd
  | Typed.External (x, _, f) as cmd ->
      begin match Common.lookup f inlinable_definitions with
      | None -> Some cmd
      | Some e ->
          inlinable := Common.update x e !inlinable; Some cmd
      end
  | (Typed.TypeOf _ | Typed.Help) -> None

let rec optimize_commands = function
  | [] -> []
  | (cmd, loc) :: cmds ->
      let cmd = optimize_command cmd in
      let cmds = optimize_commands cmds in
      begin match cmd with
      | Some cmd -> (cmd, loc) :: cmds
      | None -> cmds
      end





