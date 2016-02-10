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

let inlinable_definitions =
  [("+", binary_inlinable "Pervasives.(+)" Type.int_ty Type.int_ty Type.int_ty)]

let inlinable = ref []


and make_var_from_pattern p =   let (Pattern.Var z) = fst (p.term) in
                                var ~loc:p.location z p.scheme


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


module VariableSet = Set.Make(
  struct
    type t = variable
    let compare = Pervasives.compare
  end
  )

let rec free_vars_c c : VariableSet.t = 
  begin match c.term with 
  | Value e -> free_vars_e e
  | Let (li,cf) -> let func = fun a ->  fun b ->  
                                let (Var vp1) = (make_var_from_pattern (fst a)).term in
                                VariableSet.union (VariableSet.remove vp1 (free_vars_c (snd a))) b
                      in VariableSet.union (free_vars_c cf) (List.fold_right func li VariableSet.empty)
  
  | LetRec (li, c1) -> free_vars_let_rec li c1 (* still not fully implmented*)
  

  | Match (e, li) -> failwith "found a match in free vars, not handled yet"
  | While (c1, c2) -> VariableSet.union (free_vars_c c1) (free_vars_c c2)
  | For (v, e1, e2, c1, b) -> VariableSet.remove v (free_vars_c c1)
  | Apply (e1, e2) -> VariableSet.union (free_vars_e e1) (free_vars_e e2)
  | Handle (e, c1) -> VariableSet.union (free_vars_e e) (free_vars_c c1)
  | Check c1 -> free_vars_c c1
  | Call (eff, e1, a1) -> let (p1,cp1) = a1.term in
                           let (Var vp1) = (make_var_from_pattern p1).term in
                            VariableSet.union (free_vars_e e1) (VariableSet.remove vp1 (free_vars_c cp1))
  | Bind (c1, a1) -> let (p1,cp1) = a1.term in
                           let (Var vp1) = (make_var_from_pattern p1).term in
                            VariableSet.union (free_vars_c c1) (VariableSet.remove vp1 (free_vars_c cp1))
  | LetIn (e, a) -> let (p1,cp1) = a.term in
                           let (Var vp1) = (make_var_from_pattern p1).term in
                            VariableSet.union (free_vars_e e) (VariableSet.remove vp1 (free_vars_c cp1))
  end

and free_vars_e e : VariableSet.t = 
  begin match e.term with 
  | Var v  -> VariableSet.singleton v
  | Const _ -> VariableSet.empty
  | Tuple lst -> List.fold_right VariableSet.union (List.map free_vars_e lst ) VariableSet.empty
  | Lambda a -> let (p1,cp1) = a.term in
                           let (Var vp1) = (make_var_from_pattern p1).term in
                            VariableSet.remove vp1 (free_vars_c cp1)
  | Handler h -> free_vars_handler h
  (*  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option *)
  | PureLambda pa -> let (p1,ep1) = pa.term in
                           let (Var vp1) = (make_var_from_pattern p1).term in
                            VariableSet.remove vp1 (free_vars_e ep1)
  | PureApply (e1,e2) -> VariableSet.union (free_vars_e e1) (free_vars_e e2)
  | PureLetIn (e,pa) -> let (p1,ep1) = pa.term in
                           let (Var vp1) = (make_var_from_pattern p1).term in
                            VariableSet.union (free_vars_e e) (VariableSet.remove vp1 (free_vars_e ep1))
  | BuiltIn _ -> VariableSet.empty
  | _ -> failwith "free vars matched a record or a variant, not handled yet ";
    end

and free_vars_let_rec li c1 : VariableSet.t = VariableSet.empty
and free_vars_handler h : VariableSet.t = let (pv,cv) = (h.value_clause).term in 
                                          let (pf,cf) = (h.finally_clause).term in
                                          let eff_list = h.effect_clauses in
                                          let (Var pv1) = (make_var_from_pattern pv).term in
                                          let (Var pf1) = (make_var_from_pattern pf).term in
                                          let func = fun a -> fun b ->
                                                    let (p1,p2,c) = (snd a).term in 
                                                    let (Var pv1) = (make_var_from_pattern p1).term in 
                                                    let (Var pv2) = (make_var_from_pattern p2).term in 
                                          VariableSet.union (VariableSet.remove pv1 (VariableSet.remove pv2  (free_vars_c c))) b
                                          in
                                          VariableSet.union ( VariableSet.union 
                                                                (VariableSet.remove pv1 (free_vars_c cv)) 
                                                                (VariableSet.remove pf1 (free_vars_c cf) ))
                                                            (List.fold_right func eff_list VariableSet.empty)  



let print_free_vars c = print_endline "in free vars print ";
  let fvc = free_vars_c c in 
  Print.debug "free vars of  %t  is" (CamlPrint.print_computation c);
  (VariableSet.iter (fun v -> (Print.debug "free var :  %t" (CamlPrint.print_variable v)))) fvc 

let is_atomic e = begin match e.term with 
                    | Var _ -> true
                    | Const _ -> true
                    | _ -> false
                  end


let rec substitute_var_comp comp vr exp =
(*   Print.debug "Substituting %t" (CamlPrint.print_computation comp); *)
        let loc = Location.unknown in
        begin match comp.term with
          | Value e -> value ~loc:loc (substitute_var_exp e vr exp)
          | Let (li,cf) ->  let' ~loc:loc li cf
          | LetRec (li, c1) -> failwith "substitute_var_comp for let_rec not implemented"
          | Match (e, li) -> failwith "substitute_var_comp for match not implemented"
          | While (c1, c2) -> while' ~loc:loc (substitute_var_comp c1 vr exp) (substitute_var_comp c2 vr exp)
          | For (v, e1, e2, c1, b) -> for' ~loc:loc v (substitute_var_exp e1 vr exp) (substitute_var_exp e2 vr exp) (substitute_var_comp c1 vr exp) b
          | Apply (e1, e2) -> apply ~loc:loc (substitute_var_exp e1 vr exp) (substitute_var_exp e2 vr exp)
          | Handle (e, c1) -> handle ~loc:loc (substitute_var_exp e vr exp) (substitute_var_comp c1 vr exp)
          | Check c1 -> check ~loc:loc (substitute_var_comp c1 vr exp)
          | Call (eff, e1, a1) -> call ~loc:loc eff (substitute_var_exp e1 vr exp )  a1
          
          | Bind (c1, a1) -> print_endline "matched with bind in sub var";
                             let (p,c) = a1.term in
                             let (Var v) = (make_var_from_pattern p).term in
                             if (v == vr) then  begin print_endline "pattern = variable" ; 
                                                      bind ~loc:loc (substitute_var_comp c1 vr exp) a1
                                                end
                                 else if not( VariableSet.mem v (free_vars_e exp) )
                                      then 
                                            begin 
                                            print_endline " apply sub (not in free vars)";
                                            bind ~loc:loc (substitute_var_comp c1 vr exp) (abstraction ~loc:loc p (substitute_var_comp c vr exp))
                                            end
                                      else begin 
                                          print_endline  "we do renaming with ";
                                           let fresh_var = make_var_from_counter p.scheme in
                                           let fresh_pattern = make_pattern_from_var fresh_var in
                                           
                                           bind ~loc:loc (substitute_var_comp c1 vr exp)
                                           (abstraction ~loc:loc fresh_pattern ( substitute_var_comp (substitute_var_comp c v fresh_var) vr exp))
                                         end


          | LetIn (e, a) -> print_endline "matched with letin in sub var";
                            let (p,c) = a.term in
                            let (Var v) = (make_var_from_pattern p).term in
                            if (v == vr) then  begin print_endline "pattern = variable" ; 
                                                      let_in ~loc:loc (substitute_var_exp e vr exp) a
                                                end
                            else if not( VariableSet.mem v (free_vars_e exp) )
                                 then 
                                      begin 
                                      print_endline " apply sub (not in free vars)";
                                      let_in ~loc:loc (substitute_var_exp e vr exp) (abstraction ~loc:loc p (substitute_var_comp c vr exp))
                                      end
                                 else begin 
                                      print_endline  "we do renaming with ";
                                      let fresh_var = make_var_from_counter p.scheme in
                                      let fresh_pattern = make_pattern_from_var fresh_var in
                                      let_in ~loc:loc (substitute_var_exp e vr exp)
                                       (abstraction ~loc:loc fresh_pattern ( substitute_var_comp (substitute_var_comp c v fresh_var) vr exp))
                                  end

          end
and substitute_var_exp e vr exp = 
  (* Print.debug "Substituting %t" (CamlPrint.print_expression e); *)
    let loc = Location.unknown in
    begin match e.term with 
      | Var v -> if (v == vr) then (print_endline "did a sub" ; exp) else var ~loc:loc v e.scheme
      | Tuple lst -> let func = fun a -> substitute_var_exp a vr exp in
                     tuple ~loc:loc (List.map func lst) 
      | Lambda a -> print_endline "matched with lambda in sub var";
                    let (p,c) = a.term in
                    let (Var v) = (make_var_from_pattern p).term in
                    if (v == vr) then  begin print_endline "pattern = variable" ; e end
                                 else if not( VariableSet.mem v (free_vars_e exp) )
                                      then 
                                            begin 
                                            print_endline " apply sub (not in free vars)";
                                            lambda ~loc:loc (abstraction ~loc:loc p (substitute_var_comp c vr exp))
                                            end
                                      else begin 
                                          print_endline  "we do renaming with ";
                                           let fresh_var = make_var_from_counter p.scheme in
                                           let fresh_pattern = make_pattern_from_var fresh_var in
                                           
                                           lambda ~loc:loc (abstraction ~loc:loc fresh_pattern 
                                                           ( substitute_var_comp (substitute_var_comp c v fresh_var) vr exp))
                                         end

   (*   | Handler of handler *)
      | PureLambda pa -> print_endline "matched with pure_lambda in sub var";
                    let (p,e) = pa.term in
                    let (Var v) = (make_var_from_pattern p).term in
                    print_free_vars (value ~loc:Location.unknown exp) ;
                    if (v == vr) then  begin print_endline "pattern = variable" ; e end
                                 else if not( VariableSet.mem v (free_vars_e exp) )
                                      then 
                                            begin 
                                            print_endline " apply sub (not in free vars)";
                                            pure_lambda ~loc:loc (pure_abstraction ~loc:loc p (substitute_var_exp e vr exp))
                                            end
                                      else begin 
                                           let fresh_var = make_var_from_counter p.scheme in 
                                           let (Var fv) = fresh_var.term in
                                           let fresh_pattern = make_pattern_from_var fresh_var in
                                           let (Var var_old_pattern) = (make_var_from_pattern p).term in 
                                           Print.debug "we do renaming from %t  to %t" ( CamlPrint.print_variable var_old_pattern )(CamlPrint.print_variable fv);
                                           pure_lambda ~loc:loc (pure_abstraction ~loc:loc fresh_pattern 
                                                           ( substitute_var_exp (substitute_var_exp e v fresh_var) vr exp))
                                         end
      | PureApply (e1,e2) -> pure_apply ~loc:loc (substitute_var_exp e1 vr exp) (substitute_var_exp e2 vr exp)
      
      | PureLetIn (e,pa) ->  print_endline "matched with letin in sub var";
                            let (p,e') = pa.term in
                            let (Var v) = (make_var_from_pattern p).term in
                            if (v == vr) then  begin print_endline "pattern = variable" ; 
                                                      pure_let_in ~loc:loc (substitute_var_exp e vr exp) pa
                                                end
                            else if not( VariableSet.mem v (free_vars_e exp) )
                                 then 
                                      begin 
                                      print_endline " apply sub (not in free vars)";
                                      pure_let_in ~loc:loc (substitute_var_exp e vr exp) (pure_abstraction ~loc:loc p (substitute_var_exp e' vr exp))
                                      end
                                 else begin 
                                      print_endline  "we do renaming with ";
                                      let fresh_var = make_var_from_counter p.scheme in
                                      let fresh_pattern = make_pattern_from_var fresh_var in
                                      pure_let_in ~loc:loc (substitute_var_exp e vr exp)
                                       (pure_abstraction ~loc:loc fresh_pattern ( substitute_var_exp (substitute_var_exp e' v fresh_var) vr exp))
                                  end
      
      | _ -> e
    end



let rec optimize_comp c = shallow_opt ( opt_sub_comp c)

and shallow_opt c = 
   (*Print.debug "Shallow optimizing %t" (CamlPrint.print_computation c);*)
  match c.term with

  | Let (pclist,c2) ->  optimize_comp (folder pclist c2)
  
  | Bind (c1, c2) ->
    let (pa,ca) = c2.term in
    begin match c1.term with
    (*Bind x (Value e) c -> LetC x e c*)
    | Value e ->  shallow_opt(let_in ~loc:c.location e c2)
    | Bind (c3,c4) -> let (pa,ca) = c2.term in 
                      let (p2,cp2) = c4.term in 
                      shallow_opt (bind ~loc:c.location c1 (abstraction ~loc:c.location p2 
                                              (shallow_opt (bind ~loc:c.location cp2 (abstraction ~loc:c.location pa ca)))))
    | LetIn(e,a) ->let (pal,cal) = a.term in
                   let newbind = shallow_opt (bind ~loc:c.location cal c2) in 
                   let let_abs = abstraction ~loc:c.location pal newbind in
                   shallow_opt (let_in ~loc:c.location e let_abs)

    | Apply(e1,e2) -> let (pa,ca) = c2.term in
                      begin match e1.term with
                     | Effect ef -> begin match ca.term with 
                                   | Apply(e3,e4) -> 
                                          begin match e4.term with 
                                          | Var x -> begin match e3.term with
                                                     | Lambda k -> begin match (fst pa.term)  with
                                                                   | Pattern.Var pv when (pv = x) ->
                                                                       shallow_opt (call ~loc:c.location ef e2 k)
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
    

    | Call(eff,e,k) ->  let (pa,ca) = c2.term in
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
                        let k_lambda = lambda ~loc:loc (abstraction ~loc:loc p_k c_k) in
                        let inner_apply = shallow_opt (apply ~loc:loc k_lambda vz) in
                        let inner_bind = shallow_opt (bind ~loc:loc inner_apply (abstraction ~loc:loc pa ca)) in
                        shallow_opt (call ~loc:loc eff e (abstraction ~loc:loc pz inner_bind))
    | _ -> c
    end

  | Handle (e1,c1) ->
    begin match c1.term with

    (*Handle h (LetC x e c) -> LetC (x e) (Handle c h)*)
    | LetIn (e2,a) -> let (p,c2) = a.term in 
                     shallow_opt(
                      let_in ~loc:c.location e2 (abstraction ~loc:c.location p (shallow_opt (handle ~loc:c.location e1 c2)))
                    )
    
    | Value v -> begin match e1.term with
    
                 (*Handle (Handler vc ocs) (Value v) -> Apply (Lambda vc) v *)
                 | Handler h -> shallow_opt(
                                apply ~loc:c.location (lambda ~loc:c.location h.value_clause) v)
                 | _-> c
                 end

    | Call (eff,exp,k) -> begin match e1.term with
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
                                let k_lambda = lambda ~loc:loc (abstraction ~loc:loc p_k c_k) in
                                let e2_apply = shallow_opt (apply ~loc:loc k_lambda vz) in
                                let e2_handle = shallow_opt (handle ~loc:loc e1 e2_apply) in
                                let e2_lambda = lambda ~loc:loc (abstraction ~loc:loc pz e2_handle) in
                                begin match Common.lookup eff h.effect_clauses with
                                        | Some result -> 
                                          let (p1,p2,cresult) = result.term in
                                          let e1_lamda =  lambda ~loc:loc (abstraction ~loc:loc p2 cresult) in
                                          let e1_purelambda = pure_lambda ~loc:loc (pure_abstraction ~loc:loc p1 e1_lamda) in
                                          let e1_pureapply = pure_apply ~loc:loc e1_purelambda exp in
                                          shallow_opt (apply ~loc:loc e1_pureapply e2_lambda)

                                        | None ->
                                          let call_abst = abstraction ~loc:loc pz e2_handle in
                                          shallow_opt (call ~loc:loc eff exp call_abst )
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
          if is_atomic e2 
            then  
                let Pattern.Var vp = (fst p.term) in
                let tempvar = var ~loc:c.location  vp p.scheme in
                let Var v = tempvar.term in
                optimize_comp (substitute_var_comp c' v e2)
          else 
          begin match c'.term with 
          | Value v -> shallow_opt (value ~loc:c.location @@ 
              pure_apply ~loc:c.location (pure_lambda ~loc:e1.location (pure_abstraction ~loc:a.location p v)) e2)
          | _ -> c
          end
     | PureLambda pure_abs ->    shallow_opt (value ~loc:c.location 
                                 (pure_apply ~loc:c.location (pure_lambda ~loc:c.location pure_abs) e2 ))
     | _ -> c
     end
  
  | LetIn (e,a) ->
     let (p,cp) = a.term in
      if is_atomic e then 
          let (Var vp) = (make_var_from_pattern p).term in
          substitute_var_comp cp vp e
      else 
      begin match cp.term with
      | Value e2 -> shallow_opt (value ~loc:c.location (pure_let_in ~loc:c.location e (pure_abstraction ~loc:c.location p e2)))
      | _ -> c
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
                                let (Var vp) = (make_var_from_pattern p).term in
                                substitute_var_exp ep vp ex
                             else
                               e 
      | PureApply (e1,e2) -> 
            begin match e1.term with 
            | PureLambda pa -> 
                let (p,e') = pa.term in
                if is_atomic e2 
                then  
                    let Pattern.Var vp = (fst p.term) in
                    let tempvar = var ~loc:e.location  vp p.scheme in
                    let Var v = tempvar.term in
                    optimize_expr (substitute_var_exp e' v e2) 
                else
                  e
            | _ -> e
            end
      | _ -> e
      end

and opt_sub_comp c =
  (* Print.debug "Optimizing %t" (CamlPrint.print_computation c); *)
  match c.term with
  | Value e -> value ~loc:c.location (optimize_expr e)
  | Let (li,c1) -> let func = fun (pa,co) -> (pa, optimize_comp co) in
                    let' ~loc:c.location (List.map func li) (optimize_comp c1)
  | LetRec (li, c1) -> let_rec' ~loc:c.location li (optimize_comp c1)
  | Match (e, li) -> match' ~loc:c.location (optimize_expr e) li
  | While (c1, c2) -> while' ~loc:c.location (optimize_comp c1) (optimize_comp c2)
  | For (v, e1, e2, c1, b) -> for' ~loc:c.location v (optimize_expr e1) (optimize_expr e2) (optimize_comp c1) b
  | Apply (e1, e2) -> apply ~loc:c.location (optimize_expr e1) (optimize_expr e2)
  | Handle (e, c1) -> handle ~loc:c.location (optimize_expr e) (optimize_comp c1)
  | Check c1 -> check ~loc:c.location (optimize_comp c1)
  | Call (eff, e1, a1) -> call ~loc:c.location eff (optimize_expr e1) (optimize_abstraction a1) 
  | Bind (c1, a1) -> bind ~loc:c.location (optimize_comp c1) (optimize_abstraction a1)
  | LetIn (e, a) -> let_in ~loc: c.location(optimize_expr e) (optimize_abstraction a)

and opt_sub_expr e =
  (* Print.debug "Optimizing %t" (CamlPrint.print_expression e); *)
  match e.term with
  | Const c -> const ~loc:e.location c
  | BuiltIn f -> built_in ~loc:e.location f e.scheme
  | Tuple lst -> tuple ~loc:e.location (List.map optimize_expr lst)
  | Lambda a -> lambda ~loc:e.location (optimize_abstraction a)
  | PureLambda pa -> pure_lambda ~loc:e.location (optimize_pure_abstraction pa)
  | PureApply (e1, e2)-> pure_apply ~loc:e.location (optimize_expr e1) (optimize_expr e2)
  | PureLetIn (e1, pa) -> pure_let_in ~loc:e.location (optimize_expr e1) (optimize_pure_abstraction pa)
  | Handler h -> optimize_handler h
  | Effect eff -> effect ~loc:e.location eff
  | Var x -> 
      begin match Common.lookup x !inlinable with
      | Some e -> opt_sub_expr e
      | _ -> e
      end
  | _ -> failwith "matched record or variant in optimize sub expression. Not handled yet, or just an effect"



and optimize_handler h = let (pv,cv) = (h.value_clause).term in 
                         let (pf,cf) = (h.finally_clause).term in
                         let eff_list = h.effect_clauses in
                         let func = fun a -> let (e,ab2) = a in
                                             let (p1,p2,ca) = ab2.term in
                                             (e, abstraction2 ~loc:ca.location p1 p2 (optimize_comp ca)) in
                         let h' = {
                         effect_clauses = List.map func eff_list;
                         value_clause = abstraction ~loc:cv.location pv (optimize_comp cv);
                         finally_clause = abstraction ~loc:cf.location pf (optimize_comp cf)
                         }
                          in handler ~loc:Location.unknown h'

let optimize_command = function
  | Typed.Computation c ->
      Some (Typed.Computation (optimize_comp c))
  | Typed.TopLet (defs, vars) ->
      Some (Typed.TopLet (Common.assoc_map optimize_comp defs, vars))
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





