(*
 To Do list for optimization :

  ==> (done) optimize sub_computation (LetRec)
  ==> (done) Optimize sub_expression (Record/Variant) 
  ==> (done) Freevarse (Records/ Variants)
  ==> (done) Beta reduction with variables occur only once & not in a binder
      (let-in apply) (pure_let-in pure_apply) (bind)
  ==> (done) free_vars letrec
  ==> (done) occurrences (patterns/variants)
  ==> (done) fix all pattern matching warnings and not halt when pattern is not var (PRIORITY)
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

let a22a a2 = Typed.a22a a2
let pa2a pa = Typed.pa2a pa
let a2a2 a = Typed.a2a2 a
let a2pa a = Typed.a2pa a

let unary_inlinable f ty1 ty2 =
  let x = Typed.Variable.fresh "x" and loc = Location.unknown in
  let drt = Type.fresh_dirt () in
  let p =
    {
      term = Typed.PVar x;
      location = loc;
      scheme = Scheme.simple ty1;
    }
  in
    pure_lambda @@
    pure_abstraction p @@
      pure_apply
        (built_in f (Scheme.simple (Type.Arrow (ty1, (ty2, drt)))))
        (var x (Scheme.simple ty1))
  
let binary_inlinable f ty1 ty2 ty =
  let x1 = Typed.Variable.fresh "x1" and x2 = Typed.Variable.fresh "x2"
  and loc = Location.unknown and drt = Type.fresh_dirt () in
  let p1 =
    {
      term = Typed.PVar x1;
      location = loc;
      scheme = Scheme.simple ty1;
    }
  and p2 =
    {
      term = Typed.PVar x2;
      location = loc;
      scheme = Scheme.simple ty2;
    }
  in
    lambda @@
    abstraction p1 @@
      value @@
      lambda @@
      abstraction p2 @@
        value @@
          pure_apply
            (pure_apply
              (built_in f (Scheme.simple (Type.Arrow (ty1, ((Type.Arrow (ty2, (ty, drt))), drt)))))
              (var x1 (Scheme.simple ty1)))
            (var x2 (Scheme.simple ty2))
  
let inlinable_definitions =
  [ ("=",
     (fun () ->
        let t = Type.fresh_ty ()
        in binary_inlinable "Pervasives.(=)" t t Type.bool_ty));
    ("<",
     (fun () ->
        let t = Type.fresh_ty ()
        in binary_inlinable "Pervasives.(<)" t t Type.bool_ty));
    ("<>",
     (fun () ->
        let t = Type.fresh_ty ()
        in binary_inlinable "Pervasives.(<>)" t t Type.bool_ty));
    (">",
     (fun () ->
        let t = Type.fresh_ty ()
        in binary_inlinable "Pervasives.(>)" t t Type.bool_ty));
    ("~-",
     (fun () -> unary_inlinable "Pervasives.(~-)" Type.int_ty Type.int_ty));
    ("+",
     (fun () ->
        binary_inlinable "Pervasives.(+)" Type.int_ty Type.int_ty Type.int_ty));
    ("*",
     (fun () ->
        binary_inlinable "Pervasives.( * )" Type.int_ty Type.int_ty Type.
          int_ty));
    ("-",
     (fun () ->
        binary_inlinable "Pervasives.(-)" Type.int_ty Type.int_ty Type.int_ty));
    ("mod",
     (fun () ->
        binary_inlinable "Pervasives.(mod)" Type.int_ty Type.int_ty Type.
          int_ty));
    ("~-.",
     (fun () ->
        unary_inlinable "Pervasives.(~-.)" Type.float_ty Type.float_ty));
    ("+.",
     (fun () ->
        binary_inlinable "Pervasives.(+.)" Type.float_ty Type.float_ty Type.
          float_ty));
    ("*.",
     (fun () ->
        binary_inlinable "Pervasives.( *. )" Type.float_ty Type.float_ty
          Type.float_ty));
    ("-.",
     (fun () ->
        binary_inlinable "Pervasives.(-.)" Type.float_ty Type.float_ty Type.
          float_ty));
    ("/.",
     (fun () ->
        binary_inlinable "Pervasives.(/.)" Type.float_ty Type.float_ty Type.
          float_ty));
    ("/",
     (fun () ->
        binary_inlinable "Pervasives.(/)" Type.int_ty Type.int_ty Type.int_ty));
    ("float_of_int",
     (fun () ->
        unary_inlinable "Pervasives.(float_of_int)" Type.int_ty Type.float_ty));
    ("^",
     (fun () ->
        binary_inlinable "Pervasives.(^)" Type.string_ty Type.string_ty Type.
          string_ty));
    ("string_length",
     (fun () ->
        unary_inlinable "Pervasives.(string_length)" Type.string_ty Type.
          int_ty)) ]
  
let inlinable = ref []

let stack = ref []

let impure_wrappers = ref []

let find_inlinable x =
  match Common.lookup x !inlinable with
  | Some e -> Some (e ())
  | None -> None

let find_in_stack x =
  match Common.lookup x !stack with
  | Some e -> Some (e ())
  | None -> None
 

let rec make_expression_from_pattern p =
    let loc = p.location in
    match p.term with
    | Typed.PVar z -> var ~loc z p.scheme
    | Typed.PTuple [] -> tuple ~loc []
    | Typed.PAs (c, x) -> var ~loc x p.scheme
    | Typed.PTuple lst ->
        tuple ~loc (List.map make_expression_from_pattern lst)
    | Typed.PRecord flds ->
        record ~loc (Common.assoc_map make_expression_from_pattern flds)
    | Typed.PVariant (lbl, p) ->
        variant ~loc
          (lbl, (Common.option_map make_expression_from_pattern p))
    | Typed.PConst c -> const ~loc c
    | (Typed.PNonbinding as p) -> tuple ~loc []
  
let make_var_from_counter ann scheme =
  let x = Typed.Variable.fresh ann in var ~loc:Location.unknown x scheme
  
let make_pattern_from_var v =
  let (Var va) = v.term
  in
    {
      term = Typed.PVar va;
      location = Location.unknown;
      scheme = v.scheme;
    }
  
let refresh_pattern p = snd (Typed.refresh_pat [] p)

module VariableSet =
  Set.Make(struct type t = variable
                   let compare = Pervasives.compare
                      end)

let (@@@) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)
let (---) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)
let concat_vars vars = List.fold_right (@@@) vars ([], [])

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_exp e
  | Let (li, cf) ->
      let xs, vars = List.fold_right (fun (p, c) (xs, vars) ->
        Typed.pattern_vars p, free_vars_comp c @@@ vars
      ) li ([], ([], [])) in
      vars @@@ (free_vars_comp cf --- xs)
  | LetRec (li, c1) ->
      let xs, vars = List.fold_right (fun (x, a) (xs, vars) ->
        x :: xs, free_vars_abs a @@@ vars
      ) li ([], free_vars_comp c1) in
      vars --- xs
  | Match (e, li) -> free_vars_exp e @@@ concat_vars (List.map free_vars_abs li)
  | While (c1, c2) -> free_vars_comp c1 @@@ free_vars_comp c2
  | For (v, e1, e2, c1, b) ->
      (free_vars_exp e1 @@@ free_vars_exp e2 @@@ free_vars_comp c1) --- [v]
  | Apply (e1, e2) -> free_vars_exp e1 @@@ free_vars_exp e2
  | Handle (e, c1) -> free_vars_exp e @@@ free_vars_comp c1
  | Check c1 -> free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_exp e1 @@@ free_vars_abs a1
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
  | LetIn (e, a) -> free_vars_exp e @@@ free_vars_abs a
and free_vars_exp e =
  match e.term with
  | Var v -> ([], [v])
  | Tuple es -> concat_vars (List.map free_vars_exp es)
  | Lambda a -> free_vars_abs a
  | Handler h -> free_vars_handler h
  | Record flds -> concat_vars (List.map (fun (_, e) -> free_vars_exp e) flds)
  | Variant (_, None) -> ([], [])
  | Variant (_, Some e) -> free_vars_exp e
  | PureLambda pa -> free_vars_pure_abs pa
  | PureApply (e1, e2) -> free_vars_exp e1 @@@ free_vars_exp e2
  | PureLetIn (e, pa) -> free_vars_exp e @@@ free_vars_pure_abs pa
  | (BuiltIn _ | Effect _ | Const _) -> ([], [])
and free_vars_handler h =
  free_vars_abs h.value_clause @@@
  free_vars_abs h.finally_clause @@@
  concat_vars (List.map (fun (_, a2) -> free_vars_abs2 a2) h.effect_clauses)
and free_vars_abs a =
  let (p, c) = a.term in
  let (inside, outside) = free_vars_comp c --- Typed.pattern_vars p in
  (inside @ outside, [])
and free_vars_pure_abs pa = free_vars_abs @@ pa2a @@ pa
and free_vars_abs2 a2 = free_vars_abs @@ a22a @@ a2

let occurrences x (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x = y) ys) in
  (count inside, count outside)

(* XXX Most likely, this function should never be used *)
let pattern_occurrences p vars =
  List.fold_right (fun x (inside_occ, outside_occ) ->
    let (inside_occ_x, outside_occ_x) = occurrences x vars in
    (inside_occ + inside_occ_x, outside_occ + outside_occ_x)
  ) (Typed.pattern_vars p) (0, 0)

let replaceable x vars =
  let (inside_occ, outside_occ) = occurrences x vars in
  outside_occ <= 1 && inside_occ = 0

let only_inlinable_occurrences p c =
  let vars = free_vars_comp c in
  List.for_all (fun x -> replaceable x vars) (Typed.pattern_vars p)
  
  
let print_free_vars c =
  (print_endline "in free vars print ";
   let fvc = free_vars_comp c
   in
     (Print.debug "free vars of  %t  is" (CamlPrint.print_computation c);
      VariableSet.iter
        (fun v -> Print.debug "free var :  %t" (CamlPrint.print_variable v))
        (VariableSet.of_list (fst fvc @ snd fvc))))
  
let is_atomic e =
  match e.term with | Var _ -> true | Const _ -> true | _ -> false

let refresh_abs a = Typed.refresh_abs [] a
let refresh_exp e = Typed.refresh_exp [] e
let refresh_comp c = Typed.refresh_comp [] c
let refresh_handler h = Typed.refresh_handler [] h

let substitute_var_comp comp vr exp = Typed.subst_comp [(vr, exp.term)] comp
let substitute_var_exp e vr exp = Typed.subst_exp [(vr, exp.term)] e

let rec substitute_pattern_comp c p exp =
  optimize_comp (Typed.subst_comp (Typed.match_values p exp []) c)
and substitute_pattern_exp e p exp =
  optimize_expr (Typed.subst_exp (Typed.match_values p exp []) e)
and optimize_comp c = shallow_opt (opt_sub_comp c)
and shallow_opt c =
  (*Print.debug "Shallow optimizing %t" (CamlPrint.print_computation c);*)
  match c.term with
  | Let (pclist, c2) ->
      let bind_comps = folder pclist c2 in optimize_comp bind_comps
  | Match ({term = Const cc}, lst) ->
     let func a =
       let (p, clst) = a.term
       in
         (match p.term with
          | Typed.PConst cp when cc = cp -> true
          | _ -> false)
     in
       (match List.find func lst with
        | abs -> let (_, c') = abs.term in c'
        | _ -> c)
  | Bind ({term = Value e}, c2) ->
     let res = let_in ~loc:c.location e c2 in
     shallow_opt res
  | Bind ({term = Bind (c1, {term = (p2, c2)})}, c3) ->
     let res =
       bind ~loc:c.location c1 (abstraction p2 (shallow_opt (bind c2 c3)))
     in
     shallow_opt res
  | Bind ({term = LetIn (e, {term = (p1, c1)})}, c2) ->
     let newbind = shallow_opt (bind c1 c2) in
     let let_abs = abstraction p1 newbind in
     let res = let_in ~loc: c.location e let_abs in
     shallow_opt res
  | Bind (
      {term = Apply({term = Effect eff}, e_param)},
      {term = {term = Typed.PVar y}, {term = Apply ({term = Lambda k}, {term = Var x})}}
    ) when y = x ->
      let res = call ~loc: c.location eff e_param k in
      shallow_opt res
  | Bind ({term = Call (eff, e, k)}, {term = (pa, ca)}) ->
     let (_, (input_k_ty, _), _) = k.scheme in
     let vz =
       make_var_from_counter "_call_result"
         (Scheme.simple input_k_ty) in
     let pz = make_pattern_from_var vz in
     let k_lambda =
       shallow_opt_e
         (lambda (refresh_abs k)) in
     let inner_apply = shallow_opt (apply k_lambda vz) in
     let inner_bind =
       shallow_opt
         (bind inner_apply (abstraction pa ca)) in
     let res =
       call eff e (abstraction pz inner_bind)
     in shallow_opt res
  | Handle (e1, {term = LetIn (e2, a)}) ->
       let (p, c2) = a.term in
       let res =
         let_in ~loc: c.location e2
           (abstraction ~loc: c.location p
              (shallow_opt (handle ~loc: c.location e1 c2)))
       in shallow_opt res
  | Handle (e1, {term = Apply (ae1, ae2)}) ->
      begin match ae1.term with
      | Var v ->
            begin match find_in_stack v with
              | Some d -> 
                begin match d.term with
                | Lambda ({term = (dp,dc)}) ->
                    let new_var = make_var_from_counter "newvar" ae1.scheme in
                    let new_computation = apply ~loc:c.location (new_var) (ae2) in
                    let new_handle = handle ~loc:c.location e1 (substitute_var_comp dc v (refresh_exp d)) in
                    let new_lambda = lambda ~loc:c.location (abstraction ~loc:c.location dp new_handle) in 
                    optimize_comp (let_in ~loc:c.location new_lambda 
                          (abstraction ~loc:c.location (make_pattern_from_var new_var) (new_computation)))
                | _ -> c
                end
              |_ -> c
            end
      | PureApply ({term = Var fname} as pae1,pae2)->
            begin match find_in_stack fname with
              | Some d -> 
                begin match d.term with
                | PureLambda ({term = (dp1,{term = Lambda ({term = (dp2,dc)})})} as da) ->
                   let newfname = make_var_from_counter "newvar" ae1.scheme in
                   let pure_application = pure_apply ~loc:c.location newfname pae2 in
                   let application = apply ~loc:c.location pure_application ae2 in
                   let handler_call = handle ~loc:c.location e1 dc in 
                   let newfinnerlambda = lambda ~loc:c.location (abstraction ~loc:c.location dp2 handler_call) in 
                   let newfbody = pure_lambda ~loc:c.location (pure_abstraction dp1 newfinnerlambda) in 
                   let res = 
                     let_in ~loc:c.location (newfbody) (abstraction ~loc:c.location (make_pattern_from_var newfname) application) in
                   optimize_comp res
                   
                | _ -> c
              end
              | _ -> c
            end
      | _ -> c
      end

  | Handle ({term = Handler h}, {term = Value v}) ->
      let res =
        apply ~loc: c.location
          (shallow_opt_e (lambda ~loc: c.location h.value_clause))
          v
      in shallow_opt res
  | Handle ({term = Handler h}, {term = Call (eff, exp, k)}) ->
    let loc = Location.unknown in
    let z = Typed.Variable.fresh "z" in
    let (_, (input_k_ty, _), _) = k.scheme in
    let pz =
      {
        term = Typed.PVar z;
        location = loc;
        scheme = Scheme.simple input_k_ty;
      } in
    let vz = var ~loc z (Scheme.simple input_k_ty) in
    let k_lambda =
      shallow_opt_e
        (lambda ~loc (refresh_abs k)) in
    let e2_apply = shallow_opt (apply ~loc k_lambda vz) in
    let fresh_handler = refresh_handler h in
    let e2_handle =
      shallow_opt (handle ~loc (handler fresh_handler) e2_apply) in
    let e2_lambda =
      shallow_opt_e
        (lambda ~loc (abstraction ~loc pz e2_handle))
    in
      (match Common.lookup eff h.effect_clauses with
       | Some result ->
           (*let (p1,p2,cresult) = result.term in
                              let e1_lamda =  shallow_opt_e (lambda ~loc:loc (abstraction ~loc:loc p2 cresult)) in
                              let e1_purelambda = shallow_opt_e (pure_lambda ~loc:loc (pure_abstraction ~loc:loc p1 e1_lamda)) in
                              let e1_pureapply = shallow_opt_e (pure_apply ~loc:loc e1_purelambda exp) in
                              shallow_opt (apply ~loc:loc e1_pureapply e2_lambda)
                            *)
           let (p1, p2, cresult) = result.term in
           let fp1 = refresh_pattern p1 in
           let fp2 = refresh_pattern p2 in
           let efp1 = make_expression_from_pattern fp1 in
           let efp2 = make_expression_from_pattern fp2 in
           let fcresult =
             substitute_pattern_comp
               (substitute_pattern_comp cresult p2 efp2)
               p1 efp1 in
           let e1_lamda =
             shallow_opt_e
               (lambda ~loc
                  (abstraction ~loc fp2 fcresult)) in
           let e1_lambda_sub =
             substitute_pattern_comp fcresult fp2 e2_lambda in
           let e1_lambda =
             shallow_opt_e
               (lambda ~loc
                  (abstraction ~loc fp1 e1_lambda_sub)) in
           let res = apply ~loc e1_lambda exp
           in shallow_opt res
       | None ->
           let call_abst = abstraction ~loc pz e2_handle in
           let res = call ~loc eff exp call_abst
           in shallow_opt res)
  | Apply ({term = Lambda {term = (p, c')}}, e) when is_atomic e ->
      substitute_pattern_comp c' p e
  | Apply ({term = Lambda {term = (p, c')}}, e) ->
     (let (pbo, pfo) = pattern_occurrences p (free_vars_comp c')
      in
        if (pbo == 0) && (pfo < 2)
        then
          if pfo == 0
          then c'
          else substitute_pattern_comp c' p e
        else
          (match c'.term with
           | Value v ->
               let res =
                 (value ~loc: c.location) @@
                   (shallow_opt_e
                      (pure_apply ~loc: c.location
                         (shallow_opt_e
                            (pure_lambda
                               (pure_abstraction p
                                  v)))
                         e))
               in shallow_opt res
           | _ -> c))
  | Apply ({term = PureLambda pure_abs}, e2) ->
       let res =
         value ~loc:c.location
           (shallow_opt_e
              (pure_apply ~loc: c.location
                 (shallow_opt_e (pure_lambda ~loc: c.location pure_abs))
                 e2))
       in shallow_opt res
  
  | Apply( {term = (Var v)} as e1, e2) ->
    begin match (List.find_all (fun a -> (fst a).term = e1.term) !impure_wrappers) with
    | [(fo,fn)]-> 
          let pure_app = shallow_opt_e (pure_apply ~loc:c.location fn e2) in 
          let main_value = shallow_opt (value ~loc:c.location pure_app) in
          main_value
    | _ -> c
    end

  | LetIn (e, {term = (p, cp)}) when is_atomic e ->
      Print.debug "We are now in the let in 1 for %t" (CamlPrint.print_expression (make_expression_from_pattern p));
      substitute_pattern_comp cp p e
  | LetIn (e1, {term = (p, {term = Value e2})}) ->
    Print.debug "We are now in the let in 2 for %t" (CamlPrint.print_expression (make_expression_from_pattern p));
     let res =
       value ~loc:c.location
         (shallow_opt_e (pure_let_in e1 (pure_abstraction p e2)))
     in shallow_opt res

  | LetIn (e, {term = (p, cp)}) when only_inlinable_occurrences p cp ->
  Print.debug "We are now in the let in 3 for %t" (CamlPrint.print_expression (make_expression_from_pattern p));
       substitute_pattern_comp cp p e
  
  (*Matching let f = \x.\y. c *)    
  | LetIn({term = Lambda ({term = (pe1, {term = Value ({term = Lambda ({term = (pe2,ce2)}) } as in_lambda)} )})} as e, {term = ({term = PVar fo} as p,cp)} )->
        Print.debug "We are now in the let in 4 for %t" (CamlPrint.print_expression (make_expression_from_pattern p));
        let new_var = make_var_from_counter "newvar" p.scheme in
        let new_var2 = make_var_from_counter "newvar2" pe1.scheme in 
        let new_pattern = make_pattern_from_var new_var2 in
        let pure_application = pure_apply ~loc:c.location new_var new_var2 in
        let second_let_value = value ~loc:c.location pure_application in 
        let second_let_lambda = lambda ~loc:c.location (abstraction ~loc:c.location new_pattern second_let_value) in
        let second_let = let_in ~loc:c.location second_let_lambda (abstraction ~loc:c.location p cp) in
        let outer_lambda = pure_lambda ~loc:c.location (pure_abstraction pe1 in_lambda) in
        let first_let_abstraction = abstraction ~loc:c.location (make_pattern_from_var new_var) second_let in
        let first_let = let_in ~loc:c.location (outer_lambda) first_let_abstraction in
        impure_wrappers:= ((make_expression_from_pattern p),new_var) :: !impure_wrappers;
        optimize_comp first_let
  | LetIn(e, {term = (p,cp)} )->
      Print.debug "We are now in the let in 5 for %t" (CamlPrint.print_expression (make_expression_from_pattern p));
        begin 
          (match p.term with
          | Typed.PVar xx -> 
              Print.debug "Added to stack ==== %t" (CamlPrint.print_variable xx);
              stack:= Common.update xx (fun () -> e) !stack     
          | _ -> Print.debug "We are now in the let in 5 novar for %t" (CamlPrint.print_expression (make_expression_from_pattern p));()
          );
        let_in ~loc:c.location e (abstraction ~loc:e.location p (optimize_comp cp))
        end
  | LetRec(l,co) -> Print.debug "the letrec comp%t" (CamlPrint.print_computation co); c
  | _ -> c


and optimize_abstraction abs =
  let (p, c) = abs.term in abstraction ~loc: abs.location p (optimize_comp c)
and optimize_pure_abstraction abs =
  let (p, e) = abs.term
  in pure_abstraction ~loc: abs.location p (optimize_expr e)
and folder pclist cn =
  let func a b =
    bind ~loc: b.location (snd a) (abstraction ~loc: b.location (fst a) b)
  in List.fold_right func pclist cn
and optimize_expr e = shallow_opt_e (opt_sub_expr e)
and shallow_opt_e e =
  match e.term with
  | PureLetIn (ex, pa) ->
      let (p, ep) = pa.term
      in
        if is_atomic ex
        then substitute_pattern_exp ep p ex
        else
          (let (occ_b, occ_f) = pattern_occurrences p (free_vars_exp ep)
           in
             if (occ_b == 0) && (occ_f < 2)
             then substitute_pattern_exp ep p ex
             else e)
  | PureApply ({term = PureLambda {term = (p, e')}}, e2) ->
     if is_atomic e2
     then substitute_pattern_exp e' p e2
     else
       (let (pbo, pfo) = pattern_occurrences p (free_vars_exp e')
        in
          if (pbo == 0) && (pfo < 2)
          then
            if pfo == 0
            then e'
            else substitute_pattern_exp e' p e2
          else e)
  | Effect eff ->
      let (eff_name, (ty_par, ty_res)) = eff in
      let param = make_var_from_counter "param" (Scheme.simple ty_par) in
      let result = make_var_from_counter "result" (Scheme.simple ty_res) in
      let res_pat = make_pattern_from_var result in
      let param_pat = make_pattern_from_var param in
      let kincall =
        abstraction ~loc: e.location res_pat (value ~loc: e.location result) in
      let call_cons = shallow_opt (call ~loc: e.location eff param kincall)
      in
        optimize_expr
          (lambda ~loc: e.location
             (abstraction ~loc: e.location param_pat call_cons))
  | _ -> e
and opt_sub_comp c =
  (* Print.debug "Optimizing %t" (CamlPrint.print_computation c); *)
  match c.term with
  | Value e -> value ~loc: c.location (optimize_expr e)
  | Let (li, c1) ->
      let func (pa, co) = (pa, (optimize_comp co))
      in let' ~loc: c.location (List.map func li) (optimize_comp c1)
  | LetRec (li, c1) ->
      let_rec' ~loc: c.location
        (List.map
           (fun (v, abs) ->
              let (p, comp) = abs.term
              in (v, (abstraction ~loc: c.location p (optimize_comp comp))))
           li)
        (optimize_comp c1)
  | Match (e, li) ->
      match' ~loc: c.location (optimize_expr e)
        (List.map optimize_abstraction li)
  | While (c1, c2) ->
      while' ~loc: c.location (optimize_comp c1) (optimize_comp c2)
  | For (v, e1, e2, c1, b) ->
      for' ~loc: c.location v (optimize_expr e1) (optimize_expr e2)
        (optimize_comp c1) b
  | Apply (e1, e2) ->
      apply ~loc: c.location (optimize_expr e1) (optimize_expr e2)
  | Handle (e, c1) ->
      handle ~loc: c.location (optimize_expr e) (optimize_comp c1)
  | Check c1 -> check ~loc: c.location (optimize_comp c1)
  | Call (eff, e1, a1) ->
      call ~loc: c.location eff (optimize_expr e1) (optimize_abstraction a1)
  | Bind (c1, a1) ->
      bind ~loc: c.location (optimize_comp c1) (optimize_abstraction a1)
  | LetIn (e, a) ->
      let_in ~loc: c.location (optimize_expr e) (optimize_abstraction a)
and opt_sub_expr e =
  (* Print.debug "Optimizing %t" (CamlPrint.print_expression e); *)
  match e.term with
  | Const c -> const ~loc: e.location c
  | BuiltIn f -> e
  | Record lst ->
      record ~loc: e.location (Common.assoc_map optimize_expr lst)
  | Variant (label, exp) ->
      variant ~loc: e.location (label, (Common.option_map optimize_expr exp))
  | Tuple lst -> tuple ~loc: e.location (List.map optimize_expr lst)
  | Lambda a -> lambda ~loc: e.location (optimize_abstraction a)
  | PureLambda pa ->
      pure_lambda ~loc: e.location (optimize_pure_abstraction pa)
  | PureApply (e1, e2) ->
      pure_apply ~loc: e.location (optimize_expr e1) (optimize_expr e2)
  | PureLetIn (e1, pa) ->
      pure_let_in ~loc: e.location (optimize_expr e1)
        (optimize_pure_abstraction pa)
  | Handler h -> optimize_handler h
  | Effect eff -> e
  | Var x ->
      (begin match find_inlinable x with
       | Some d -> (match d.term with | Handler _ -> refresh_exp d | _ -> d)
       | _ -> e
     end )
and optimize_handler h =
  let (pv, cv) = h.value_clause.term in
  let (pf, cf) = h.finally_clause.term in
  let eff_list = h.effect_clauses in
  let func a =
    let (e, ab2) = a in
    let (p1, p2, ca) = ab2.term
    in (e, (abstraction2 ~loc: ca.location p1 p2 (optimize_comp ca))) in
  let h' =
    {
      effect_clauses = List.map func eff_list;
      value_clause = abstraction ~loc: cv.location pv (optimize_comp cv);
      finally_clause = abstraction ~loc: cf.location pf (optimize_comp cf);
    }
  in handler ~loc:Location.unknown h'
  
let optimize_command =
  function
  | Typed.Computation c ->
      Typed.Computation (optimize_comp c)
  | Typed.TopLet (defs, vars) ->
      let defs' = Common.assoc_map optimize_comp defs in
      begin match defs' with
      (* If we define a single simple handler, we inline it *)
      | [({ term = Typed.PVar x}, { term = Value ({ term = Handler _ } as e)})] ->
        inlinable := Common.update x (fun () -> e) !inlinable
      | [({ term = Typed.PVar x}, ({ term = Value ({term = Lambda ({term = (pc,cc)}) } as e )} ))] ->
        stack := Common.update x (fun () -> e) !stack
      | _ -> ()
      end;
      Typed.TopLet (defs', vars)
  | Typed.TopLetRec (defs, vars) ->
      Typed.TopLetRec (Common.assoc_map optimize_abstraction defs, vars)
  | Typed.External (x, _, f) as cmd ->
      begin match Common.lookup f inlinable_definitions with
      (* If the external function is one of the predefined inlinables, we inline it *)
      | Some e -> inlinable := Common.update x e !inlinable
      | None -> ()
      end;
      cmd
  | Typed.DefEffect _ | Typed.Reset | Typed.Quit | Typed.Use _
  | Typed.Tydef _ | Typed.TypeOf _ | Typed.Help as cmd -> cmd
  
let optimize_commands cmds =
  List.map (fun (cmd, loc) -> (optimize_command cmd, loc)) cmds
