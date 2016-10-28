(*
 To Do list for optimization :

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

let letrec_memory = ref []

let handlers_functions_mem = ref []

let impure_wrappers = ref []

let find_inlinable x =
  match Common.lookup x !inlinable with
  | Some e -> Some (e ())
  | None -> None

let find_in_stack x =
  match Common.lookup x !stack with
  | Some e -> Some (e ())
  | None -> None


let find_in_let_rec_mem v =
  let findres = List.filter ( fun (var,a) ->  if(var == v) then true else false) !letrec_memory in
  begin match findres with
  | [] -> None
  | [(vr,ab)] -> Some ab
  end

let find_in_handlers_func_mem f_name h_exp =
  let findres = List.filter
                  (fun (h,old_f,new_f) -> (f_name == old_f) && alphaeq_expr [] h h_exp) !handlers_functions_mem in
  begin match findres with
  | [] -> None
  | [(_,_,newf)] -> Some newf
  end

let make_var ?(loc=Location.unknown) ann scheme =
  let x = Typed.Variable.fresh ann in
  let x_var = var ~loc x scheme
  and x_pat = {
    term = Typed.PVar x;
    location = loc;
    scheme = scheme
  } in
  x_var, x_pat

type inlinability =
  | NotInlinable (* Pattern variables occur more than once or inside a binder *)
  | NotPresent (* Pattern variables are not present in the body *)
  | Inlinable (* Pattern variables occur each at most once outside a binder *)

let applicable_pattern p vars =
  let rec check_variables = function
    | [] -> NotPresent
    | x :: xs ->
      let inside_occ, outside_occ = Typed.occurrences x vars in
      if inside_occ > 0 || outside_occ > 1 then
        NotInlinable
      else
        begin match check_variables xs with
          | NotPresent -> if outside_occ = 0 then NotPresent else Inlinable
          | inlinability -> inlinability
        end
  in
  check_variables (Typed.pattern_vars p)

let is_atomic e =
  match e.term with | Var _ -> true | Const _ -> true | _ -> false

let refresh_abs a = Typed.refresh_abs [] a
let refresh_abs2 a2 = Typed.refresh_abs2 [] a2
let refresh_expr e = Typed.refresh_expr [] e
let refresh_comp c = Typed.refresh_comp [] c
let refresh_handler h = Typed.refresh_handler [] h

let substitute_var_comp comp vr exp = Typed.subst_comp [(vr, exp.term)] comp

let rec substitute_pattern_comp c p exp =
  optimize_comp (Typed.subst_comp (Typed.pattern_match p exp) c)
and substitute_pattern_expr e p exp =
  optimize_expr (Typed.subst_expr (Typed.pattern_match p exp) e)


and hasEffectsInCommon c h =
    (* Print.debug "%t" (CamlPrint.print_computation_effects c1); *)
    let rec hasCommonEffects l1 l2 =
        match l1 with
            | [] -> false
            | (h1,_)::t1 -> (
                match l2 with
                    | [] -> false
                    | ((h2,(_,_)),_)::t2 when h1 = h2 -> true
                    | ((h2,(_,_)),_)::t2 -> (hasCommonEffects t1 l2) || (hasCommonEffects l1 t2)
            ) in
    let get_dirt (_,(_,dirt),_) = dirt in
    hasCommonEffects (get_dirt (c.Typed.scheme)).Type.ops h.effect_clauses

and beta_reduce ({term = (p, c)} as a) e =
  match applicable_pattern p (Typed.free_vars_comp c) with
  | NotInlinable when is_atomic e -> substitute_pattern_comp c p e
  | Inlinable -> substitute_pattern_comp c p e
  | NotPresent -> c
  | _ ->
    let a =
      begin match p with
        | {term = Typed.PVar x} ->
          Print.debug "Added to stack ==== %t" (CamlPrint.print_variable x);
          stack := Common.update x (fun () -> e) !stack;
          abstraction p (optimize_comp c)
        | _ ->
          Print.debug "We are now in the let in 5 novar for %t" (Typed.print_pattern p);
          a
      end
    in
    let_in e a

and pure_beta_reduce ({term = (p, exp)} as pa) e =
  match applicable_pattern p (Typed.free_vars_expr exp) with
  | NotInlinable when is_atomic e -> substitute_pattern_expr exp p e
  | Inlinable -> substitute_pattern_expr exp p e
  | NotPresent -> exp
  | _ ->
    let pa =
      begin match p with
        | {term = Typed.PVar x} ->
          Print.debug "Added to stack ==== %t" (CamlPrint.print_variable x);
          stack := Common.update x (fun () -> e) !stack;
          pure_abstraction p (optimize_expr e)
        | _ ->
          Print.debug "We are now in the let in 5 novar for %t" (Typed.print_pattern p);
          pa
      end
    in
    pure_let_in e pa

and optimize_expr e = reduce_expr (optimize_sub_expr e)
and optimize_comp c = reduce_comp (optimize_sub_comp c)

and optimize_sub_expr e =
  (* Print.debug "Optimizing %t" (CamlPrint.print_expression e); *)
  let loc = e.location in
  match e.term with
  | Record lst ->
    record ~loc (Common.assoc_map optimize_expr lst)
  | Variant (lbl, e) ->
    variant ~loc (lbl, (Common.option_map optimize_expr e))
  | Tuple lst ->
    tuple ~loc (List.map optimize_expr lst)
  | Lambda a ->
    lambda ~loc (optimize_abs a)
  | PureLambda pa ->
    pure_lambda ~loc (optimize_pure_abs pa)
  | PureApply (e1, e2) ->
    pure_apply ~loc (optimize_expr e1) (optimize_expr e2)
  | PureLetIn (e1, pa) ->
    pure_let_in ~loc (optimize_expr e1) (optimize_pure_abs pa)
  | Handler h ->
    handler ~loc {
      effect_clauses = Common.assoc_map optimize_abs2 h.effect_clauses;
      value_clause = optimize_abs h.value_clause;
      finally_clause = optimize_abs h.finally_clause;
    }
  | (Var _ | Const _ | BuiltIn _ | Effect _) -> e
and optimize_sub_comp c =
  (* Print.debug "Optimizing %t" (CamlPrint.print_computation c); *)
  let loc = c.location in
  match c.term with
  | Value e ->
    value ~loc (optimize_expr e)
  | Let (li, c1) ->
    let' ~loc (Common.assoc_map optimize_comp li) (optimize_comp c1)
  | LetRec (li, c1) ->
    let_rec' ~loc (Common.assoc_map optimize_abs li) (optimize_comp c1)
  | Match (e, li) ->
    match' ~loc (optimize_expr e) (List.map optimize_abs li)
  | While (c1, c2) ->
    while' ~loc (optimize_comp c1) (optimize_comp c2)
  | For (v, e1, e2, c1, b) ->
    for' ~loc v (optimize_expr e1) (optimize_expr e2) (optimize_comp c1) b
  | Apply (e1, e2) ->
    apply ~loc (optimize_expr e1) (optimize_expr e2)
  | Handle (e, c1) ->
    handle ~loc (optimize_expr e) (optimize_comp c1)
  | Check c1 ->
    check ~loc (optimize_comp c1)
  | Call (eff, e1, a1) ->
    call ~loc eff (optimize_expr e1) (optimize_abs a1)
  | Bind (c1, a1) ->
    bind ~loc (optimize_comp c1) (optimize_abs a1)
  | LetIn (e, a) ->
    let_in ~loc (optimize_expr e) (optimize_abs a)
and optimize_abs {term = (p, c); location = loc} =
  abstraction ~loc p (optimize_comp c)
and optimize_pure_abs pa = a2pa @@ optimize_abs @@ pa2a @@ pa
and optimize_abs2 a2 = a2a2 @@ optimize_abs @@ a22a @@ a2

and reduce_expr e =
  match e.term with

  | Var x ->
    begin match find_inlinable x with
      | Some ({term = Handler _} as d) -> reduce_expr (refresh_expr d)
      | Some d -> reduce_expr d
      | _ -> e
    end

  | PureLetIn (ex, pa) ->
    pure_beta_reduce pa ex

  | PureApply ({term = PureLambda pa}, e2) ->
    pure_beta_reduce pa e2

  | Effect eff ->
    let (eff_name, (ty_par, ty_res)) = eff in
    let param_var, param_pat = make_var "param" (Scheme.simple ty_par) in
    let result_var, result_pat = make_var "result" (Scheme.simple ty_res) in
    let k = abstraction result_pat (value result_var) in
    let call_eff_param_var_k = reduce_comp (call eff param_var k) in
    let res =
      lambda (abstraction param_pat call_eff_param_var_k)
    in
    (* Body is already reduced and it's a lambda *)
    res

  | _ -> e

and reduce_comp c =
  (*Print.debug "Shallow optimizing %t" (CamlPrint.print_computation c);*)
  match c.term with

  (* Convert simultaneous let into a sequence of binds *)
  | Let (defs, c) ->
    let binds = List.fold_right (fun (p_def, c_def) binds ->
        bind c_def (abstraction p_def binds)
      ) defs c in
    reduce_comp binds

  | Match ({term = Const cst}, cases) ->
    let rec find_const_case = function
      | [] -> c
      | ({term = {term = PConst cst'}, c'}) :: _ when Const.equal cst cst' -> c'
      | _ :: cases -> find_const_case cases
    in
    find_const_case cases

  | Bind ({term = Value e}, c) ->
    beta_reduce c e

  | Bind ({term = Bind (c1, {term = (p1, c2)})}, c3) ->
    let bind_c2_c3 = reduce_comp (bind c2 c3) in
    let res =
      bind c1 (abstraction p1 bind_c2_c3)
    in
    reduce_comp res

  | Bind ({term = LetIn (e1, {term = (p1, c2)})}, c3) ->
    let bind_c2_c3 = reduce_comp (bind c2 c3) in
    let res =
      let_in e1 (abstraction p1 (bind_c2_c3))
    in
    reduce_comp res

  | Bind ({term = Call (eff, param, k)}, c) ->
    let {term = (k_pat, k_body)} = refresh_abs k in
    let bind_k_c = reduce_comp (bind k_body c) in
    let res =
      call eff param (abstraction k_pat bind_k_c)
    in
    reduce_comp res

  | Handle (h, {term = LetIn (e, {term = (p, c)})}) ->
    let handle_h_c = reduce_comp (handle h c) in
    let res =
      let_in e (abstraction p (handle_h_c))
    in
    reduce_comp res

  | Handle ({term = Handler h}, c1) when (not (hasEffectsInCommon c1 h)) ->
    Print.debug "Remove handler, keep handler since no effects in common with computation";
    reduce_comp (bind c1 h.value_clause)

  | Handle ({term = Handler h} as handler, {term = Bind (c1, {term = (p1, c2)})}) when  (not (hasEffectsInCommon c1 h)) ->
    Print.debug "Remove handler of outer Bind, keep handler since no effects in common with computation";
    reduce_comp (bind (reduce_comp c1) (abstraction p1 (reduce_comp (handle (refresh_expr handler) c2))))

  | Handle ({term = Handler h}, {term = Value v}) ->
    beta_reduce h.value_clause v

  | Handle ({term = Handler h} as handler, {term = Call (eff, param, k)}) ->
    let {term = (k_pat, k_body)} = refresh_abs k in
    let handled_k =
      abstraction k_pat
        (reduce_comp (handle (refresh_expr handler) k_body))
    in
    begin match Common.lookup eff h.effect_clauses with
      | Some eff_clause ->
        let {term = (p1, p2, c)} = refresh_abs2 eff_clause in
        (* Shouldn't we check for inlinability of p1 and p2 here? *)
        substitute_pattern_comp (substitute_pattern_comp c p1 param) p2 (lambda handled_k)
      | None ->
        let res =
          call eff param handled_k
        in
        reduce_comp res
    end

  | Apply ({term = Lambda a}, e) ->
    beta_reduce a e

  | Apply ({term = PureLambda pa}, e2) ->
    value (pure_beta_reduce pa e2)

  | Apply ({term = Var v}, e2) ->
    begin match Common.lookup v !impure_wrappers with
      | Some f ->
        let res =
          value (pure_apply f e2)
        in
        reduce_comp res
      | None -> c
    end

  | LetIn (e1, {term = (p, {term = Value e2})}) ->
    Print.debug "We are now in the let in 2 for %t" (Typed.print_pattern p);
    let res =
      value (pure_let_in e1 (pure_abstraction p e2))
    in
    reduce_comp res

  | Handle (e1, {term = Match (e2, cases)}) ->
    let push_handler = fun {term = (p, c)} ->
      abstraction p (reduce_comp (handle (refresh_expr e1) c))
    in
    let res =
      match' e2 (List.map push_handler cases)
    in
    res

  | Handle (e1, {term = Apply (ae1, ae2)}) ->
    begin match ae1.term with
      | Var v ->
        begin match find_in_stack v with
          | Some ({term = Lambda {term = (dp, dc)}} as d) ->
            (* let f_var, f_pat = make_var "newvar" ae1.scheme in
            let f_def =
              lambda @@
              abstraction dp @@
              handle e1 (substitute_var_comp dc v (refresh_expr d))
            in
            let res =
              let_in f_def @@
              abstraction f_pat @@
              apply f_var ae2
            in
            optimize_comp res *)
            c
          | _ -> begin match (find_in_handlers_func_mem v e1) with
                 | Some new_f_exp ->
                                    let res = apply new_f_exp ae2
                                    in reduce_comp res
                 | _ ->
                       begin match (find_in_let_rec_mem v) with
                       | Some abs ->
                                    let (let_rec_p,let_rec_c) = abs.term in
                                    let new_f_var, new_f_pat = make_var "newvar" ae1.scheme in
                                    let new_handler_call = handle e1 let_rec_c in
                                    let v_pat = {
                                              term = Typed.PVar v;
                                              location = c.location;
                                              scheme = ae1.scheme
                                            } in
                                    let Var newfvar = new_f_var.term in
                                    let defs = [(newfvar, (abstraction let_rec_p new_handler_call ))] in
                                    handlers_functions_mem:= (e1,v,new_f_var) :: !handlers_functions_mem ;
                                    let res =
                                      let_rec' defs @@
                                      apply new_f_var ae2
                                    in
                                    optimize_comp res
                       | None -> c
                       end
               end
        end
      | PureApply ({term = Var fname}, pae2)->
        begin match find_in_stack fname with
          | Some {term = PureLambda {term = (dp1, {term = Lambda ({term = (dp2,dc)})})}} ->
            let f_var, f_pat = make_var "newvar" ae1.scheme in
            let f_def =
              pure_lambda @@
              pure_abstraction dp1 @@
              lambda @@
              abstraction dp2 @@
              (* Why don't we refresh dc here? *)
              handle e1 dc
            in
            let res =
              let_in f_def @@
              abstraction f_pat @@
              apply (pure_apply f_var pae2) ae2
            in
            optimize_comp res
          | _ -> c
        end
      | _ -> c
    end



    (*
      let f = \p. val lambda in c
       ~~> (append f := f1 to impure_wrappers)
      let f1 = \*p. lambda
      let f = \new_p. val (f1 new_p) in
      c
    *)
  | LetIn ({term = Lambda ({term = (p, {term = Value ({term = Lambda _ } as in_lambda)} )})}, ({term = ({term = PVar f} as f_pat,_)} as a) )->
    Print.debug "We are now in the let in 4 for %t" (Typed.print_pattern f_pat);
    let f1_var, f1_pat = make_var "f1" f_pat.scheme in
    let new_p_var, new_p_pat = make_var "new_p" p.scheme in
    let first_fun =
      pure_lambda @@
      pure_abstraction p @@
      in_lambda
    and second_fun =
      lambda @@
      abstraction new_p_pat @@
      value (pure_apply f1_var new_p_var)
    in
    impure_wrappers := (f, f1_var) :: !impure_wrappers;
    let res =
      let_in first_fun @@
      abstraction f1_pat @@
      let_in second_fun @@
      a
    in
    optimize_comp res

  | LetIn (e, ({term = (p, cp)} as a)) ->
    Print.debug "We are now in the let in 1, 3 or 5 for %t" (Typed.print_pattern p);
    beta_reduce a e

  (* XXX simplify *)
  | LetRec (defs, co) ->
    Print.debug "the letrec comp  %t" (CamlPrint.print_computation co);
    List.map (fun (var,abs)->
            Print.debug "ADDING %t and %t to letrec" (CamlPrint.print_variable var) (CamlPrint.print_abstraction abs);
            letrec_memory := (var,abs) :: !letrec_memory) defs;
    let_rec' defs (reduce_comp co)


  | _ -> c


let optimize_command = function
  | Typed.Computation c ->
    Typed.Computation (optimize_comp c)
  | Typed.TopLet (defs, vars) ->
    let defs' = Common.assoc_map optimize_comp defs in
    begin match defs' with
      (* If we define a single simple handler, we inline it *)
      | [({ term = Typed.PVar x}, { term = Value ({ term = Handler _ } as e)})] ->
        inlinable := Common.update x (fun () -> e) !inlinable
      | [({ term = Typed.PVar x}, ({ term = Value ({term = Lambda _ } as e )} ))] ->
        stack := Common.update x (fun () -> e) !stack
      | _ -> ()
    end;
    Typed.TopLet (defs', vars)
  | Typed.TopLetRec (defs, vars) ->
    Typed.TopLetRec (Common.assoc_map optimize_abs defs, vars)
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
