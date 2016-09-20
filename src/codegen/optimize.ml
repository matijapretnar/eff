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

let impure_wrappers = ref []

let find_inlinable x =
  match Common.lookup x !inlinable with
  | Some e -> Some (e ())
  | None -> None

let find_in_stack x =
  match Common.lookup x !stack with
  | Some e -> Some (e ())
  | None -> None
 
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
      let binds = List.fold_right (fun (p, c) binds ->
        bind c (abstraction p binds)
      ) defs c in
      reduce_comp binds

  | Match ({term = Const cst}, cases) ->
      let rec find_const_case = function
      | [] -> c
      | ({term = {term = PConst cst'}, c'}) :: _ when Const.equal cst cst' -> c'
      | _ :: cases -> find_const_case cases
      in
      find_const_case cases

  | Bind ({term = Value e}, c2) ->
      beta_reduce c2 e

  | Bind ({term = Bind (c1, {term = (p2, c2)})}, c3) ->
      let bind_c2_c3 = reduce_comp (bind c2 c3) in
      let res =
        bind c1 (abstraction p2 bind_c2_c3)
      in
      reduce_comp res

  | Bind ({term = LetIn (e, {term = (p1, c1)})}, c2) ->
      let bind_c1_c2 = reduce_comp (bind c1 c2) in
      let res =
        let_in e (abstraction p1 (bind_c1_c2))
      in
      reduce_comp res
  
  | Bind ({term = Call (eff, e, k)}, c2) ->
      let (_, (result_ty, _), _) = k.scheme in
      let result_var, result_pat = make_var "result" (Scheme.simple result_ty) in
      let lambda_k = reduce_expr (lambda (refresh_abs k)) in
      let apply_lambda_k_result_var = reduce_comp (apply lambda_k result_var) in
      let bind_apply_lambda_k_result_var_c2 = reduce_comp (bind apply_lambda_k_result_var c2) in
      let res =
       call eff e (abstraction result_pat bind_apply_lambda_k_result_var_c2)
      in
      reduce_comp res

  | Handle (e1, {term = LetIn (e2, {term = (p, c2)})}) ->
      let handle_e1_c2 = reduce_comp (handle e1 c2) in
      let res =
        let_in e2 (abstraction p (handle_e1_c2))
      in
      reduce_comp res

   (* XXX simplify *)
  | Handle (e1, {term = Apply (ae1, ae2)}) ->
      begin match ae1.term with
      | Var v ->
            begin match find_in_stack v with
              | Some d -> 
                begin match d.term with
                | Lambda ({term = (dp,dc)}) ->
                    let new_var, new_pat = make_var "newvar" ae1.scheme in
                    let new_computation = apply ~loc:c.location (new_var) (ae2) in
                    let new_handle = handle ~loc:c.location e1 (substitute_var_comp dc v (refresh_expr d)) in
                    let new_lambda = lambda ~loc:c.location (abstraction ~loc:c.location dp new_handle) in 
                    optimize_comp (let_in ~loc:c.location new_lambda 
                          (abstraction ~loc:c.location new_pat (new_computation)))
                | _ -> c
                end
              |_ -> c
            end
      | PureApply ({term = Var fname},pae2)->
            begin match find_in_stack fname with
              | Some d -> 
                begin match d.term with
                | PureLambda {term = (dp1,{term = Lambda ({term = (dp2,dc)})})} ->
                   let newfname, new_pat = make_var "newvar" ae1.scheme in
                   let pure_application = pure_apply ~loc:c.location newfname pae2 in
                   let application = apply ~loc:c.location pure_application ae2 in
                   let handler_call = handle ~loc:c.location e1 dc in 
                   let newfinnerlambda = lambda ~loc:c.location (abstraction ~loc:c.location dp2 handler_call) in 
                   let newfbody = pure_lambda ~loc:c.location (pure_abstraction dp1 newfinnerlambda) in 
                   let res = 
                     let_in ~loc:c.location (newfbody) (abstraction ~loc:c.location new_pat application) in
                   optimize_comp res
                   
                | _ -> c
              end
              | _ -> c
            end
      | _ -> c
      end

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
  
  | Apply( {term = Var v}, e2) ->
      begin match Common.lookup v !impure_wrappers with
      | Some fn -> 
            let pure_apply_fn_e2 = reduce_expr (pure_apply fn e2) in 
            let res =
              value pure_apply_fn_e2
            in
            reduce_comp res
      | None -> c
      end

  | LetIn (e1, {term = (p, {term = Value e2})}) ->
      Print.debug "We are now in the let in 2 for %t" (Typed.print_pattern p);
      let pure_let_in_e1_p_e2 = reduce_expr (pure_let_in e1 (pure_abstraction p e2)) in
      let res =
        value pure_let_in_e1_p_e2
      in
      reduce_comp res

   (* XXX simplify *)
  (*Matching let f = \x.\y. c *)    
  | LetIn({term = Lambda ({term = (pe1, {term = Value ({term = Lambda ({term = (pe2,ce2)}) } as in_lambda)} )})}, {term = ({term = PVar fo} as p,cp)} )->
        Print.debug "We are now in the let in 4 for %t" (Typed.print_pattern p);
        let new_var, new_pat = make_var "newvar" p.scheme in
        let new_var2, new_pat2 = make_var "newvar2" pe1.scheme in 
        let pure_application = pure_apply ~loc:c.location new_var new_var2 in
        let second_let_value = value ~loc:c.location pure_application in 
        let second_let_lambda = lambda ~loc:c.location (abstraction ~loc:c.location new_pat2 second_let_value) in
        let second_let = let_in ~loc:c.location second_let_lambda (abstraction ~loc:c.location p cp) in
        let outer_lambda = pure_lambda ~loc:c.location (pure_abstraction pe1 in_lambda) in
        let first_let_abstraction = abstraction ~loc:c.location new_pat second_let in
        let first_let = let_in ~loc:c.location (outer_lambda) first_let_abstraction in
        impure_wrappers:= (fo,new_var) :: !impure_wrappers;
        optimize_comp first_let

  | LetIn (e, ({term = (p, cp)} as a)) ->
      Print.debug "We are now in the let in 1, 3 or 5 for %t" (Typed.print_pattern p);
      beta_reduce a e

   (* XXX simplify *)
  | LetRec (defs, co) ->
      Print.debug "the letrec comp%t" (CamlPrint.print_computation co);
      c

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
