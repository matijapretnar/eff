(*
 To Do list for optimization :

  ==> Handlers inline.

*)
open Typed

type state = {
  inlinable : (Typed.variable, unit -> Typed.expression) Common.assoc;
  stack : (Typed.variable, Typed.expression) Common.assoc;
  letrec_memory : (Typed.variable, Typed.abstraction) Common.assoc;
  handlers_functions_mem : (Typed.expression * Typed.variable * Typed.expression) list;
  impure_wrappers : (Typed.variable, Typed.expression) Common.assoc
}

let initial = {
  inlinable = [];
  stack = [];
  letrec_memory = [];
  handlers_functions_mem = [];
  impure_wrappers = []
}

let find_inlinable st x =
  match Common.lookup x st.inlinable with
  | Some e -> Some (e ())
  | None -> None

let find_in_stack st x = Common.lookup x st.stack

let find_in_let_rec_mem st v = Common.lookup v st.letrec_memory

let find_in_handlers_func_mem st f_name h_exp =
  let findres = List.filter
                  (fun (h,old_f,new_f) -> (f_name == old_f) && alphaeq_expr [] h h_exp) st.handlers_functions_mem in
  begin match findres with
  | [] -> None
  | [(_,_,newf)] -> Some newf
  end

let a22a a2 = Typed.a22a a2
let a2a2 a = Typed.a2a2 a


let inlinable_definitions =
  let unary_builtin f ty1 ty2 =
    let drt = Type.fresh_dirt () in
    built_in f (Scheme.simple (Type.Arrow (ty1, (ty2, drt))))
  and binary_builtin f ty1 ty2 ty =
    let drt = Type.fresh_dirt ()
    and drt2 = Type.fresh_dirt () in
    built_in f (Scheme.simple (Type.Arrow (ty1, (Type.Arrow (ty2, (ty, drt)), drt2))))
  and polymorphic expr_of_ty = fun () -> expr_of_ty (Type.fresh_ty ())
  and monomorphic expr = fun () -> expr in
  [
    ("=", polymorphic @@ fun t -> binary_builtin "(=)" t t Type.bool_ty);
    ("<", polymorphic @@ fun t -> binary_builtin "(<)" t t Type.bool_ty);
    ("<>", polymorphic @@ fun t -> binary_builtin "(<>)" t t Type.bool_ty);
    (">", polymorphic @@ fun t -> binary_builtin "(>)" t t Type.bool_ty);
    (">=", polymorphic @@ fun t -> binary_builtin "(>=)" t t Type.bool_ty);
    ("<=", polymorphic @@ fun t -> binary_builtin "(<=)" t t Type.bool_ty);
    ("!=", polymorphic @@ fun t -> binary_builtin "(!=)" t t Type.bool_ty);
    ("~-", monomorphic @@ unary_builtin "(~-)" Type.int_ty Type.int_ty);
    ("+", monomorphic @@ binary_builtin "(+)" Type.int_ty Type.int_ty Type.int_ty);
    ("*", monomorphic @@ binary_builtin "( * )" Type.int_ty Type.int_ty Type. int_ty);
    ("-", monomorphic @@ binary_builtin "(-)" Type.int_ty Type.int_ty Type.int_ty);
    ("mod", monomorphic @@ binary_builtin "(mod)" Type.int_ty Type.int_ty Type.int_ty);
    ("~-.", monomorphic @@ unary_builtin "(~-.)" Type.float_ty Type.float_ty);
    ("+.", monomorphic @@ binary_builtin "(+.)" Type.float_ty Type.float_ty Type.float_ty);
    ("*.", monomorphic @@ binary_builtin "( *. )" Type.float_ty Type.float_ty Type.float_ty);
    ("-.", monomorphic @@ binary_builtin "(-.)" Type.float_ty Type.float_ty Type.float_ty);
    ("/.", monomorphic @@ binary_builtin "(/.)" Type.float_ty Type.float_ty Type.float_ty);
    ("/", monomorphic @@ binary_builtin "(/)" Type.int_ty Type.int_ty Type.int_ty);
    ("float_of_int", monomorphic @@ unary_builtin "float_of_int" Type.int_ty Type.float_ty);
    ("^", monomorphic @@ binary_builtin "(^)" Type.string_ty Type.string_ty Type.string_ty);
    ("string_length", monomorphic @@ unary_builtin "string_length" Type.string_ty Type.int_ty)
  ]

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

let rec substitute_pattern_comp st c p exp =
  optimize_comp st (Typed.subst_comp (Typed.pattern_match p exp) c)
and substitute_pattern_expr st e p exp =
  optimize_expr st (Typed.subst_expr (Typed.pattern_match p exp) e)

and beta_reduce st ({term = (p, c)} as a) e =
  match applicable_pattern p (Typed.free_vars_comp c) with
  | NotInlinable when is_atomic e -> substitute_pattern_comp st c p e
  | Inlinable -> substitute_pattern_comp st c p e
  | NotPresent -> c
  | _ ->
    let a =
      begin match p with
        | {term = Typed.PVar x} ->
          Print.debug "Added to stack ==== %t" (CamlPrint.print_variable x);
          let st = {st with stack = Common.update x e st.stack} in
          abstraction p (optimize_comp st c)
        | _ ->
          Print.debug "We are now in the let in 5 novar for %t" (Typed.print_pattern p);
          a
      end
    in
    let_in e a

and optimize_expr st e = reduce_expr st (optimize_sub_expr st e)
and optimize_comp st c = reduce_comp st (optimize_sub_comp st c)

and optimize_sub_expr st e =
  let loc = e.location in
  match e.term with
  | Record lst ->
    record ~loc (Common.assoc_map (optimize_expr st) lst)
  | Variant (lbl, e) ->
    variant ~loc (lbl, (Common.option_map (optimize_expr st) e))
  | Tuple lst ->
    tuple ~loc (List.map (optimize_expr st) lst)
  | Lambda a ->
    lambda ~loc (optimize_abs st a)
  | Pure c ->
    pure ~loc (optimize_comp st c)
  | Handler h ->
    handler ~loc {
      effect_clauses = Common.assoc_map (optimize_abs2 st) h.effect_clauses;
      value_clause = optimize_abs st h.value_clause;
      finally_clause = optimize_abs st h.finally_clause;
    }
  | (Var _ | Const _ | BuiltIn _ | Effect _) -> e
and optimize_sub_comp st c =
  let loc = c.location in
  match c.term with
  | Value e ->
    value ~loc (optimize_expr st e)
  | Let (li, c1) ->
    let' ~loc (Common.assoc_map (optimize_comp st) li) (optimize_comp st c1)
  | LetRec (li, c1) ->
    let_rec' ~loc (Common.assoc_map (optimize_abs st) li) (optimize_comp st c1)
  | Match (e, li) ->
    match' ~loc (optimize_expr st e) (List.map (optimize_abs st) li)
  | While (c1, c2) ->
    while' ~loc (optimize_comp st c1) (optimize_comp st c2)
  | For (v, e1, e2, c1, b) ->
    for' ~loc v (optimize_expr st e1) (optimize_expr st e2) (optimize_comp st c1) b
  | Apply (e1, e2) ->
    apply ~loc (optimize_expr st e1) (optimize_expr st e2)
  | Handle (e, c1) ->
    handle ~loc (optimize_expr st e) (optimize_comp st c1)
  | Check c1 ->
    check ~loc (optimize_comp st c1)
  | Call (eff, e1, a1) ->
    call ~loc eff (optimize_expr st e1) (optimize_abs st a1)
  | Bind (c1, a1) ->
    bind ~loc (optimize_comp st c1) (optimize_abs st a1)
  | LetIn (e, a) ->
    let_in ~loc (optimize_expr st e) (optimize_abs st a)
and optimize_abs st {term = (p, c); location = loc} =
  abstraction ~loc p (optimize_comp st c)
and optimize_abs2 st a2 = a2a2 @@ optimize_abs st @@ a22a @@ a2

and reduce_expr st e =
  let e' = match e.term with

  | Var x ->
    begin match find_inlinable st x with
      | Some ({term = Handler _} as d) -> reduce_expr st (refresh_expr d)
      | Some d -> reduce_expr st d
      | _ -> e
    end

  | Effect eff ->
    let (eff_name, (ty_par, ty_res)) = eff in
    let param_var, param_pat = make_var "param" (Scheme.simple ty_par) in
    let result_var, result_pat = make_var "result" (Scheme.simple ty_res) in
    let k = abstraction result_pat (value result_var) in
    let call_eff_param_var_k = reduce_comp st (call eff param_var k) in
    let res =
      lambda (abstraction param_pat call_eff_param_var_k)
    in
    (* Body is already reduced and it's a lambda *)
    res

  | Pure {term = Value e} ->
    e

  | _ -> e
  in
  if e <> e' then
  Print.debug ~loc:e.Typed.location "%t : %t@.~~~>@.%t : %t@.\n"
    (CamlPrint.print_expression CamlPrint.initial e) (Scheme.print_ty_scheme e.Typed.scheme)
    (CamlPrint.print_expression CamlPrint.initial e') (Scheme.print_ty_scheme e'.Typed.scheme);
  e'


and reduce_comp st c =
  let c' = match c.term with

  (* Convert simultaneous let into a sequence of binds *)
  | Let (defs, c) ->
    let binds = List.fold_right (fun (p_def, c_def) binds ->
        bind c_def (abstraction p_def binds)
      ) defs c in
    reduce_comp st binds

  | Match ({term = Const cst}, cases) ->
    let rec find_const_case = function
      | [] -> c
      | ({term = {term = PConst cst'}, c'}) :: _ when Const.equal cst cst' -> c'
      | _ :: cases -> find_const_case cases
    in
    find_const_case cases

  | Bind (c1, c2) when Scheme.is_pure c1.scheme ->
    beta_reduce st c2 (reduce_expr st (pure c1))

  | Bind ({term = Bind (c1, {term = (p1, c2)})}, c3) ->
    let bind_c2_c3 = reduce_comp st (bind c2 c3) in
    let res =
      bind c1 (abstraction p1 bind_c2_c3)
    in
    reduce_comp st res

  | Bind ({term = LetIn (e1, {term = (p1, c2)})}, c3) ->
    let bind_c2_c3 = reduce_comp st (bind c2 c3) in
    let res =
      let_in e1 (abstraction p1 (bind_c2_c3))
    in
    reduce_comp st res

  | Bind ({term = Call (eff, param, k)}, c) ->
    let {term = (k_pat, k_body)} = refresh_abs k in
    let bind_k_c = reduce_comp st (bind k_body c) in
    let res =
      call eff param (abstraction k_pat bind_k_c)
    in
    reduce_comp st res

  | Handle (h, {term = LetIn (e, {term = (p, c)})}) ->
    let handle_h_c = reduce_comp st (handle h c) in
    let res =
      let_in e (abstraction p (handle_h_c))
    in
    reduce_comp st res

  | Handle (h, {term = LetRec (defs, co)}) ->
    let handle_h_c = reduce_comp st (handle h co) in
    let res =
      let_rec' defs handle_h_c
    in
    reduce_comp st res

  | Handle ({term = Handler h}, c1)
        when (Scheme.is_pure_for_handler c1.Typed.scheme h.effect_clauses) ->
    Print.debug "Remove handler, since no effects in common with computation";
    reduce_comp st (bind c1 h.value_clause)

  | Handle ({term = Handler h} as handler, {term = Bind (c1, {term = (p1, c2)})})
        when (Scheme.is_pure_for_handler c1.Typed.scheme h.effect_clauses) ->
    Print.debug "Remove handler of outer Bind, since no effects in common with computation";
    reduce_comp st (bind (reduce_comp st c1) (abstraction p1 (reduce_comp st (handle (refresh_expr handler) c2))))

  | Handle ({term = Handler h}, c) when Scheme.is_pure c.scheme ->
    beta_reduce st h.value_clause (reduce_expr st (pure c))

  | Handle ({term = Handler h}, {term = Bind (c1, {term = (p1, c2)})})
        when (Scheme.is_pure_for_handler c2.Typed.scheme h.effect_clauses) ->
    Print.debug "Move inner bind into the value case";
    let new_value_clause = abstraction p1 (bind (reduce_comp st c2) (refresh_abs h.value_clause)) in
    let hdlr = handler {
      effect_clauses = h.effect_clauses;
      value_clause = refresh_abs new_value_clause;
      finally_clause = h.finally_clause;
    } in
    reduce_comp st (handle (refresh_expr hdlr) c1)

  | Handle ({term = Handler h} as h2, {term = Bind (c1, {term = (p, c2)})}) ->
    Print.debug "Move (dirty) inner bind into the value case";
    let new_value_clause = abstraction p (handle (refresh_expr h2) (refresh_comp (reduce_comp st c2) )) in
    let hdlr = handler {
      effect_clauses = h.effect_clauses;
      value_clause = refresh_abs new_value_clause;
      finally_clause = h.finally_clause;
    } in
    reduce_comp st (handle (refresh_expr hdlr) (refresh_comp c1))

  | Handle ({term = Handler h} as handler, {term = Call (eff, param, k)}) ->
    let {term = (k_pat, k_body)} = refresh_abs k in
    let handled_k =
      abstraction k_pat
        (reduce_comp st (handle (refresh_expr handler) k_body))
    in
    begin match Common.lookup eff h.effect_clauses with
      | Some eff_clause ->
        let {term = (p1, p2, c)} = refresh_abs2 eff_clause in
        (* Shouldn't we check for inlinability of p1 and p2 here? *)
        substitute_pattern_comp st (substitute_pattern_comp st c p1 param) p2 (lambda handled_k)
      | None ->
        let res =
          call eff param handled_k
        in
        reduce_comp st res
    end

  | Apply ({term = Lambda a}, e) ->
    beta_reduce st a e

  | Apply ({term = Var v}, e2) ->
    begin match Common.lookup v st.impure_wrappers with
      | Some f ->
        let res =
          value (pure (apply f e2))
        in
        reduce_comp st res
      | None -> c
    end

  | Handle (e1, {term = Match (e2, cases)}) ->
    let push_handler = fun {term = (p, c)} ->
      abstraction p (reduce_comp st (handle (refresh_expr e1) c))
    in
    let res =
      match' e2 (List.map push_handler cases)
    in
    res

(*   | Handle (e1, {term = Apply (ae1, ae2)}) ->
    begin match ae1.term with
      | Var v ->
        begin match find_in_stack st v with
          | Some ({term = Lambda k}) ->
            let {term = (newdp, newdc)} = refresh_abs k in
            let (h_ctx,Type.Handler(h_ty_in, (ty_out, drt_out)),h_const) = e1.scheme in
            let (f_ctx,Type.Arrow(f_ty_in, f_ty_out ),f_const) = ae1.scheme in 
            let constraints = Constraints.list_union [h_const; f_const]
                              |> Constraints.add_dirty_constraint ~loc:c.location f_ty_out h_ty_in in
            let sch = (h_ctx @ f_ctx, (Type.Arrow(f_ty_in,(ty_out,drt_out))), constraints) in
            let function_scheme = Scheme.clean_ty_scheme ~loc:c.location sch in 
            let f_var, f_pat = make_var "newvar"  function_scheme in
            let f_def =
              lambda @@
              abstraction newdp @@
              handle e1 newdc in
            let res =
              let_in f_def @@
              abstraction f_pat @@
              apply f_var ae2
            in
            optimize_comp st res
          | _ -> begin match (find_in_handlers_func_mem st v e1) with
                 | Some new_f_exp ->
                                    let res = apply new_f_exp ae2
                                    in reduce_comp st res
                 | _ ->
                       begin match (find_in_let_rec_mem st v) with
                       | Some abs ->
                                    let (let_rec_p,let_rec_c) = abs.term in
                                    let (h_ctx,Type.Handler(h_ty_in, (ty_out, drt_out)),h_const) = e1.scheme in
                                    let (f_ctx,Type.Arrow(f_ty_in, f_ty_out ),f_const) = ae1.scheme in 
                                    let constraints = Constraints.list_union [h_const; f_const]
                                          |> Constraints.add_dirty_constraint ~loc:c.location f_ty_out h_ty_in in
                                    let sch = (h_ctx @ f_ctx, (Type.Arrow(f_ty_in,(ty_out,drt_out))), constraints) in
                                    let function_scheme = Scheme.clean_ty_scheme ~loc:c.location sch in 
                                    let new_f_var, new_f_pat = make_var "newvar"  function_scheme in
                                    let new_handler_call = handle e1 let_rec_c in
                                    let Var newfvar = new_f_var.term in
                                    let defs = [(newfvar, (abstraction let_rec_p new_handler_call ))] in
                                    let st = {st with handlers_functions_mem = (e1,v,new_f_var) :: st.handlers_functions_mem} in
                                    let res =
                                      let_rec' defs @@
                                      apply new_f_var ae2
                                    in
                                    optimize_comp st res
                       | None -> c
                       end
               end
        end
      | PureApply ({term = Var fname}, pae2)->
        begin match find_in_stack st fname with
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
            optimize_comp st res
          | _ -> c
        end
      | _ -> c
    end *)



    (*
      let f = \p. val lambda in c
       ~~> (append f := f1 to impure_wrappers)
      let f1 = \*p. lambda
      let f = \new_p. val (f1 new_p) in
      c
    *)
(*   | LetIn ({term = Lambda ({term = (p, {term = Value ({term = Lambda _ } as in_lambda)} )})}, ({term = ({term = PVar f} as f_pat,_)} as a) )->
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
    let st = {st with impure_wrappers = (f, f1_var) :: st.impure_wrappers} in
    let res =
      let_in first_fun @@
      abstraction f1_pat @@
      let_in second_fun @@
      a
    in
    optimize_comp st res *)

  | LetIn (e, ({term = (p, cp)} as a)) ->
    Print.debug "We are now in the let in 1, 3 or 5 for %t" (Typed.print_pattern p);
    beta_reduce st a e

  (* XXX simplify *)
  | LetRec (defs, co) ->
    Print.debug "the letrec comp  %t" (CamlPrint.print_computation CamlPrint.initial co);
    let st = 
    List.fold_right (fun (var,abs) st ->
            Print.debug "ADDING %t and %t to letrec" (CamlPrint.print_variable var) (CamlPrint.print_abstraction ~pure:false CamlPrint.initial abs);
            {st with letrec_memory = (var,abs) :: st.letrec_memory}) defs st in
    let_rec' defs (reduce_comp st co)


  | _ -> c

  in 
  if c <> c' then
  Print.debug ~loc:c.Typed.location "%t : %t@.~~~>@.%t : %t@.\n"
    (CamlPrint.print_computation CamlPrint.initial c) (Scheme.print_dirty_scheme c.Typed.scheme)
    (CamlPrint.print_computation CamlPrint.initial c') (Scheme.print_dirty_scheme c'.Typed.scheme);
  c'


let optimize_command st = function
  | Typed.Computation c ->
    st, Typed.Computation (optimize_comp st c)
  | Typed.TopLet (defs, vars) ->
    let defs' = Common.assoc_map (optimize_comp st) defs in
    let defs' = Common.assoc_map (fun c ->
      if Scheme.is_pure c.scheme then value (reduce_expr st (pure c)) else c
    ) defs' in
    let st' = begin match defs' with
      (* If we define a single simple handler, we inline it *)
      | [({ term = Typed.PVar x}, { term = Value ({ term = Handler _ } as e)})] ->
        {st with inlinable = Common.update x (fun () -> e) st.inlinable}
      | [({ term = Typed.PVar x}, ({ term = Value ({term = Lambda _ } as e )} ))] ->
        {st with stack = Common.update x e st.stack}
      | _ -> st
    end
    in
    st', Typed.TopLet (defs', vars)
  | Typed.TopLetRec (defs, vars) ->
    st, Typed.TopLetRec (Common.assoc_map (optimize_abs st) defs, vars)
  | Typed.External (x, _, f) as cmd ->
    let st' =
      begin match Common.lookup f inlinable_definitions with
        (* If the external function is one of the predefined inlinables, we inline it *)
        | Some e -> {st with inlinable = Common.update x e st.inlinable}
        | None -> st
      end
    in
    st', cmd
  | Typed.DefEffect _ | Typed.Reset | Typed.Quit | Typed.Use _
  | Typed.Tydef _ | Typed.TypeOf _ | Typed.Help as cmd -> st, cmd

let optimize_commands cmds =
  let _, cmds = 
  List.fold_left (fun (st, cmds) (cmd, loc) ->
    let st', cmd' = optimize_command st cmd in
    st', (cmd', loc) :: cmds
  ) (initial, []) cmds
in
List.rev cmds