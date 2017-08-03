(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type effect = Common.effect * (Type.ty * Type.ty)

type 'term annotation = {
  term: 'term;
  location: Location.t;
}

type pattern = plain_pattern annotation
and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (Common.field, pattern) Common.assoc
  | PVariant of Common.label * pattern option
  | PConst of Const.t
  | PNonbinding

let rec pattern_vars p =
  match p.term with
  | PVar x -> [x]
  | PAs (p,x) -> x :: pattern_vars p
  | PTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
  | PRecord lst -> List.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
  | PVariant (_, None) -> []
  | PVariant (_, Some p) -> pattern_vars p
  | PConst _ -> []
  | PNonbinding -> []

let annotate t loc = {
  term = t;
  location = loc;
}

(** Pure expressions *)
type expression = plain_expression annotation
and plain_expression =
  | Var of variable
  | BuiltIn of string * int
  | Const of Const.t
  | Tuple of expression list
  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option
  | Effect of effect
  | Handler of handler
  | Lambda of abstractionLambda
  | BigLambdaTy of abstractionType
  | ApplyTy of expression * Type.ty

(** Impure computations *)
and computation = plain_computation annotation
and plain_computation =
  | Value of expression
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  (* | TyApple of expression * target_ty *)
  | Handle of expression * computation
  | Call of effect * expression * abstraction
  | Bind of computation * abstraction

(** Handler definitions *)
and handler = {
  effect_clauses : (effect, abstraction2) Common.assoc;
  value_clause : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation) annotation

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation) annotation

(** Abstractions that take one argument but is typed. *)
and abstractionLambda = (pattern * Type.ty * computation)

(** Abstraction that take one *type* argument. **)
and abstractionType = (Params.ty_param * expression)

type toplevel = plain_toplevel * Location.t
and plain_toplevel =
  | Tydef of (Common.tyname, Params.t * Tctx.tydef) Common.assoc
  | TopLet of (pattern * computation) list * (variable * Scheme.ty_scheme) list
  | TopLetRec of (variable * abstraction) list * (variable * Scheme.ty_scheme) list
  | External of variable * Type.ty * string
  | DefEffect of effect * (Type.ty * Type.ty)
  | Computation of computation
  | Use of string
  | Reset
  | Help
  | Quit
  (* | TypeOf of computation *)

let abstraction ?loc p c : abstraction =
  {
    term = (p, c);
    location = c.location;
  }

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let print_variable = Variable.print ~safe:true

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PVar x -> print "%t" (print_variable x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record print_pattern lst ppf
  | PVariant (lbl, None) when lbl = Common.nil -> print "[]"
  | PVariant (lbl, None) -> print "%s" lbl
  | PVariant ("(::)", Some ({ term = PTuple [p1; p2] })) ->
    print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | PVariant (lbl, Some p) ->
    print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.term with
  | Var x ->
    print "%t" (print_variable x)
  | BuiltIn (s, _) ->
    print "%s" s
  | Const c ->
    print "%t" (Const.print c)
  | Tuple lst ->
    Print.tuple print_expression lst ppf
  | Record lst ->
    Print.record print_expression lst ppf
  | Variant (lbl, None) ->
    print "%s" lbl
  | Variant (lbl, Some e) ->
    print ~at_level:1 "%s %t" lbl (print_expression e)
  | Lambda (_,_,_) ->
    assert false (*Still needs to be done*)
  | Handler h ->
    print "{@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]}"
      (print_abstraction h.value_clause)
      (print_effect_clauses h.effect_clauses)
  | Effect eff ->
    print ~at_level:2 "effect %t" (print_effect eff)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | Apply (e1, e2) ->
    print ~at_level:1 "%t@ %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Value e ->
    print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Match (e, []) ->
    print ~at_level:2 "(match %t with _ -> assert false)" (print_expression e)
  | Match (e, lst) ->
    print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e) (Print.cases print_abstraction lst)
  | Handle (e, c) ->
    print ~at_level:1 "handle %t %t" (print_expression ~max_level:0 e) (print_computation ~max_level:0 c)
  | LetRec (lst, c) ->
    print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Call (eff, e, a) ->
    print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction a)
  | Bind (c1, a) ->
    print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]" (print_computation ~max_level:0 c1) (print_abstraction a)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
    print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), {term = (p1, p2, c)}) :: cases ->
    print ~at_level:1 "| %t -> (fun %t %t -> %t) %t"
      (print_effect eff) (print_pattern p1) (print_pattern p2) (print_computation c) (print_effect_clauses cases)

and print_abstraction {term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

and print_pure_abstraction {term = (p, e)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_expression e)

and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_top_let_abstraction (p, c) ppf =
  match c.term with
  | Value e ->
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ ->
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a)


let rec refresh_pattern sbst p =
  let sbst', p' = refresh_pattern' sbst p.term in
  sbst', {p with term = p'}
and refresh_pattern' sbst = function
  | PVar x ->
    let x' = Variable.refresh x in
    Common.update x x' sbst, PVar x'
  | PAs (p, x) ->
    let x' = Variable.refresh x in
    let sbst, p' = refresh_pattern (Common.update x x' sbst) p in
    sbst, PAs (p', x')
  | PTuple ps ->
    let sbst, ps' =
      List.fold_right (fun p (sbst, ps') ->
          let sbst, p' = refresh_pattern sbst p in
          sbst, p' :: ps'
        ) ps (sbst, []) in
    sbst, PTuple ps'
  | PRecord flds ->
    let sbst, flds' =
      List.fold_right (fun (lbl, p) (sbst, flds') ->
          let sbst, p' = refresh_pattern sbst p in
          sbst, (lbl, p') :: flds'
        ) flds (sbst, []) in
    sbst, PRecord flds'
  | PVariant (lbl, None) ->
    sbst, PVariant (lbl, None)
  | PVariant (lbl, Some p) ->
    let sbst, p' = refresh_pattern sbst p in
    sbst, PVariant (lbl, Some p')
  | (PConst _ | PNonbinding) as p -> sbst, p

let rec refresh_expr sbst e =
  {e with term = refresh_expr' sbst e.term}
and refresh_expr' sbst = function
  | (Var x) as e ->
    begin match Common.lookup x sbst with
      | Some x' -> Var x'
      | None -> e
    end
   | Lambda a ->
    assert false
  | Handler h ->
    Handler (refresh_handler sbst h)
  | Tuple es ->
    Tuple (List.map (refresh_expr sbst) es)
  | Record flds ->
    Record (Common.assoc_map (refresh_expr sbst) flds)
  | Variant (lbl, e) ->
    Variant (lbl, Common.option_map (refresh_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
and refresh_comp sbst c =
  {c with term = refresh_comp' sbst c.term}
and refresh_comp' sbst = function
  | Bind (c1, c2) ->
    Bind (refresh_comp sbst c1, refresh_abs sbst c2)
  | LetRec (li, c1) ->
    let new_xs, sbst' = List.fold_right (fun (x, _) (new_xs, sbst') ->
        let x' = Variable.refresh x in
        x' :: new_xs, Common.update x x' sbst'
      ) li ([], sbst) in
    let li' =
      List.combine new_xs (List.map (fun (_, a) -> refresh_abs sbst' a) li)
    in
    LetRec (li', refresh_comp sbst' c1)
  | Match (e, li) ->
    Match (refresh_expr sbst e, List.map (refresh_abs sbst) li)
  | Apply (e1, e2) ->
    Apply (refresh_expr sbst e1, refresh_expr sbst e2)
  | Handle (e, c) ->
    Handle (refresh_expr sbst e, refresh_comp sbst c)
  | Call (eff, e, a) ->
    Call (eff, refresh_expr sbst e, refresh_abs sbst a)
  | Value e ->
    Value (refresh_expr sbst e)
and refresh_handler sbst h = {
  effect_clauses = Common.assoc_map (refresh_abs2 sbst) h.effect_clauses;
  value_clause = refresh_abs sbst h.value_clause;
}
and refresh_abs sbst a =
  let (p, c) = a.term in
  let sbst, p' = refresh_pattern sbst p in
  {a with term = (p', refresh_comp sbst c)}
and refresh_abs2 sbst a2 =
  (* a2a2 @@ refresh_abs sbst @@ a22a @@ a2 *)
  assert false

let rec subst_expr sbst e =
  {e with term = subst_expr' sbst e.term}
and subst_expr' sbst = function
  | (Var x) as e ->
    begin match Common.lookup x sbst with
      | Some e' -> e'
      | None -> e
    end
  | Lambda a ->
    assert false
  | Handler h ->
    Handler (subst_handler sbst h)
  | Tuple es ->
    Tuple (List.map (subst_expr sbst) es)
  | Record flds ->
    Record (Common.assoc_map (subst_expr sbst) flds)
  | Variant (lbl, e) ->
    Variant (lbl, Common.option_map (subst_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
and subst_comp sbst c =
  {c with term = subst_comp' sbst c.term}
and subst_comp' sbst = function
  | Bind (c1, c2) ->
    Bind (subst_comp sbst c1, subst_abs sbst c2)
  | LetRec (li, c1) ->
    let li' = List.map (fun (x, a) ->
        (* XXX Should we check that x does not appear in sbst? *)
        (x, subst_abs sbst a)
      ) li
    in
    LetRec (li', subst_comp sbst c1)
  | Match (e, li) ->
    Match (subst_expr sbst e, List.map (subst_abs sbst) li)
  | Apply (e1, e2) ->
    Apply (subst_expr sbst e1, subst_expr sbst e2)
  | Handle (e, c) ->
    Handle (subst_expr sbst e, subst_comp sbst c)
  | Call (eff, e, a) ->
    Call (eff, subst_expr sbst e, subst_abs sbst a)
  | Value e ->
    Value (subst_expr sbst e)
and subst_handler sbst h = {
  effect_clauses = Common.assoc_map (subst_abs2 sbst) h.effect_clauses;
  value_clause = subst_abs sbst h.value_clause;
}
and subst_abs sbst a =
  let (p, c) = a.term in
  (* XXX Should we check that p & sbst have disjoint variables? *)
  {a with term = (p, subst_comp sbst c)}
and subst_abs2 sbst a2 =
  (* a2a2 @@ subst_abs sbst @@ a22a @@ a2 *)
  assert false




let assoc_equal eq flds flds' : bool =
  let rec equal_fields flds =
    match flds with
    | [] -> true
    | (f, x) :: flds ->
      begin match Common.lookup f flds' with
        | Some x' when eq x x' -> equal_fields flds
        | _ -> false
      end
  in
  List.length flds = List.length flds' &&
  equal_fields flds

let rec make_equal_pattern eqvars p p' =
  make_equal_pattern' eqvars p.term p'.term
and make_equal_pattern' eqvars p p' =
  match p, p' with
  | PVar x, PVar x' -> Some ((x, x') :: eqvars)
  | PAs (p, x), PAs (p', x') ->
    Common.option_map (fun eqvars ->
        (x, x') :: eqvars
      ) (make_equal_pattern eqvars p p')
  | PTuple ps, PTuple ps' ->
    List.fold_right2 (fun p p' -> function
        | Some eqvars' -> make_equal_pattern eqvars' p p'
        | None -> None
      ) ps ps' (Some eqvars)
  | PConst cst, PConst cst' when Const.equal cst cst' -> Some eqvars
  | PNonbinding, PNonbinding -> Some eqvars
  | PVariant (lbl, None), PVariant (lbl', None) when lbl = lbl' -> Some eqvars
  | PVariant (lbl, Some p), PVariant (lbl', Some p') when lbl = lbl' ->
      make_equal_pattern eqvars p p'
  | _, _ -> None

let rec alphaeq_expr eqvars e e' =
  alphaeq_expr' eqvars e.term e'.term
and alphaeq_expr' eqvars e e' =
  match e, e' with
  | Var x, Var y ->
    List.mem (x, y) eqvars ||  Variable.compare x y = 0
  | Lambda a, Lambda a' ->
    assert false
  | Handler h, Handler h' ->
    alphaeq_handler eqvars h h'
  | Tuple es, Tuple es' ->
    List.for_all2 (alphaeq_expr eqvars) es es'
  | Record flds, Record flds' ->
    assoc_equal (alphaeq_expr eqvars) flds flds'
  | Variant (lbl, None), Variant (lbl', None) ->
    lbl = lbl'
  | Variant (lbl, Some e), Variant (lbl', Some e') ->
    lbl = lbl' && alphaeq_expr eqvars e e'
  | BuiltIn (f, n), BuiltIn (f', n') ->
    f = f' && n = n'
  | Const cst, Const cst' ->
    Const.equal cst cst'
  | Effect eff, Effect eff' ->
    eff = eff'
  | _, _ -> false
and alphaeq_comp eqvars c c' =
  alphaeq_comp' eqvars c.term c'.term
and alphaeq_comp' eqvars c c' =
  match c, c' with
  | Bind (c1, c2), Bind (c1', c2') ->
    alphaeq_comp eqvars c1 c1' && alphaeq_abs eqvars c2 c2'
  | LetRec (li, c1), LetRec (li', c1') ->
    (* XXX Not yet implemented *)
    false
  | Match (e, li), Match (e', li') ->
    alphaeq_expr eqvars e e' && List.for_all2 (alphaeq_abs eqvars) li li'
  | Apply (e1, e2), Apply (e1', e2') ->
    alphaeq_expr eqvars e1 e1' && alphaeq_expr eqvars e2 e2'
  | Handle (e, c), Handle (e', c') ->
    alphaeq_expr eqvars e e' && alphaeq_comp eqvars c c'
  | Call (eff, e, a), Call (eff', e', a') ->
    eff = eff' && alphaeq_expr eqvars e e' && alphaeq_abs eqvars a a'
  | Value e, Value e' ->
    alphaeq_expr eqvars e e'
  | _, _ -> false
and alphaeq_handler eqvars h h' =
  assoc_equal (alphaeq_abs2 eqvars) h.effect_clauses h'.effect_clauses &&
  alphaeq_abs eqvars h.value_clause h'.value_clause
and alphaeq_abs eqvars {term = (p, c)} {term = (p', c')} =
  match make_equal_pattern eqvars p p' with
  | Some eqvars' -> alphaeq_comp eqvars' c c'
  | None -> false
and alphaeq_abs2 eqvars a2 a2' =
  (* alphaeq_abs eqvars (a22a a2) (a22a a2') *)
  assert false

let pattern_match p e =
  (* XXX The commented out part checked that p and e had matching types *)
(*   let _, ty_e, constraints_e = e.scheme
  and _, ty_p, constraints_p = p.scheme in
  let constraints =
    Constraints.union constraints_e constraints_p |>
    Constraints.add_ty_constraint ~loc:e.location ty_e ty_p
  in
  ignore constraints; *)
  let rec extend_subst p e sbst =
    match p.term, e.term with
    | PVar x, e -> Common.update x e sbst
    | PAs (p, x), e' ->
      let sbst = extend_subst p e sbst in
      Common.update x e' sbst
    | PNonbinding, _ -> sbst
    | PTuple ps, Tuple es -> List.fold_right2 extend_subst ps es sbst
    | PRecord ps, Record es ->
      begin
        let rec extend_record ps es sbst =
          match ps with
          | [] -> sbst
          | (f, p) :: ps ->
            let e = List.assoc f es in
            extend_record ps es (extend_subst p e sbst)
        in
        try
          extend_record ps es sbst
        with Not_found -> Error.runtime ~loc:e.location "Incompatible records in substitution."
      end
    | PVariant (lbl, None), Variant (lbl', None) when lbl = lbl' -> sbst
    | PVariant (lbl, Some p), Variant (lbl', Some e) when lbl = lbl' ->
      extend_subst p e sbst
    | PConst c, Const c' when Const.equal c c' -> sbst
    | _, _ -> Error.runtime ~loc:e.location "Cannot substitute an expression in a pattern."
  in
  extend_subst p e []

let (@@@) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)
let (---) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)
let concat_vars vars = List.fold_right (@@@) vars ([], [])

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_expr e
  | LetRec (li, c1) ->
    let xs, vars = List.fold_right (fun (x, a) (xs, vars) ->
        x :: xs, free_vars_abs a @@@ vars
      ) li ([], free_vars_comp c1) in
    vars --- xs
  | Match (e, li) -> free_vars_expr e @@@ concat_vars (List.map free_vars_abs li)
  | Apply (e1, e2) -> free_vars_expr e1 @@@ free_vars_expr e2
  | Handle (e, c1) -> free_vars_expr e @@@ free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_expr e1 @@@ free_vars_abs a1
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
and free_vars_expr e =
  match e.term with
  | Var v -> ([], [v])
  | Tuple es -> concat_vars (List.map free_vars_expr es)
  | Lambda a -> assert false
  | Handler h -> free_vars_handler h
  | Record flds -> concat_vars (List.map (fun (_, e) -> free_vars_expr e) flds)
  | Variant (_, None) -> ([], [])
  | Variant (_, Some e) -> free_vars_expr e
  | (BuiltIn _ | Effect _ | Const _) -> ([], [])
and free_vars_handler h =
  free_vars_abs h.value_clause @@@
  concat_vars (List.map (fun (_, a2) -> free_vars_abs2 a2) h.effect_clauses)
and free_vars_finally_handler (h, finally_clause) =
  free_vars_handler h @@@
  free_vars_abs finally_clause
and free_vars_abs a =
  let (p, c) = a.term in
  let (inside, outside) = free_vars_comp c --- pattern_vars p in
  (inside @ outside, [])
and free_vars_abs2 a2 =
  (* free_vars_abs @@ a22a @@ a2 *)
  assert false

let occurrences x (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x = y) ys) in
  (count inside, count outside)
