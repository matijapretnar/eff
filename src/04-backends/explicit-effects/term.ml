open Utils
module CoreTypes = Language.CoreTypes

module Const = Language.Const
(** Syntax of the core language. *)

module EffectMap = Map.Make (CoreTypes.Effect)

type variable = CoreTypes.Variable.t

type effect = CoreTypes.Effect.t * (Type.ty * Type.ty)

type pattern = (pattern', Type.ty) typed

and pattern' =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (CoreTypes.Field.t, pattern) Assoc.t
  | PVariant of CoreTypes.Label.t * pattern option
  | PConst of Language.Const.t
  | PNonbinding

let pVar p ty = { term = PVar p; ty }

let pTuple ps =
  { term = PTuple ps; ty = Type.Tuple (List.map (fun x -> x.ty) ps) }

let rec pattern_vars pat =
  match pat.term with
  | PVar x -> [ x ]
  | PAs (p, x) -> x :: pattern_vars p
  | PTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
  | PRecord lst -> Assoc.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
  | PVariant (_, None) -> []
  | PVariant (_, Some p) -> pattern_vars p
  | PConst _ -> []
  | PNonbinding -> []

type expression = (expression', Type.ty) typed
(** Pure expressions *)

and expression' =
  | Var of variable
  | Const of Language.Const.t
  | Tuple of expression list
  | Record of (CoreTypes.Field.t, expression) Assoc.t
  | Variant of CoreTypes.Label.t * expression option
  | Lambda of abstraction
  | Effect of effect
  | Handler of handler
  | CastExp of expression * Constraint.ty_coercion
  | LambdaTyCoerVar of Type.TyCoercionParam.t * expression
  | LambdaDirtCoerVar of Type.DirtCoercionParam.t * expression
  | ApplyTyCoercion of expression * Constraint.ty_coercion
  | ApplyDirtCoercion of expression * Constraint.dirt_coercion

and computation = (computation', Type.dirty) typed
(** Impure computations *)

and computation' =
  | Value of expression
  | LetVal of expression * abstraction
  | LetRec of letrec_abstraction list * computation
  (* Historical note: Previously LetRec looked like this:

       LetRec of (variable * Type.ty * expression) list * computation

     Unfortunately this shape forgets the source structure (where the
     abstraction is explicit) and thus makes translation to MulticoreOcaml
     impossible in the general case.
  *)
  | Match of expression * abstraction list
  (* We need to keep the result type in the term, in case the match is empty *)
  | Apply of expression * expression
  | Handle of expression * computation
  | Call of effect * expression * abstraction
  | Op of effect * expression
  | Bind of computation * abstraction
  | CastComp of computation * Constraint.dirty_coercion

and handler = (handler', Type.dirty * Type.dirty) typed

and handler' = {
  effect_clauses : (effect, abstraction2) Assoc.t;
  value_clause : abstraction;
}
(** Handler definitions *)

and abstraction = (pattern * computation, Type.ty * Type.dirty) typed
(** Abstractions that take one argument. *)

and letrec_abstraction = variable * abstraction
(** LetRec Abstractions: function name, result type, pattern,
    and right-hand side *)

and abstraction2 =
  (pattern * pattern * computation, Type.ty * Type.ty * Type.dirty) typed
(** Abstractions that take two arguments. *)

let var x ty = { term = Var x; ty }

let fresh_variable x ty =
  let x' = CoreTypes.Variable.fresh x in
  (pVar x' ty, var x' ty)

let const (_ : Language.Const.t) : expression = failwith __LOC__

let tuple es =
  { term = Tuple es; ty = Type.Tuple (List.map (fun e -> e.ty) es) }

let record (_ : (CoreTypes.Field.t, expression) Assoc.t) : expression =
  failwith __LOC__

let variant (lbl, e) ty = { term = Variant (lbl, e); ty }

let lambda abs = { term = Lambda abs; ty = Type.Arrow abs.ty }

let effect (_ : effect) : expression = failwith __LOC__

let handler h =
  let drty1, drty2 = h.ty in
  (* Check that effect clauses have a correct type *)
  { term = Handler h; ty = Type.Handler (drty1, drty2) }

let castExp (exp, coer) =
  let ty1 = exp.ty and ty1', ty2 = coer.ty in
  assert (Type.equal_ty ty1 ty1');
  { term = CastExp (exp, coer); ty = ty2 }

let lambdaTyCoerVar (_ : Type.TyCoercionParam.t * expression) : expression =
  failwith __LOC__

let lambdaDirtCoerVar (_ : Type.DirtCoercionParam.t * expression) : expression =
  failwith __LOC__

let applyTyCoercion (_ : expression * Constraint.ty_coercion) : expression =
  failwith __LOC__

let applyDirtCoercion (_ : expression * Constraint.dirt_coercion) : expression =
  failwith __LOC__

let value exp = { term = Value exp; ty = Type.pure_ty exp.ty }

let letVal (exp, abs) =
  let ty1, drty2 = abs.ty in
  assert (Type.equal_ty exp.ty ty1);
  { term = LetVal (exp, abs); ty = drty2 }

let letRec (defs, comp) = { term = LetRec (defs, comp); ty = comp.ty }

let match_ (e, cases) drty = { term = Match (e, cases); ty = drty }

let apply (exp1, exp2) =
  match exp1.ty with
  | Type.Arrow (ty1, drty2) ->
      assert (Type.equal_ty exp2.ty ty1);
      { term = Apply (exp1, exp2); ty = drty2 }
  | _ -> assert false

let handle (exp, comp) =
  match exp.ty with
  | Type.Handler (drty1, drty2) ->
      assert (Type.equal_dirty comp.ty drty1);
      { term = Handle (exp, comp); ty = drty2 }
  | _ -> assert false

let call (_ : effect * expression * abstraction) : computation =
  failwith __LOC__

let op (_ : effect * expression) : computation = failwith __LOC__

let bind (comp1, abs2) =
  let ty1, drt1 = comp1.ty and ty2, ((_, drt2) as drty2) = abs2.ty in
  assert (Type.equal_ty ty1 ty2);
  assert (Type.equal_dirt drt1 drt2);
  { term = Bind (comp1, abs2); ty = drty2 }

let castComp (cmp, coer) =
  let drty1 = cmp.ty and drty1', drty2 = coer.ty in
  assert (Type.equal_dirty drty1 drty1');
  { term = CastComp (cmp, coer); ty = drty2 }

let abstraction (p, c) : abstraction = { term = (p, c); ty = (p.ty, c.ty) }

let abstraction2 (p1, p2, c) : abstraction2 =
  { term = (p1, p2, c); ty = (p1.ty, p2.ty, c.ty) }

let print_effect (eff, _) ppf =
  Print.print ppf "Effect_%t" (CoreTypes.Effect.print eff)

let print_variable = CoreTypes.Variable.print ~safe:true

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PVar x -> print "%t" (print_variable x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record CoreTypes.Field.print print_pattern lst ppf
  | PVariant (lbl, None) -> print ~at_level:1 "(%t)" (CoreTypes.Label.print lbl)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "(%t @[<hov>%t@])"
        (CoreTypes.Label.print lbl)
        (print_pattern p)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.term with
  | Var x -> print "%t" (print_variable x)
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record CoreTypes.Field.print print_expression lst ppf
  | Variant (lbl, None) -> print ~at_level:1 "%t" (CoreTypes.Label.print lbl)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%t %t" (CoreTypes.Label.print lbl) (print_expression e)
  | Lambda { term = x, c; _ } ->
      print "fun (%t:%t) -> (%t)" (print_pattern x) (Type.print_ty x.ty)
        (print_computation c)
  | Handler h ->
      print
        "{@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) \
         (type b) (x : (a, b) effect) ->\n\
        \             ((match x with %t) : a -> (b -> _ computation) -> _ \
         computation)) @]}"
        (print_abstraction h.term.value_clause)
        (print_effect_clauses (Assoc.to_list h.term.effect_clauses))
  | Effect eff -> print ~at_level:2 "effect %t" (print_effect eff)
  | CastExp (e1, tc) ->
      print "(%t) |> [%t]" (print_expression e1)
        (Constraint.print_ty_coercion tc)
  | LambdaTyCoerVar (p, e) ->
      print "/\\(%t).( %t ) "
        (Type.TyCoercionParam.print p)
        (print_expression e)
  | LambdaDirtCoerVar (p, e) ->
      print "/\\(%t).( %t )"
        (Type.DirtCoercionParam.print p)
        (print_expression e)
  | ApplyTyCoercion (e, tty) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (Constraint.print_ty_coercion tty)
  | ApplyDirtCoercion (e, tty) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (Constraint.print_dirt_coercion tty)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | Apply (e1, e2) ->
      print ~at_level:1 "((%t)@ (%t))"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value (%t)" (print_expression ~max_level:0 e)
  | Match (e, []) ->
      print ~at_level:2 "(match %t with _ -> assert false)" (print_expression e)
  | Match (e, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e)
        (Print.sequence "@, | " print_abstraction lst)
  | Handle (e, c) ->
      print ~at_level:1 "handle %t %t"
        (print_expression ~max_level:0 e)
        (print_computation ~max_level:0 c)
  | LetRec (lst, c) ->
      print ~at_level:2 "let rec @[<hov>%t@] in %t"
        (Print.sequence " and " print_let_rec_abstraction lst)
        (print_computation c)
  | Call (eff, e, a) ->
      print ~at_level:1 "call (%t) (%t) ((@[fun %t@]))" (print_effect eff)
        (print_expression ~max_level:0 e)
        (print_abstraction a)
  | Op (eff, e) ->
      print ~at_level:1 "(#%t %t)" (print_effect eff) (print_expression e)
  | Bind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_computation ~max_level:0 c1)
        (print_abstraction a)
  | CastComp (c1, dc) ->
      print " ( (%t) |> [%t] ) " (print_computation c1)
        (Constraint.print_dirty_coercion dc)
  | LetVal (e1, { term = p, c1; _ }) ->
      print "let (%t = (%t)) in (%t)" (print_pattern p) (print_expression e1)
        (print_computation c1)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (_t1, _t2)) as eff), a2) :: cases ->
      print ~at_level:1 "| %t -> %t %t" (print_effect eff)
        (print_abstraction2 a2)
        (print_effect_clauses cases)

and print_abstraction { term = p, c; _ } ppf =
  Format.fprintf ppf "%t:%t ->@;<1 2> %t" (print_pattern p) (Type.print_ty p.ty)
    (print_computation c)

and print_abstraction2 { term = p1, p2, c; _ } ppf =
  Format.fprintf ppf "(fun %t %t -> %t)" (print_pattern p1) (print_pattern p2)
    (print_computation c)

and print_pure_abstraction (p, e) ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_expression e)

and print_let_abstraction { term = p, c; _ } ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_top_let_abstraction (p, c) ppf =
  match c.term with
  | Value e ->
      Format.fprintf ppf "%t = %t" (print_pattern p)
        (print_expression ~max_level:0 e)
  | _ ->
      Format.fprintf ppf "%t = run %t" (print_pattern p)
        (print_computation ~max_level:0 c)

and print_let_rec_abstraction (f, abs) ppf =
  Format.fprintf ppf "(%t : %t) %t" (print_variable f)
    (Type.print_ty (Type.Arrow abs.ty))
    (print_let_abstraction abs)

let backup_location loc locs =
  match loc with None -> Location.union locs | Some loc -> loc

let rec subst_expr sbst exp = { exp with term = subst_expr' sbst exp.term }

and subst_expr' sbst = function
  (* We could afford to check that types of x and e match *)
  | Var x as e -> (
      match Assoc.lookup x sbst with Some e' -> e'.term | None -> e)
  | Lambda abs -> Lambda (subst_abs sbst abs)
  | Handler h -> Handler (subst_handler sbst h)
  | Tuple es -> Tuple (List.map (subst_expr sbst) es)
  | Record flds -> Record (Assoc.map (subst_expr sbst) flds)
  | Variant (lbl, e) -> Variant (lbl, Option.map (subst_expr sbst) e)
  | (Const _ | Effect _) as e -> e
  | CastExp (e, tyco) -> CastExp (subst_expr sbst e, tyco)
  | LambdaTyCoerVar (tycovar, e) -> LambdaTyCoerVar (tycovar, subst_expr sbst e)
  | LambdaDirtCoerVar (dcovar, e) ->
      LambdaDirtCoerVar (dcovar, subst_expr sbst e)
  | ApplyTyCoercion (e, tyco) -> ApplyTyCoercion (subst_expr sbst e, tyco)
  | ApplyDirtCoercion (e, dco) -> ApplyDirtCoercion (subst_expr sbst e, dco)

and subst_comp sbst cmp = { cmp with term = subst_comp' sbst cmp.term }

and subst_comp' sbst = function
  | Bind (c1, c2) -> Bind (subst_comp sbst c1, subst_abs sbst c2)
  | LetVal (e1, abs) ->
      (* XXX Should we check that x does not appear in sbst? *)
      LetVal (subst_expr sbst e1, subst_abs sbst abs)
  | LetRec (li, c1) ->
      let li' =
        List.map
          (fun (x, abs) ->
            (* XXX Should we check that x does not appear in sbst? *)
            (x, subst_abs sbst abs))
          li
      in
      LetRec (li', subst_comp sbst c1)
  | Match (e, li) -> Match (subst_expr sbst e, List.map (subst_abs sbst) li)
  | Apply (e1, e2) -> Apply (subst_expr sbst e1, subst_expr sbst e2)
  | Handle (e, c) -> Handle (subst_expr sbst e, subst_comp sbst c)
  | Call (eff, e, a) -> Call (eff, subst_expr sbst e, subst_abs sbst a)
  | Value e -> Value (subst_expr sbst e)
  | CastComp (c, dtyco) -> CastComp (subst_comp sbst c, dtyco)
  | _ -> failwith __LOC__

and subst_handler sbst h =
  {
    h with
    term =
      {
        effect_clauses = Assoc.map (subst_abs2 sbst) h.term.effect_clauses;
        value_clause = subst_abs sbst h.term.value_clause;
      };
  }

and subst_abs sbst { term = p, c; ty = absty } =
  (* XXX We should assert that p & sbst have disjoint variables *)
  { term = (p, subst_comp sbst c); ty = absty }

and subst_abs2 sbst { term = p1, p2, c; ty = absty } =
  (* XXX We should assert that p1, p2 & sbst have disjoint variables *)
  { term = (p1, p2, subst_comp sbst c); ty = absty }

let assoc_equal eq flds flds' : bool =
  let rec equal_fields flds =
    match flds with
    | [] -> true
    | (f, x) :: flds -> (
        match Assoc.lookup f flds' with
        | Some x' when eq x x' -> equal_fields flds
        | _ -> false)
  in
  Assoc.length flds = Assoc.length flds' && equal_fields (Assoc.to_list flds)

let rec make_equal_pattern eqvars p p' =
  match (p.term, p'.term) with
  | PVar x, PVar x' -> Some ((x, x') :: eqvars)
  | PAs (p, x), PAs (p', x') ->
      Option.map
        (fun eqvars -> (x, x') :: eqvars)
        (make_equal_pattern eqvars p p')
  | PTuple ps, PTuple ps' ->
      List.fold_right2
        (fun p p' -> function
          | Some eqvars' -> make_equal_pattern eqvars' p p'
          | None -> None)
        ps ps' (Some eqvars)
  | PConst cst, PConst cst' when Const.equal cst cst' -> Some eqvars
  | PNonbinding, PNonbinding -> Some eqvars
  | PVariant (lbl, Some p), PVariant (lbl', Some p') when lbl = lbl' ->
      make_equal_pattern eqvars p p'
  | _, _ -> None

let rec alphaeq_expr eqvars e e' =
  match (e.term, e'.term) with
  | Var x, Var y -> List.mem (x, y) eqvars || CoreTypes.Variable.compare x y = 0
  | Lambda a, Lambda a' -> alphaeq_abs eqvars a a'
  | Handler h, Handler h' -> alphaeq_handler eqvars h h'
  | Tuple es, Tuple es' -> List.for_all2 (alphaeq_expr eqvars) es es'
  | Record flds, Record flds' -> assoc_equal (alphaeq_expr eqvars) flds flds'
  | Variant (lbl, None), Variant (lbl', None) -> lbl = lbl'
  | Variant (lbl, Some e), Variant (lbl', Some e') ->
      lbl = lbl' && alphaeq_expr eqvars e e'
  | Const cst, Const cst' -> Const.equal cst cst'
  | Effect eff, Effect eff' -> eff = eff'
  | ApplyDirtCoercion (e, dco), ApplyDirtCoercion (e', dco') ->
      dco = dco' && alphaeq_expr eqvars e e'
  | _, _ -> false

and alphaeq_comp eqvars c c' =
  match (c.term, c'.term) with
  | Bind (c1, c2), Bind (c1', c2') ->
      alphaeq_comp eqvars c1 c1' && alphaeq_abs eqvars c2 c2'
  | LetRec _, LetRec _ ->
      (* XXX Not yet implemented *)
      false
  | Match (e, li), Match (e', li') ->
      alphaeq_expr eqvars e e' && List.for_all2 (alphaeq_abs eqvars) li li'
  | Apply (e1, e2), Apply (e1', e2') ->
      alphaeq_expr eqvars e1 e1' && alphaeq_expr eqvars e2 e2'
  | Handle (e, c), Handle (e', c') ->
      alphaeq_expr eqvars e e' && alphaeq_comp eqvars c c'
  (* | Call (eff, e, a), Call (eff', e', a') ->
     eff = eff' && alphaeq_expr eqvars e e' && alphaeq_abs eqvars a a' *)
  | Value e, Value e' -> alphaeq_expr eqvars e e'
  | _, _ -> false

and alphaeq_handler eqvars h h' =
  alphaeq_abs eqvars h.term.value_clause h'.term.value_clause
  && Assoc.length h.term.effect_clauses = Assoc.length h'.term.effect_clauses
  && List.for_all
       (fun (effect, abs2) ->
         match Assoc.lookup effect h'.term.effect_clauses with
         | Some abs2' -> alphaeq_abs2 eqvars abs2 abs2'
         | None -> false)
       (Assoc.to_list h.term.effect_clauses)

(*   assoc_equal (alphaeq_abs2 eqvars) h.effect_clauses h'.effect_clauses &&
  alphaeq_abs eqvars h.value_clause h'.value_clause *)
and alphaeq_abs eqvars { term = p, c; _ } { term = p', c'; _ } =
  match make_equal_pattern eqvars p p' with
  | Some eqvars' -> alphaeq_comp eqvars' c c'
  | None -> false

and alphaeq_abs2 eqvars { term = p1, p2, c; _ } { term = p1', p2', c'; _ } =
  (* alphaeq_abs eqvars (a22a a2) (a22a a2') *)
  match make_equal_pattern eqvars p1 p1' with
  | Some eqvars' -> (
      match make_equal_pattern eqvars' p2 p2' with
      | Some eqvars'' -> alphaeq_comp eqvars'' c c'
      | None -> false)
  | None -> false

let pattern_match p e =
  (* XXX The commented out part checked that p and e had matching types *)
  (* let _, ty_e, constraints_e = e.scheme
     and _, ty_p, constraints_p = p.scheme in
     let constraints =
       Constraints.union constraints_e constraints_p |>
       Constraints.add_ty_constraint ~loc:e.location ty_e ty_p
     in
     ignore constraints; *)
  let rec extend_subst p e sbst =
    match (p.term, e.term) with
    | PVar x, _ -> Assoc.update x e sbst
    | PAs (p, x), _ ->
        let sbst = extend_subst p e sbst in
        Assoc.update x e sbst
    | PNonbinding, _ -> sbst
    | PTuple ps, Tuple es -> List.fold_right2 extend_subst ps es sbst
    | PRecord ps, Record es ->
        let rec extend_record ps es sbst =
          match ps with
          | [] -> sbst
          | (f, p) :: ps ->
              let e = List.assoc f es in
              extend_record ps es (extend_subst p e sbst)
        in
        extend_record (Assoc.to_list ps) (Assoc.to_list es) sbst
    | PVariant (lbl, None), Variant (lbl', None) when lbl = lbl' -> sbst
    | PVariant (lbl, Some p), Variant (lbl', Some e) when lbl = lbl' ->
        extend_subst p e sbst
    | PConst c, Const c' when Const.equal c c' -> sbst
    | _, _ -> assert false
  in
  extend_subst p e Assoc.empty

let ( @@@ ) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)

let ( --- ) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)

let concat_vars vars = List.fold_right ( @@@ ) vars ([], [])

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_expr e
  | LetVal (e, abs) -> free_vars_expr e @@@ free_vars_abs abs
  | LetRec (li, c1) ->
      let xs, vars =
        List.fold_right
          (fun (x, abs) (xs, vars) -> (x :: xs, free_vars_abs abs @@@ vars))
          li
          ([], free_vars_comp c1)
      in
      vars --- xs
  | Match (e, li) ->
      free_vars_expr e @@@ concat_vars (List.map free_vars_abs li)
  | Apply (e1, e2) -> free_vars_expr e1 @@@ free_vars_expr e2
  | Handle (e, c1) -> free_vars_expr e @@@ free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_expr e1 @@@ free_vars_abs a1
  | Op (_, e) -> free_vars_expr e
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
  | CastComp (c1, _dtyco) -> free_vars_comp c1

and free_vars_expr e =
  match e.term with
  | Var v -> ([], [ v ])
  | Tuple es -> concat_vars (List.map free_vars_expr es)
  | Lambda a -> free_vars_abs a
  | Handler h -> free_vars_handler h
  | Record flds ->
      Assoc.values_of flds |> List.map free_vars_expr |> concat_vars
  | Variant (_, e) -> Option.default_map ([], []) free_vars_expr e
  | CastExp (e', _tyco) -> free_vars_expr e'
  | Effect _ | Const _ -> ([], [])
  | LambdaTyCoerVar _ -> failwith __LOC__
  | LambdaDirtCoerVar _ -> failwith __LOC__
  | ApplyTyCoercion (e, _tyco) -> free_vars_expr e
  | ApplyDirtCoercion (e, _dco) -> free_vars_expr e

and free_vars_handler h =
  free_vars_abs h.term.value_clause
  @@@ (Assoc.values_of h.term.effect_clauses
      |> List.map free_vars_abs2 |> concat_vars)

and free_vars_finally_handler (h, finally_clause) =
  free_vars_handler h @@@ free_vars_abs finally_clause

and free_vars_abs { term = p, c; _ } =
  let inside, outside = free_vars_comp c --- pattern_vars p in
  (inside @ outside, [])

and free_vars_abs2 { term = p1, p2, c; _ } =
  let inside, outside =
    free_vars_comp c --- pattern_vars p2 --- pattern_vars p1
  in
  (inside @ outside, [])

let occurrences x (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x = y) ys) in
  (count inside, count outside)

let cast_expression e ty =
  let omega, cons = Constraint.fresh_ty_coer (e.ty, ty) in
  (castExp (e, omega), cons)

let cast_computation c dirty =
  let omega, cnstrs = Constraint.fresh_dirty_coer (c.ty, dirty) in
  (castComp (c, omega), cnstrs)

let cast_abstraction { term = pat, cmp; _ } dirty =
  let cmp', cnstrs = cast_computation cmp dirty in
  (abstraction (pat, cmp'), cnstrs)

(* ************************************************************************* *)
(*                         FREE VARIABLE COMPUTATION                         *)
(* ************************************************************************* *)
let rec free_params_expression e =
  Type.FreeParams.union
    (free_params_expression' e.term)
    (Type.free_params_ty e.ty)

and free_params_expression' e =
  match e with
  | Var _ -> Type.FreeParams.empty
  | Const _ -> Type.FreeParams.empty
  | Tuple es ->
      List.fold_left
        (fun free e -> Type.FreeParams.union free (free_params_expression e))
        Type.FreeParams.empty es
  | Record _ -> failwith __LOC__
  | Variant (_, e) ->
      Option.default_map Type.FreeParams.empty free_params_expression e
  | Lambda abs -> free_params_abstraction abs
  | Effect _ -> Type.FreeParams.empty
  | Handler h -> free_params_abstraction h.term.value_clause
  | CastExp (e, tc) ->
      Type.FreeParams.union (free_params_expression e)
        (Constraint.free_params_ty_coercion tc)
  | LambdaTyCoerVar (_tcp, e) -> free_params_expression e
  | LambdaDirtCoerVar (_dcp, e) -> free_params_expression e
  | ApplyTyCoercion (e, tc) ->
      Type.FreeParams.union (free_params_expression e)
        (Constraint.free_params_ty_coercion tc)
  | ApplyDirtCoercion (e, dc) ->
      Type.FreeParams.union (free_params_expression e)
        (Constraint.free_params_dirt_coercion dc)

and free_params_computation c =
  Type.FreeParams.union
    (free_params_computation' c.term)
    (Type.free_params_dirty c.ty)

and free_params_computation' c =
  match c with
  | Value e -> free_params_expression e
  | LetVal (e, abs) ->
      Type.FreeParams.union (free_params_expression e)
        (free_params_abstraction abs)
  | LetRec (defs, c) -> (
      match defs with
      | [ (_f, abs) ] ->
          free_params_abstraction abs
          |> Type.FreeParams.union (free_params_computation c)
      | _ -> failwith __LOC__)
  | Match (e, cases) ->
      List.fold_left
        (fun free case ->
          Type.FreeParams.union free (free_params_abstraction case))
        (free_params_expression e) cases
  | Apply (e1, e2) ->
      Type.FreeParams.union
        (free_params_expression e1)
        (free_params_expression e2)
  | Handle (e, c) ->
      Type.FreeParams.union (free_params_expression e)
        (free_params_computation c)
  | Call (_, _e, _awty) -> failwith __LOC__
  | Op (_, e) -> free_params_expression e
  | Bind (c, a) ->
      Type.FreeParams.union
        (free_params_computation c)
        (free_params_abstraction a)
  | CastComp (c, dc) ->
      Type.FreeParams.union
        (free_params_computation c)
        (Constraint.free_params_dirty_coercion dc)

and free_params_abstraction abs =
  Type.FreeParams.union
    (Type.free_params_abstraction_ty abs.ty)
    (free_params_abstraction' abs.term)

and free_params_abstraction' (_, c) = free_params_computation c
