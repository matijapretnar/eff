open Utils
module CoreTypes = Language.CoreTypes

module Const = Language.Const
(** Syntax of the core language. *)

module EffectMap = Map.Make (CoreTypes.Effect)
module VariableMap = Map.Make (CoreTypes.Variable)

type variable = (CoreTypes.Variable.t, Type.ty) typed

let variable x ty = { term = x; ty }

module EffectFingerprint = Symbol.Make (Symbol.Anonymous)

type effect_fingerprint = EffectFingerprint.t

type effekt = CoreTypes.Effect.t * (Type.ty * Type.ty)

type pattern = (pattern', Type.ty) typed

and pattern' =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (CoreTypes.Field.t, pattern) Assoc.t
  | PVariant of CoreTypes.Label.t * pattern option
  | PConst of Language.Const.t
  | PNonbinding

let pVar p = { term = PVar p; ty = p.ty }

let pTuple ps =
  { term = PTuple ps; ty = Type.Tuple (List.map (fun x -> x.ty) ps) }

let rec pattern_vars pat =
  match pat.term with
  | PVar x -> [ x.term ]
  | PAs (p, x) -> x.term :: pattern_vars p
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
  | Handler of handler_clauses
  | CastExp of expression * Constraint.ty_coercion

and computation = (computation', Type.dirty) typed
(** Impure computations *)

and computation' =
  | Value of expression
  | LetVal of expression * abstraction
  | LetRec of rec_definitions * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Handle of expression * computation
  | Call of effekt * expression * abstraction
  | Bind of computation * abstraction
  | CastComp of computation * Constraint.dirty_coercion

and handler_clauses = (handler_clauses', Type.dirty * Type.dirty) typed
(** Handler definitions *)

and handler_clauses' = {
  effect_clauses : effect_clauses;
  value_clause : abstraction;
}

and effect_clauses = {
  effect_part : (effekt, abstraction2) Assoc.t;
  fingerprint : effect_fingerprint;
}

and abstraction = (pattern * computation, Type.ty * Type.dirty) typed
(** Abstractions that take one argument. *)

and rec_definitions = (variable, abstraction) Assoc.t

and abstraction2 =
  (pattern * pattern * computation, Type.ty * Type.ty * Type.dirty) typed
(** Abstractions that take two arguments. *)

let var x = { term = Var x; ty = x.ty }

let fresh_variable x ty =
  let x' = { term = CoreTypes.Variable.fresh x; ty } in
  (pVar x', var x')

let const (c : Language.Const.t) : expression =
  { term = Const c; ty = Type.TyBasic (Const.infer_ty c) }

let tuple es =
  { term = Tuple es; ty = Type.Tuple (List.map (fun e -> e.ty) es) }

let record (_ : (CoreTypes.Field.t, expression) Assoc.t) : expression =
  failwith __LOC__

let variant (lbl, e) ty = { term = Variant (lbl, e); ty }

let lambda abs = { term = Lambda abs; ty = Type.Arrow abs.ty }

let handler_clauses (value_clause : abstraction) effect_part drt_in =
  (* TODO: Check that input dirt is either handled or covered in output dirt *)
  let fingerprint = EffectFingerprint.fresh () in
  let ty_in, drty_out = value_clause.ty in
  let ty = ((ty_in, drt_in), drty_out) in
  let check_effect_clause ((_eff, (ty1, ty2)), abs) =
    let pty1, pty2, drty = abs.ty in
    assert (Type.equal_ty ty1 pty1);
    assert (Type.equal_ty (Type.Arrow (ty2, drty_out)) pty2);
    assert (Type.equal_dirty drty_out drty)
  in
  Assoc.iter check_effect_clause effect_part;
  { term = { value_clause; effect_clauses = { fingerprint; effect_part } }; ty }

let handler_with_new_value_clause hnd value_clause =
  let ty_in, drty_out = value_clause.ty in
  let (_, drt_in), _ = hnd.ty in
  {
    term = { value_clause; effect_clauses = hnd.term.effect_clauses };
    ty = ((ty_in, drt_in), drty_out);
  }

let handler_with_smaller_input_dirt hnd dcoer =
  let (ty_in, drt_in), drty_out = hnd.ty in
  let drt, drt_in' = dcoer.ty in
  assert (Type.equal_dirt drt_in drt_in');
  { term = hnd.term; ty = ((ty_in, drt), drty_out) }

let handler h =
  let drty1, drty2 = h.ty in
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

let call (eff, e, a) =
  let eff_name, (in_ty, out_ty) = eff in
  let p_ty, (r_ty, r_ty_dirt) = a.ty in
  assert (Type.equal_ty in_ty e.ty);
  assert (Type.equal_ty out_ty p_ty);
  {
    term = Call (eff, e, a);
    ty = (r_ty, Type.add_effects (Type.EffectSet.singleton eff_name) r_ty_dirt);
  }

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
  Print.print ppf "%t" (CoreTypes.Effect.print eff)

let print_variable x = CoreTypes.Variable.print ~safe:true x.term

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PVar x -> print "%t" (print_variable x)
  | PAs (p, x) -> print "%t as %t" (print_pattern p) (print_variable x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print_pattern lst ppf
  | PRecord lst -> Print.record CoreTypes.Field.print print_pattern lst ppf
  | PVariant (lbl, None) -> print ~at_level:0 "%t" (CoreTypes.Label.print lbl)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "%t %t" (CoreTypes.Label.print lbl) (print_pattern p)
  | PNonbinding -> print "_"

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  (* print "(%t : %t)" (print_expression' e.term) (Type.print_ty e.ty) *)
  print "%t" (print_expression' e.term)

and print_expression' ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | Var x -> print "%t" (print_variable x)
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record CoreTypes.Field.print print_expression lst ppf
  | Variant (lbl, None) -> print ~at_level:0 "%t" (CoreTypes.Label.print lbl)
  | Variant (lbl, Some e) ->
      print ~at_level:1 "%t %t"
        (CoreTypes.Label.print lbl)
        (print_expression ~max_level:0 e)
  | Lambda { term = x, c; _ } ->
      print ~at_level:2 "λ(%t:%t). %t" (print_pattern x) (Type.print_ty x.ty)
        (print_computation c)
  | Handler h ->
      print "{ret %t; %t}"
        (print_abstraction h.term.value_clause)
        (Print.sequence ";" print_effect_clause
           (Assoc.to_list h.term.effect_clauses.effect_part))
  | CastExp (e1, tc) ->
      print ~at_level:2 "%t ▷ %t"
        (print_expression ~max_level:0 e1)
        (Constraint.print_ty_coercion ~max_level:0 tc)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  (* print "(%t : %t)" (print_computation' c.term) (Type.print_dirty c.ty) *)
  print "%t" (print_computation' c.term)

and print_computation' ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | Apply (e1, e2) ->
      print ~at_level:1 "%t %t"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | Value e -> print ~at_level:1 "ret %t" (print_expression ~max_level:0 e)
  | Match (e, []) -> print ~at_level:3 "match %t with /" (print_expression e)
  | Match (e, lst) ->
      print ~at_level:3 "match %t with %t" (print_expression e)
        (Print.sequence "|" print_abstraction lst)
  | Handle (e, c) ->
      print ~at_level:3 "with %t handle %t"
        (print_expression ~max_level:0 e)
        (print_computation ~max_level:0 c)
  | LetRec (lst, c) ->
      print ~at_level:3 "let rec %t in %t"
        (Print.sequence " and " print_let_rec_abstraction (Assoc.to_list lst))
        (print_computation c)
  | Call (eff, e, a) ->
      print ~at_level:2 "%t(%t; %t)" (print_effect eff)
        (print_expression ~max_level:1 e)
        (print_abstraction a)
  | Bind (c2, { term = p, c1; _ }) ->
      print ~at_level:3 "do %t ← %t in %t" (print_pattern p)
        (print_computation c1)
        (print_computation ~max_level:3 c2)
  | CastComp (c1, dc) ->
      print ~at_level:2 "%t ▷ %t"
        (print_computation ~max_level:2 c1)
        (Constraint.print_dirty_coercion ~max_level:0 dc)
  | LetVal (e1, { term = p, c1; _ }) ->
      print ~at_level:3 "let %t = %t in %t" (print_pattern p)
        (print_expression e1) (print_computation c1)

and print_effect_clause (eff, a2) ppf =
  let print ?at_level = Print.print ?at_level ppf in
  print ~at_level:2 "%t %t" (print_effect eff) (print_abstraction2 a2)

and print_abstraction { term = p, c; _ } ppf =
  Format.fprintf ppf "(%t:%t) ↦ %t" (print_pattern p) (Type.print_ty p.ty)
    (print_computation c)

and print_abstraction2 { term = p1, p2, c; _ } ppf =
  Format.fprintf ppf "%t %t ↦ %t" (print_pattern p1) (print_pattern p2)
    (print_computation c)

and print_let_abstraction { term = p, c; _ } ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)

and print_let_rec_abstraction (f, abs) ppf =
  Format.fprintf ppf "(%t : %t) %t" (print_variable f)
    (Type.print_ty (Type.Arrow abs.ty))
    (print_let_abstraction abs)

let refresh_variable x = { x with term = CoreTypes.Variable.refresh x.term }

let rec refresh_pattern sbst pat =
  let sbst', pat' = refresh_pattern' sbst pat.term in
  (sbst', { pat with term = pat' })

and refresh_pattern' sbst = function
  | PVar x ->
      let x' = refresh_variable x in
      (Assoc.update x x' sbst, PVar x')
  | PAs (p, x) ->
      let x' = refresh_variable x in
      let sbst, p' = refresh_pattern (Assoc.update x x' sbst) p in
      (sbst, PAs (p', x'))
  | PTuple ps ->
      let sbst, ps' =
        List.fold_right
          (fun p (sbst, ps') ->
            let sbst, p' = refresh_pattern sbst p in
            (sbst, p' :: ps'))
          ps (sbst, [])
      in
      (sbst, PTuple ps')
  | PRecord flds ->
      let sbst, flds' =
        Assoc.fold_right
          (fun (lbl, p) (sbst, flds') ->
            let sbst, p' = refresh_pattern sbst p in
            (sbst, Assoc.update lbl p' flds'))
          flds (sbst, Assoc.empty)
      in
      (sbst, PRecord flds')
  | PVariant (lbl, Some p) ->
      let sbst, p' = refresh_pattern sbst p in
      (sbst, PVariant (lbl, Some p'))
  | (PConst _ | PNonbinding | PVariant (_, None)) as p -> (sbst, p)

let rec refresh_expression sbst exp =
  { exp with term = refresh_expression' sbst exp.term }

and refresh_expression' sbst = function
  | Var x as e -> (
      match Assoc.lookup x sbst with Some x' -> Var x' | None -> e)
  | Lambda abs -> Lambda (refresh_abstraction sbst abs)
  | Handler h -> Handler (refresh_handler sbst h)
  | Tuple es -> Tuple (List.map (refresh_expression sbst) es)
  | Record flds -> Record (Assoc.map (refresh_expression sbst) flds)
  | Variant (lbl, e) -> Variant (lbl, Option.map (refresh_expression sbst) e)
  | CastExp (e1, tyco) -> CastExp (refresh_expression sbst e1, tyco)
  | Const _ as e -> e

and refresh_computation sbst cmp =
  { cmp with term = refresh_computation' sbst cmp.term }

and refresh_computation' sbst = function
  | Bind (c1, c2) ->
      Bind (refresh_computation sbst c1, refresh_abstraction sbst c2)
  | LetRec (li, c1) ->
      let new_xs, sbst' =
        List.fold_right
          (fun (x, _) (new_xs, sbst') ->
            let x' = refresh_variable x in
            (x' :: new_xs, Assoc.update x x' sbst'))
          (Assoc.to_list li) ([], sbst)
      in
      let li' =
        List.map
          (fun (x', abs) -> (x', abs))
          (List.combine new_xs
             (List.map
                (fun (_, abs) -> refresh_abstraction sbst' abs)
                (Assoc.to_list li)))
      in
      LetRec (Assoc.of_list li', refresh_computation sbst' c1)
  | Match (e, li) ->
      Match (refresh_expression sbst e, List.map (refresh_abstraction sbst) li)
  | Apply (e1, e2) ->
      Apply (refresh_expression sbst e1, refresh_expression sbst e2)
  | Handle (e, c) ->
      Handle (refresh_expression sbst e, refresh_computation sbst c)
  | Call (eff, e, a) ->
      Call (eff, refresh_expression sbst e, refresh_abstraction sbst a)
  | Value e -> Value (refresh_expression sbst e)
  | CastComp (c, dtyco) -> CastComp (refresh_computation sbst c, dtyco)
  | LetVal (exp, abs) ->
      LetVal (refresh_expression sbst exp, refresh_abstraction sbst abs)

and refresh_handler sbst { term = h; ty } =
  {
    term =
      {
        effect_clauses =
          {
            fingerprint = h.effect_clauses.fingerprint;
            effect_part =
              Assoc.map (refresh_abstraction2 sbst) h.effect_clauses.effect_part;
          };
        value_clause = refresh_abstraction sbst h.value_clause;
      };
    ty;
  }

and refresh_abstraction sbst { term = p, c; ty } =
  let sbst, p' = refresh_pattern sbst p in
  { term = (p', refresh_computation sbst c); ty }

and refresh_abstraction2 sbst { term = p1, p2, c; ty } =
  let sbst, p1' = refresh_pattern sbst p1 in
  let sbst, p2' = refresh_pattern sbst p2 in
  let c' = refresh_computation sbst c in
  { term = (p1', p2', c'); ty }

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
  | Const _ as e -> e
  | CastExp (e, tyco) -> CastExp (subst_expr sbst e, tyco)

and subst_comp sbst cmp = { cmp with term = subst_comp' sbst cmp.term }

and subst_comp' sbst = function
  | Bind (c1, c2) -> Bind (subst_comp sbst c1, subst_abs sbst c2)
  | LetVal (e1, abs) ->
      (* XXX Should we check that x does not appear in sbst? *)
      LetVal (subst_expr sbst e1, subst_abs sbst abs)
  | LetRec (li, c1) -> LetRec (Assoc.map (subst_abs sbst) li, subst_comp sbst c1)
  | Match (e, li) -> Match (subst_expr sbst e, List.map (subst_abs sbst) li)
  | Apply (e1, e2) -> Apply (subst_expr sbst e1, subst_expr sbst e2)
  | Handle (e, c) -> Handle (subst_expr sbst e, subst_comp sbst c)
  | Call (eff, e, a) -> Call (eff, subst_expr sbst e, subst_abs sbst a)
  | Value e -> Value (subst_expr sbst e)
  | CastComp (c, dtyco) -> CastComp (subst_comp sbst c, dtyco)

and substitute_effect_clauses sbst effect_clauses =
  {
    effect_part = Assoc.map (subst_abs2 sbst) effect_clauses.effect_part;
    (* We refresh the fingerprint because the meaning of effect clauses changes *)
    fingerprint = EffectFingerprint.refresh effect_clauses.fingerprint;
  }

and subst_handler sbst h =
  {
    h with
    term =
      {
        effect_clauses = substitute_effect_clauses sbst h.term.effect_clauses;
        value_clause = subst_abs sbst h.term.value_clause;
      };
  }

and subst_abs sbst { term = p, c; ty = absty } =
  (* XXX We should assert that p & sbst have disjoint variables *)
  { term = (p, subst_comp sbst c); ty = absty }

and subst_abs2 sbst { term = p1, p2, c; ty = absty } =
  (* XXX We should assert that p1, p2 & sbst have disjoint variables *)
  { term = (p1, p2, subst_comp sbst c); ty = absty }

(* Checks if the effect handling part of handlers is the same *)
let effect_part_identical h1 h2 =
  EffectFingerprint.compare h1.effect_clauses.fingerprint
    h2.effect_clauses.fingerprint
  = 0

let pattern_match p e =
  assert (Type.equal_ty p.ty e.ty);
  let rec extend_subst p e sbst =
    match (p.term, e.term) with
    | PVar x, _ -> Some (Assoc.update x e sbst)
    | PAs (p, x), _ ->
        Option.bind (extend_subst p e sbst) (fun sbst ->
            Some (Assoc.update x e sbst))
    | PNonbinding, _ -> Some sbst
    | PTuple ps, Tuple es ->
        List.fold_right2
          (fun p e sbst -> Option.bind sbst (fun sbst -> extend_subst p e sbst))
          ps es (Some sbst)
    | PRecord ps, Record es ->
        let rec extend_record ps es sbst =
          match (sbst, ps) with
          | None, _ -> None
          | Some sbst, [] -> Some sbst
          | Some sbst, (f, p) :: ps ->
              let e = List.assoc f es in
              extend_record ps es (extend_subst p e sbst)
        in
        extend_record (Assoc.to_list ps) (Assoc.to_list es) (Some sbst)
    | PVariant (lbl, None), Variant (lbl', None) when lbl = lbl' -> Some sbst
    | PVariant (lbl, Some p), Variant (lbl', Some e) when lbl = lbl' ->
        extend_subst p e sbst
    | PConst c, Const c' when Const.equal c c' -> Some sbst
    | _, _ ->
        (* Print.debug "%t = %t" (print_pattern p) (print_expression e); *)
        None
  in
  extend_subst p e Assoc.empty

let beta_reduce abs exp =
  let { term = pat, cmp; _ } = refresh_abstraction Assoc.empty abs in
  let sub = pattern_match pat exp in
  Option.map (fun sub -> subst_comp sub cmp) sub

let ( @@@ ) occur1 occur2 =
  VariableMap.merge
    (fun _ oc1 oc2 ->
      Some (Option.value ~default:0 oc1 + Option.value ~default:0 oc2))
    occur1 occur2

let ( --- ) occur bound =
  VariableMap.filter (fun x _ -> not (List.mem x bound)) occur

let concat_vars vars = List.fold_right ( @@@ ) vars VariableMap.empty

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_expr e
  | LetVal (e, abs) -> free_vars_expr e @@@ free_vars_abs abs
  | LetRec (li, c1) ->
      let xs, vars =
        List.fold_right
          (fun (x, abs) (xs, vars) ->
            (x.term :: xs, free_vars_abs abs @@@ vars))
          (Assoc.to_list li)
          ([], free_vars_comp c1)
      in
      vars --- xs
  | Match (e, li) ->
      free_vars_expr e @@@ concat_vars (List.map free_vars_abs li)
  | Apply (e1, e2) -> free_vars_expr e1 @@@ free_vars_expr e2
  | Handle (e, c1) -> free_vars_expr e @@@ free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_expr e1 @@@ free_vars_abs a1
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
  | CastComp (c1, _dtyco) -> free_vars_comp c1

and free_vars_expr e =
  match e.term with
  | Var v -> VariableMap.singleton v.term 1
  | Tuple es -> concat_vars (List.map free_vars_expr es)
  | Lambda a -> free_vars_abs a
  | Handler h -> free_vars_handler h
  | Record flds ->
      Assoc.values_of flds |> List.map free_vars_expr |> concat_vars
  | Variant (_, e) -> Option.default_map VariableMap.empty free_vars_expr e
  | CastExp (e', _tyco) -> free_vars_expr e'
  | Const _ -> VariableMap.empty

and free_vars_handler h =
  free_vars_abs h.term.value_clause
  @@@ (Assoc.values_of h.term.effect_clauses.effect_part
      |> List.map free_vars_abs2 |> concat_vars)

and free_vars_finally_handler (h, finally_clause) =
  free_vars_handler h @@@ free_vars_abs finally_clause

and free_vars_abs { term = p, c; _ } = free_vars_comp c --- pattern_vars p

and free_vars_abs2 { term = p1, p2, c; _ } =
  free_vars_comp c --- pattern_vars p2 --- pattern_vars p1

let does_not_occur v vars =
  match VariableMap.find_opt v vars with Some x -> x = 0 | None -> true

let cast_expression e ty =
  let omega, cons = Constraint.fresh_ty_coer (e.ty, ty) in
  (castExp (e, omega), cons)

let cast_computation c dirty =
  let omega, cnstrs = Constraint.fresh_dirty_coer (c.ty, dirty) in
  (castComp (c, omega), cnstrs)

let cast_abstraction { term = pat, cmp; _ } dirty =
  let cmp', cnstrs = cast_computation cmp dirty in
  (abstraction (pat, cmp'), cnstrs)

let full_cast_abstraction { term = pat, cmp; _ } ty_in dirty_out =
  let x_pat, x_var = fresh_variable "x" ty_in in
  let exp', cnstrs1 = cast_expression x_var pat.ty in
  let cmp', cnstrs2 = cast_computation cmp dirty_out in
  ( abstraction (x_pat, letVal (exp', abstraction (pat, cmp'))),
    cnstrs1 :: cnstrs2 )

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
  | Handler h -> free_params_abstraction h.term.value_clause
  | CastExp (e, tc) ->
      Type.FreeParams.union (free_params_expression e)
        (Constraint.free_params_ty_coercion tc)

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
  | LetRec (defs, c) ->
      free_params_definitions defs
      |> Type.FreeParams.union (free_params_computation c)
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
  | Call (_, e, abs) ->
      Type.FreeParams.union (free_params_expression e)
        (free_params_abstraction abs)
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

and free_params_definitions defs =
  Type.FreeParams.union_map
    (fun (_, abs) -> free_params_abstraction abs)
    (Assoc.to_list defs)
