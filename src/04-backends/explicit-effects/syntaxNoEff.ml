open Utils
(** Syntax of the NoEff language **)

module CoreTypes = Language.CoreTypes
module Const = Language.Const
module Variable = Symbol.Make (Symbol.String)

type n_type =
  (* Might remove this later to drop all polymorphism *)
  | NTyParam of CoreTypes.TyParam.t
  | NTyTuple of n_type list
  | NTyArrow of n_type * n_type
  | NTyHandler of n_type * n_type
  | NTyComp of n_type
  | NTyApply of CoreTypes.TyName.t * n_type list
  | NTyBasic of Const.ty

and n_coerty = n_type * n_type

type n_coercion =
  | NCoerVar of Type.TyCoercionParam.t
  | NCoerRefl
  | NCoerArrow of n_coercion * n_coercion
  | NCoerHandler of n_coercion * n_coercion
  | NCoerHandToFun of n_coercion * n_coercion
  | NCoerFunToHand of n_coercion * n_coercion
  | NCoerComp of n_coercion
  | NCoerReturn of n_coercion
  | NCoerUnsafe of n_coercion
  | NCoerForceUnsafe
  | NCoerApply of CoreTypes.TyName.t * n_coercion list
  | NCoerTuple of n_coercion list

type variable = (Variable.t, n_type) typed

let variable (x : Variable.t) (ty : n_type) = { term = x; ty }

type n_effect = CoreTypes.Effect.t * (n_type * n_type)

type n_pattern = (n_pattern', n_type) typed

and n_pattern' =
  | PNVar of variable
  | PNAs of n_pattern * variable
  | PNTuple of n_pattern list
  | PNRecord of (CoreTypes.Field.t, n_pattern) Assoc.t
  | PNVariant of CoreTypes.Label.t * n_pattern option
  | PNConst of Const.t
  | PNNonbinding

let rec pattern_vars pat =
  match pat.term with
  | PNVar x -> [ x ]
  | PNAs (p, x) -> x :: pattern_vars p
  | PNTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
  | PNRecord lst ->
      Assoc.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
  | PNVariant (_, None) -> []
  | PNVariant (_, Some p) -> pattern_vars p
  | PNConst _ -> []
  | PNNonbinding -> []

type n_term = (n_term', n_type) typed

and n_term' =
  | NVar of variable
  | NTuple of n_term list
  | NFun of n_abstraction_with_param_ty
  | NApplyTerm of n_term * n_term
  | NCast of n_term * n_coercion
  | NReturn of n_term
  | NHandler of n_handler
  | NLet of n_term * n_abstraction
  | NCall of n_effect * n_term * n_abstraction_with_param_ty
  | NBind of n_term * n_abstraction
  | NHandle of n_term * n_term
  | NConst of Const.t
  | NLetRec of n_rec_definitions * n_term
  | NMatch of n_term * n_abstraction list
  | NRecord of (CoreTypes.Field.t, n_term) Assoc.t
  | NVariant of CoreTypes.Label.t * n_term option

and n_handler = (n_handler', n_type * n_type) typed

and n_handler' = {
  effect_clauses : (n_effect, n_abstraction_2_args) Assoc.t;
  return_clause : n_abstraction_with_param_ty;
}

and n_abstraction = (n_pattern * n_term, n_type * n_type) typed

and n_abstraction_with_param_ty =
  (n_pattern * n_type * n_term, n_type * n_type) typed

and n_abstraction_2_args =
  (n_pattern * n_pattern * n_term, n_type * n_type * n_type) typed

and n_rec_definitions = (variable, n_abstraction) Assoc.t

let var (x : variable) : n_term = { term = NVar x; ty = x.ty }

let const c = { term = NConst c.term; ty = c.ty }

let tuple t = { term = NTuple t; ty = NTyTuple (List.map (fun e -> e.ty) t) }

let funct (p, ty, t) =
  let typ = (ty, t.ty) in
  { term = NFun { term = (p, ty, t); ty = typ }; ty = NTyArrow (ty, t.ty) }

let apply_term (t1, t2) =
  match t1.ty with
  | NTyArrow (_ty1, ty2) -> { term = NApplyTerm (t1, t2); ty = ty2 }
  | _ -> assert false

let cast (t1, coer) = { term = NCast (t1, coer); ty = t1.ty }

let return t = { term = NReturn t; ty = t.ty }

let handler (h : n_handler) : n_term =
  let t1, t2 = h.ty in
  { term = NHandler h; ty = NTyHandler (t1, t2) }

let n_let (t1, t2) : n_term =
  let _ty1, ty2 = t2.ty in
  { term = NLet (t1, t2); ty = ty2 }

let call (eff, t, abs) : n_term =
  let _, ty = abs.ty in
  { term = NCall (eff, t, abs); ty }

let bind (t, abs) : n_term =
  let _, out = abs.ty in
  { term = NBind (t, abs); ty = out }

let handle ((t1, t2) : n_term * n_term) : n_term =
  match t2.ty with
  | NTyHandler (_ty1, ty2) -> { term = NHandle (t1, t2); ty = ty2 }
  | _ -> assert false

let letrec (l, t) : n_term = { term = NLetRec (l, t); ty = t.ty }

let n_match (t, lst) ty : n_term = { term = NMatch (t, lst); ty }

let record _ass : n_term = failwith "Not implemented"

let variant (l, t) ty : n_term = { term = NVariant (l, t); ty }

let abstraction (p, c) : n_abstraction = { term = (p, c); ty = (p.ty, c.ty) }

type n_tydef =
  | TyDefRecord of (CoreTypes.Field.t, n_type) Assoc.t
  | TyDefSum of (CoreTypes.Label.t, n_type option) Assoc.t
  | TyDefInline of n_type

type cmd =
  | Term of n_term
  | TopLet of (variable, n_term) Assoc.t
  | TopLetRec of n_rec_definitions
  | DefEffect of n_effect
  | TyDef of (CoreTypes.TyName.t * (CoreTypes.TyParam.t list * n_tydef)) list

let rec subs_var_in_term par subs { term; ty } =
  let term' =
    match term with
    | NVar v -> if v = par then subs else term
    | NTuple ls -> NTuple (List.map (subs_var_in_term par subs) ls)
    | NFun abs -> NFun (subs_var_in_abs_with_ty par subs abs)
    | NApplyTerm (t1, t2) ->
        NApplyTerm (subs_var_in_term par subs t1, subs_var_in_term par subs t2)
    | NCast (t, c) -> NCast (subs_var_in_term par subs t, c)
    | NReturn t -> NReturn (subs_var_in_term par subs t)
    | NHandler h -> NHandler h
    | NLet (t, abs) ->
        NLet (subs_var_in_term par subs t, subs_var_in_abs par subs abs)
    | NCall (eff, t, abs) ->
        NCall
          ( eff,
            subs_var_in_term par subs t,
            subs_var_in_abs_with_ty par subs abs )
    | NBind (t, abs) ->
        NBind (subs_var_in_term par subs t, subs_var_in_abs par subs abs)
    | NHandle (t1, t2) ->
        NHandle (subs_var_in_term par subs t1, subs_var_in_term par subs t2)
    | NConst c -> NConst c
    | NLetRec (abss, t) ->
        NLetRec
          ( Assoc.map (subs_var_in_abs par subs) abss,
            subs_var_in_term par subs t )
    | NMatch (t, abss) ->
        NMatch
          (subs_var_in_term par subs t, List.map (subs_var_in_abs par subs) abss)
    | NRecord a -> NRecord (Assoc.map (subs_var_in_term par subs) a)
    | NVariant (lbl, None) -> NVariant (lbl, None)
    | NVariant (lbl, Some t) ->
        NVariant (lbl, Some (subs_var_in_term par subs t))
  in
  { term = term'; ty }

and subs_var_in_abs par subs { term = p, c; ty } =
  { term = (p, subs_var_in_term par subs c); ty }

and subs_var_in_abs_with_ty par subs { term = p, t, c; ty } =
  let p, c = (subs_var_in_abs par subs { term = (p, c); ty }).term in
  { term = (p, t, c); ty }

let occurrences (x : variable) (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x.term = y.term) ys) in
  (count inside, count outside)

let pattern_match p e =
  let rec extend_subst p e sbst =
    match (p.term, e.term) with
    | PNVar x, _ -> Some (Assoc.update x.term e sbst)
    | PNAs (p, x), _ ->
        Option.bind (extend_subst p e sbst) (fun sbst ->
            Some (Assoc.update x.term e sbst))
    | PNNonbinding, _ -> Some sbst
    | PNTuple ps, NTuple es ->
        List.fold_right2
          (fun p e sbst -> Option.bind sbst (fun sbst -> extend_subst p e sbst))
          ps es (Some sbst)
    | PNRecord ps, NRecord es ->
        let rec extend_record ps es sbst =
          match (sbst, ps) with
          | None, _ -> None
          | Some sbst, [] -> Some sbst
          | Some sbst, (f, p) :: ps ->
              let e = List.assoc f es in
              extend_record ps es (extend_subst p e sbst)
        in
        extend_record (Assoc.to_list ps) (Assoc.to_list es) (Some sbst)
    | PNVariant (lbl, None), NVariant (lbl', None) when lbl = lbl' -> Some sbst
    | PNVariant (lbl, Some p), NVariant (lbl', Some e) when lbl = lbl' ->
        extend_subst p e sbst
    | PNConst c, NConst c' when Const.equal c c' -> Some sbst
    | _, _ -> None
  in
  extend_subst p e Assoc.empty

(* Substitutions *)

let rec substitute_term sbst term =
  { term with term = substitute_term' sbst term.term }

and substitute_term' sbst n_term =
  match n_term with
  | NVar x -> (
      match Assoc.lookup x.term sbst with Some e' -> e'.term | None -> n_term)
  | NTuple t -> NTuple (List.map (substitute_term sbst) t)
  | NFun a -> NFun (substitute_abstraction_with_ty sbst a)
  | NApplyTerm (t1, t2) ->
      NApplyTerm ((substitute_term sbst) t1, (substitute_term sbst) t2)
  | NCast (t, c) -> NCast ((substitute_term sbst) t, c)
  | NReturn t -> NReturn ((substitute_term sbst) t)
  | NHandler h -> NHandler (substitue_handler sbst h)
  | NLet (t, a) -> NLet ((substitute_term sbst) t, substitute_abstraction sbst a)
  | NCall (eff, t, a) ->
      NCall
        (eff, (substitute_term sbst) t, substitute_abstraction_with_ty sbst a)
  | NBind (t, a) ->
      NBind ((substitute_term sbst) t, substitute_abstraction sbst a)
  | NHandle (t1, t2) ->
      NHandle ((substitute_term sbst) t1, (substitute_term sbst) t2)
  | NConst _ -> n_term
  | NLetRec (lst, t) ->
      NLetRec
        (Assoc.map (substitute_abstraction sbst) lst, (substitute_term sbst) t)
  | NMatch (t, abs) ->
      NMatch
        ((substitute_term sbst) t, List.map (substitute_abstraction sbst) abs)
  | NRecord recs -> NRecord (Assoc.map (substitute_term sbst) recs)
  | NVariant (lbl, a) -> NVariant (lbl, Option.map (substitute_term sbst) a)

and substitute_abstraction sbst { term = p, c; ty } =
  { term = (p, substitute_term sbst c); ty }

and substitute_abstraction_with_ty sbst ({ term = p, ty, c; _ } as t) =
  { t with term = (p, ty, substitute_term sbst c) }

and substitute_abstraction2 sbst ({ term = p1, p2, c; _ } as t) =
  { t with term = (p1, p2, (substitute_term sbst) c) }

and substitue_handler sbst h =
  {
    h with
    term =
      {
        return_clause = substitute_abstraction_with_ty sbst h.term.return_clause;
        effect_clauses =
          Assoc.map (substitute_abstraction2 sbst) h.term.effect_clauses;
      };
  }

let beta_reduce { term = pat, trm2; _ } trm1 =
  (* let { term = pat, trm2; _ } = refresh_abstraction Assoc.empty abs in *)
  let sub = pattern_match pat trm1 in
  Option.map (fun sub -> substitute_term sub trm2) sub

(* Free variables *)

let ( @@@ ) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)

let ( --- ) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)

let concat_vars vars = List.fold_right ( @@@ ) vars ([], [])

let rec free_vars term =
  match term.term with
  | NVar v -> ([], [ v ])
  | NTuple l -> concat_vars (List.map free_vars l)
  | NFun abs -> free_vars_abs_with_ty abs
  | NHandle (t1, t2) | NApplyTerm (t1, t2) -> free_vars t1 @@@ free_vars t2
  | NCast (t, _) -> free_vars t
  | NReturn t -> free_vars t
  | NHandler h -> free_vars_handler h
  | NLet (e, a) -> free_vars e @@@ free_vars_abs a
  | NCall (_, e, a) -> free_vars e @@@ free_vars_abs_with_ty a
  | NBind (e, a) -> free_vars e @@@ free_vars_abs a
  | NConst _ -> ([], [])
  | NLetRec (defs, c) ->
      (List.map free_vars_letrec (Assoc.to_list defs) |> concat_vars)
      @@@ free_vars c
  | NMatch (e, l) -> free_vars e @@@ concat_vars (List.map free_vars_abs l)
  | NRecord r -> Assoc.values_of r |> List.map free_vars |> concat_vars
  | NVariant (_, e) -> Option.default_map ([], []) free_vars e

and free_vars_handler h =
  free_vars_abs_with_ty h.term.return_clause
  @@@ (Assoc.values_of h.term.effect_clauses
      |> List.map free_vars_abs2 |> concat_vars)

and free_vars_abs { term = p, c; _ } =
  let inside, outside = free_vars c --- pattern_vars p in
  (inside @ outside, [])

and free_vars_letrec (v, { term = p, c; _ }) =
  let inside, outside = free_vars c --- pattern_vars p --- [ v ] in
  (inside @ outside, [])

and free_vars_abs_with_ty { term = p, _ty, c; ty } =
  free_vars_abs { term = (p, c); ty }

and free_vars_abs2 { term = p1, p2, c; _ } =
  let inside, outside = free_vars c --- pattern_vars p2 --- pattern_vars p1 in
  (inside @ outside, [])

(********************** PRINT FUNCTIONS **********************)

let rec print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | NTyParam x -> CoreTypes.TyParam.print x ppf
  | NTyTuple [] -> print "unit"
  | NTyTuple tys -> Print.tuple print_type tys ppf
  | NTyArrow (t1, t2) -> print "%t -> %t" (print_type t1) (print_type t2)
  | NTyHandler (t1, t2) -> print "%t ==> %t" (print_type t1) (print_type t2)
  | NTyComp t -> print "Comp %t" (print_type t)
  | NTyApply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | NTyApply (t, [ s ]) ->
      print ~at_level:1 "%t %t"
        (print_type ~max_level:1 s)
        (CoreTypes.TyName.print t)
  | NTyApply (t, ts) ->
      print ~at_level:1 "(%t) %t"
        (Print.sequence ", " print_type ts)
        (CoreTypes.TyName.print t)
  | NTyBasic t -> print "%t" (Const.print_ty t)

and print_coerty ?max_level (t1, t2) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print "%t <= %t" (print_type t1) (print_type t2)

let rec print_coercion ?max_level coer ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match coer with
  | NCoerVar x -> Type.TyCoercionParam.print x ppf
  | NCoerRefl -> print "<>"
  | NCoerArrow (c1, c2) ->
      print "(%t -> %t)" (print_coercion c1) (print_coercion c2)
  | NCoerHandler (c1, c2) ->
      print "(%t ==> %t)" (print_coercion c1) (print_coercion c2)
  | NCoerHandToFun (c1, c2) ->
      print "(handToFun %t %t)" (print_coercion c1) (print_coercion c2)
  | NCoerFunToHand (c1, c2) ->
      print "(funToHand %t %t)" (print_coercion c1) (print_coercion c2)
  | NCoerComp c -> print "(Comp %t)" (print_coercion c)
  | NCoerReturn c -> print "(return %t)" (print_coercion c)
  | NCoerUnsafe c -> print "(unsafe %t)" (print_coercion c)
  | NCoerForceUnsafe -> print "(force_unsafe)"
  | NCoerTuple _ls -> print "tuplecoer"
  | NCoerApply (_ty_name, _cs) -> print "applycoer"

let print_variable x = CoreTypes.Variable.print ~safe:true x.term

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PNVar var -> print "%t" (print_variable var)
  | PNAs (_pat, var) ->
      print "As %t = %t" (print_variable var) (print_pattern p)
  | PNTuple ps -> Print.tuple print_pattern ps ppf
  | PNRecord recs -> Print.record CoreTypes.Field.print print_pattern recs ppf
  | PNVariant (l, Some t) ->
      print "Variant %t %t" (CoreTypes.Label.print l) (print_pattern t)
  | PNVariant (l, None) -> print "Variant %t" (CoreTypes.Label.print l)
  | PNConst c -> Const.print c ppf
  | PNNonbinding -> print "_"

let rec print_term ?max_level t ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match t.term with
  | NVar x -> print "%t" (print_variable x)
  | NTuple ts -> Print.tuple print_term ts ppf
  | NFun abs -> print_abstraction_with_param_ty abs ppf
  | NApplyTerm (t1, t2) ->
      print ~at_level:1 "((%t)@ (%t))"
        (print_term ~max_level:1 t1)
        (print_term ~max_level:0 t2)
  | NCast (t, coer) -> print "(%t) |> [%t]" (print_term t) (print_coercion coer)
  | NReturn t -> print "return %t" (print_term t)
  | NHandler { term = h; _ } ->
      print
        "{@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) \
         (type b) (x : (a, b) effect) ->\n\
        \             ((match x with %t) : a -> (b -> _ computation) -> _ \
         computation)) @]}"
        (print_abstraction_with_param_ty h.return_clause)
        (print_effect_clauses (Assoc.to_list h.effect_clauses))
  | NLet (t1, { term = t2, t3; _ }) ->
      print "let (%t = (%t)) in (%t)" (print_pattern t2) (print_term t1)
        (print_term t3)
  | NCall (eff, t, abs) ->
      print ~at_level:1 "call (%t) (%t) ((@[fun %t@]))" (print_effect eff)
        (print_term ~max_level:0 t)
        (print_abstraction_with_param_ty abs)
  | NBind (t, abs) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_term ~max_level:0 t)
        (print_abstraction abs)
  | NHandle (t, h) ->
      print ~at_level:1 "handle %t %t"
        (print_term ~max_level:0 t)
        (print_term ~max_level:0 h)
  | NConst c -> Const.print c ppf
  | NLetRec (lst, t) ->
      print ~at_level:2 "let rec @[<hov>%t@] in %t"
        (Print.sequence " and " print_let_rec_abstraction (Assoc.to_list lst))
        (print_term t)
  | NMatch (t, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])" (print_term t)
        (Print.sequence "@, | " print_abstraction lst)
  | NRecord recs -> Print.record CoreTypes.Field.print print_term recs ppf
  | NVariant (l, Some t) ->
      print "Variant %t %t" (CoreTypes.Label.print l) (print_term t)
  | NVariant (l, None) -> print "Variant %t" (CoreTypes.Label.print l)

and print_let_rec_abstraction (f, abs) ppf =
  Format.fprintf ppf "%t %t" (print_variable f) (print_let_abstraction abs)

and print_let_abstraction { term = t1, t2; _ } ppf =
  Format.fprintf ppf "%t = %t" (print_pattern t1) (print_term t2)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | ((_ as eff), a2) :: cases ->
      print ~at_level:1 "| %t -> %t %t" (print_effect eff)
        (print_abstraction2 a2)
        (print_effect_clauses cases)

and print_effect (eff, _) ppf =
  Print.print ppf "Effect_%t" (CoreTypes.Effect.print eff)

and print_abstraction { term = t1, t2; _ } ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern t1) (print_term t2)

and print_abstraction_with_param_ty { term = t1, ty, t2; _ } ppf =
  Format.fprintf ppf "%t:%t ->@;<1 2> %t" (print_pattern t1) (print_type ty)
    (print_term t2)

and print_abstraction2 { term = t1, t2, t3; _ } ppf =
  Format.fprintf ppf "(fun %t %t -> %t)" (print_pattern t1) (print_pattern t2)
    (print_term t3)
