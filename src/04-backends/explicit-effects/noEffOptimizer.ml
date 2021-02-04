open Utils
module NoEff = SyntaxNoEff

type state = { fuel : int }

let initial_state = { fuel = !Config.optimization_fuel }

(* Optimization functions *)

(* Reductions and inlining *)

type inlinability =
  (* Pattern does not occur in in an abstraction body *)
  | NotPresent
  (* Pattern occurs, and occurs at most once in an abstraction and there is no recursion *)
  | Inlinable
  (* Pattern occurs more than once in a body of abstraction or it occurs recursively *)
  | NotInlinable

let is_atomic = function NoEff.NVar _ | NConst _ -> true | _ -> false

let applicable_pattern p vars =
  let rec check_variables = function
    | [] -> NotPresent
    | x :: xs -> (
        let inside_occ, outside_occ = NoEff.occurrences x vars in
        if inside_occ > 0 || outside_occ > 1 then NotInlinable
        else
          match check_variables xs with
          | NotPresent -> if outside_occ = 0 then NotPresent else Inlinable
          | inlinability -> inlinability)
  in
  check_variables (NoEff.pattern_vars p)

let rec optimize_ty_coercion state (n_coer : NoEff.n_coercion) =
  reduce_ty_coercion state (optimize_ty_coercion' state n_coer)

and optimize_ty_coercion' state (n_coer : NoEff.n_coercion) =
  match n_coer with
  | NCoerVar _ | NCoerRefl _ -> n_coer
  | NCoerArrow (n1, n2) ->
      NCoerArrow (optimize_ty_coercion state n1, optimize_ty_coercion state n2)
  | NCoerHandler (n1, n2) ->
      NCoerHandler (optimize_ty_coercion state n1, optimize_ty_coercion state n2)
  | NCoerHandToFun (n1, n2) ->
      NCoerHandToFun
        (optimize_ty_coercion state n1, optimize_ty_coercion state n2)
  | NCoerFunToHand (n1, n2) ->
      NCoerFunToHand
        (optimize_ty_coercion state n1, optimize_ty_coercion state n2)
  | NCoerQual (ct_ty, n2) -> NCoerQual (ct_ty, optimize_ty_coercion state n2)
  | NCoerComp n -> NCoerComp (optimize_ty_coercion state n)
  | NCoerReturn n -> NCoerReturn (optimize_ty_coercion state n)
  | NCoerUnsafe n -> NCoerUnsafe (optimize_ty_coercion state n)
  | NCoerForceUnsafe -> NCoerForceUnsafe
  | NCoerApply (t, lst) ->
      NCoerApply (t, List.map (optimize_ty_coercion state) lst)
  | NCoerTuple lst -> NCoerTuple (List.map (optimize_ty_coercion state) lst)

and reduce_ty_coercion state ty_coer = reduce_ty_coercion' state ty_coer

and reduce_ty_coercion' _state n_coer =
  match n_coer with
  | NoEff.NCoerArrow (NCoerRefl t1, NCoerRefl t2) ->
      NCoerRefl (NTyArrow (t1, t2))
  | NoEff.NCoerHandler (NCoerRefl t1, NCoerRefl t2) ->
      NCoerRefl (NTyHandler (t1, t2))
  | NCoerUnsafe (NCoerRefl _) -> NCoerForceUnsafe
  | NCoerComp (NCoerRefl t1) -> NCoerRefl t1
  | NoEff.NCoerTuple _ -> failwith ""
  | _ -> n_coer

and optimize_term state (n_term : NoEff.n_term) =
  (* Print.debug "%t" (Term.print_computation n_term); *)
  let n_term' = optimize_term' state n_term in
  (* assert (Type.dirty_types_are_equal n_term.ty n_term'.ty); *)
  let n_term'' = reduce_term state n_term' in
  (* assert (Type.dirty_types_are_equal n_term'.ty n_term''.ty); *)
  n_term''

and optimize_term' state (n_term : NoEff.n_term) =
  match n_term with
  | NVar _ | NConst _ -> n_term
  | NTuple ts -> NoEff.NTuple (List.map (optimize_term state) ts)
  | NFun (p, ty, term) -> NFun (p, ty, optimize_term state term)
  | NApplyTerm (t1, t2) ->
      NApplyTerm (optimize_term state t1, optimize_term state t2)
  | NBigLambdaCoer (p, term) -> NBigLambdaCoer (p, optimize_term state term)
  | NApplyCoer (term, coer) ->
      NApplyCoer (optimize_term state term, optimize_ty_coercion state coer)
  | NCast (term, coercion) ->
      NCast (optimize_term state term, optimize_ty_coercion state coercion)
  | NReturn term -> NReturn (optimize_term state term)
  | NHandler hnd -> NHandler (optimize_handler state hnd)
  | NLet (term, abs) ->
      NLet (optimize_term state term, optimize_abstraction state abs)
  | NCall (eff, term, abs_with_ty) ->
      NCall
        ( eff,
          optimize_term state term,
          optimize_abstraction_with_ty state abs_with_ty )
  | NBind (term, abs) ->
      NBind (optimize_term state term, optimize_abstraction state abs)
  | NHandle (t1, t2) -> NHandle (optimize_term state t1, optimize_term state t2)
  | NLetRec (abs_lst, term) ->
      NLetRec
        ( List.map (optimize_letrec_abstraction state) abs_lst,
          optimize_term state term )
  | NMatch (term, abs_list) ->
      NMatch
        ( optimize_term state term,
          List.map (optimize_abstraction state) abs_list )
  | NRecord ass -> NRecord (Assoc.map (fun t -> optimize_term state t) ass)
  | NVariant (l, opt_term) ->
      NVariant (l, Option.map (optimize_term state) opt_term)

and optimize_handler state (hnd : NoEff.n_handler) =
  {
    return_clause = optimize_abstraction_with_ty state hnd.return_clause;
    effect_clauses = Assoc.map (n_abstraction_2_args state) hnd.effect_clauses;
  }

and optimize_abstraction state ((pat, term) : NoEff.n_abstraction) =
  (pat, optimize_term state term)

and optimize_abstraction_with_ty state
    ((pat, ty, term) : NoEff.n_abstraction_with_param_ty) =
  let pat, term = optimize_abstraction state (pat, term) in
  (pat, ty, term)

and optimize_letrec_abstraction state (v, abs) =
  (v, optimize_abstraction state abs)

and n_abstraction_2_args state ((pat1, pat2, term) : NoEff.n_abstraction_2_args)
    =
  (pat1, pat2, optimize_term state term)

and substitute_pattern st t p exp =
  optimize_term st (NoEff.substitute_term (NoEff.pattern_match p exp) t)

and beta_reduce state (p, c) e =
  match applicable_pattern p (NoEff.free_vars c) with
  | Inlinable -> substitute_pattern state c p e
  | NotPresent -> c
  | NotInlinable ->
      if is_atomic e then
        (* Inline constants and variables anyway *)
        substitute_pattern state c p e
      else
        let abs = (p, c) in
        NoEff.NLet (e, abs)

and reduce_term' state (n_term : NoEff.n_term) =
  (* Print.debug "Reducing noeff term: %t" (NoEff.print_term n_term); *)
  match n_term with
  | NCast (t, (NCoerReturn (NCoerRefl _) as _c)) -> NoEff.NReturn t
  | NCast (t, NCoerRefl _) -> t
  | NBind (NReturn t, c) -> beta_reduce state c t
  | NLet (e, a) -> beta_reduce state a e
  | _ -> n_term

and reduce_term state n_term =
  let n_term = reduce_term' state n_term in
  n_term
