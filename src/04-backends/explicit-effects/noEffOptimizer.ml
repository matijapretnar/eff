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

let abstraction_inlinability (pat, cmp) =
  let vars = NoEff.free_vars cmp in
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
  check_variables (NoEff.pattern_vars pat)

let rec optimize_ty_coercion state (n_coer : NoEff.n_coercion) =
  reduce_ty_coercion state (optimize_ty_coercion' state n_coer)

and optimize_ty_coercion' state (n_coer : NoEff.n_coercion) =
  match n_coer with
  | NCoerVar _ | NCoerRefl -> n_coer
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
  | NoEff.NCoerArrow (NCoerRefl, NCoerRefl) -> NCoerRefl
  | NoEff.NCoerHandler (NCoerRefl, NCoerRefl) -> NCoerRefl
  | NCoerUnsafe NCoerRefl -> NCoerForceUnsafe
  | NCoerComp NCoerRefl -> NCoerRefl
  | NoEff.NCoerTuple coers
    when List.for_all (fun coer -> coer = NoEff.NCoerRefl) coers ->
      NCoerRefl
  | _ -> n_coer

and optimize_term state (n_term : NoEff.n_term) =
  (* Print.debug "%t" (Term.print_computation n_term); *)
  let n_term' = optimize_term' state n_term in
  (* assert (Type.dirty_types_are_equal n_term.ty n_term'.ty); *)
  let n_term'' = reduce_term state n_term' in
  (* assert (Type.dirty_types_are_equal n_term'.ty n_term''.ty); *)
  n_term''

and optimize_term' state (n_term : NoEff.n_term) =
  match n_term.term with
  | NVar _ | NConst _ -> n_term
  | NTuple ts -> NoEff.tuple (List.map (optimize_term state) ts)
  | NFun { term = p, ty1, term; _ } ->
      NoEff.funct (p, ty1, optimize_term state term)
  | NApplyTerm (t1, t2) ->
      NoEff.apply_term (optimize_term state t1, optimize_term state t2)
  | NCast (term, coercion) ->
      NoEff.cast (optimize_term state term, optimize_ty_coercion state coercion)
  | NReturn term -> NoEff.return (optimize_term state term)
  | NHandler hnd -> NoEff.handler (optimize_handler state hnd)
  | NLet (term, abs) ->
      NoEff.n_let (optimize_term state term, optimize_abstraction state abs)
  | NCall (eff, term, abs_with_ty) ->
      NoEff.call
        ( eff,
          optimize_term state term,
          optimize_abstraction_with_ty state abs_with_ty )
  | NBind (term, abs) ->
      NoEff.bind (optimize_term state term, optimize_abstraction state abs)
  | NHandle (t1, t2) ->
      NoEff.handle (optimize_term state t1, optimize_term state t2)
  | NLetRec (abs_lst, term) ->
      NoEff.letrec
        (optimize_rec_definitions state abs_lst, optimize_term state term)
  | NMatch (term, abs_list) ->
      NoEff.n_match
        ( optimize_term state term,
          List.map (optimize_abstraction state) abs_list )
        n_term.ty
  | NRecord ass -> NoEff.record (Assoc.map (fun t -> optimize_term state t) ass)
  | NVariant (l, opt_term) ->
      NoEff.variant (l, Option.map (optimize_term state) opt_term) n_term.ty

and optimize_handler state (hnd : NoEff.n_handler) : NoEff.n_handler =
  {
    hnd with
    term =
      {
        return_clause =
          optimize_abstraction_with_ty state hnd.term.return_clause;
        effect_clauses =
          Assoc.map (n_abstraction_2_args state) hnd.term.effect_clauses;
      };
  }

and optimize_rec_definitions state defs =
  Assoc.map (optimize_abstraction state) defs

and optimize_rec_definitions' state defs =
  Assoc.map NoEff.abstraction (Assoc.map (optimize_abstraction' state) defs)

and optimize_abstraction state { term = pat, term; ty } : NoEff.n_abstraction =
  { term = (pat, optimize_term state term); ty }

and optimize_abstraction' state ({ term = pat, term; _ } : NoEff.n_abstraction)
    =
  (pat, optimize_term state term)

and optimize_abstraction_with_ty state
    ({ term = pat, ty, term; ty = a_ty } : NoEff.n_abstraction_with_param_ty) =
  { term = (pat, ty, optimize_term state term); ty = a_ty }

and n_abstraction_2_args state
    ({ term = pat1, pat2, term; ty } : NoEff.n_abstraction_2_args) =
  { term = (pat1, pat2, optimize_term state term); ty }

and reduce_bool_match t abs = NoEff.n_match (t, abs) (NoEff.NTyBasic BooleanTy)

and reduce_constant_match state const (abs : NoEff.n_abstraction list) =
  let rec folder : NoEff.n_abstraction list -> NoEff.n_term option = function
    | [] -> None
    | abs :: xs -> (
        match NoEff.beta_reduce abs const with
        | Some trm -> Some (optimize_term state trm)
        | None -> folder xs)
  in
  folder abs

(*   match abs with [(p1, t1); (p2, t2)] ->  *)
and reduce_letrec l t =
  (* Is it worth it to remove unneeded let rec ? *)
  let reduce_single (({ term = p, t; ty } : NoEff.n_abstraction) as s) :
      NoEff.n_abstraction =
    match (p.term, t.term) with
    (* Let rec with pattern unwrap gets compiled to let rec with let unwrap case *)
    | ( NoEff.PNVar v,
        NoEff.NMatch ({ term = NoEff.NVar v'; _ }, [ { term = p', t'; _ } ]) )
    | ( NoEff.PNVar v,
        NoEff.NLet ({ term = NoEff.NVar v'; _ }, { term = p', t'; _ }) )
      when v.term = v'.term ->
        let vars = NoEff.free_vars t' in
        let inside, outside = NoEff.occurrences v' vars in
        if inside = 0 && outside = 0 then { term = (p', t'); ty }
        else { term = (p, t); ty }
    | _ -> s
  in
  NoEff.letrec (Assoc.map reduce_single l, t)

(* (Assoc.map reduce_single l, t) *)
and beta_reduce state ({ term = p, cmp; _ } as abs) trm2 : NoEff.n_term =
  match (abstraction_inlinability (p, cmp), trm2.term) with
  | Inlinable, _
  (* Inline constants and variables anyway *)
  | NotInlinable, (NoEff.NVar _ | NoEff.NConst _) -> (
      match NoEff.beta_reduce abs trm2 with
      | Some trm -> optimize_term state trm
      | None -> NoEff.n_let (trm2, abs))
  | NotPresent, _ -> cmp
  | NotInlinable, _ -> NoEff.n_let (trm2, abs)

and beta_reduce_with_ty state { term = p, _, cmp; ty } trm2 : NoEff.n_term =
  beta_reduce state { term = (p, cmp); ty } trm2

and reduce_term' state (n_term : NoEff.n_term) =
  (* Print.debug "Reducing noeff term: %t" (NoEff.print_term n_term); *)
  match n_term.term with
  | NCast (t, (NCoerReturn NCoerRefl as _c)) -> NoEff.return t
  | NCast (t, NCoerRefl) -> t
  | NBind ({ term = NReturn t; _ }, c) -> beta_reduce state c t
  (* | NBind ({ term = NCall (e, arg, { term = (_, ty, _) as k; _ }); _ }, f) ->
      let v = NoEff.Variable.fresh "xXx" in
      let p' = NoEff.PNVar v in
      let cont = NoEff.NApplyTerm (NoEff.NFun k, NoEff.NVar v) in
      optimize_term state (NCall (e, arg, (p', ty, NoEff.NBind (cont, f))))
  *)
  | NLet (e, a) -> beta_reduce state a e
  | NLetRec (l, t) -> reduce_letrec l t
  | NApplyTerm ({ term = NFun abs; _ }, t) -> beta_reduce_with_ty state abs t
  | NMatch (({ term = NoEff.NConst _; _ } as c), abs)
  | NMatch (({ term = NoEff.NVariant _; _ } as c), abs) -> (
      match reduce_constant_match state c abs with
      | Some t -> t
      | None -> n_term)
  | NMatch (t, abs) when n_term.ty = NoEff.NTyBasic BooleanTy ->
      reduce_bool_match t abs
  | _ -> n_term

and reduce_term state n_term =
  let n_term = reduce_term' state n_term in
  n_term
