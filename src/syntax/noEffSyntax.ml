(** Syntax of the NoEff language **)

module Variable = Symbol.Make (Symbol.String)

type variable = Variable.t

type n_effect = CoreTypes.Effect.t

type n_term =
  | NVar of variable
  | NTuple of n_term list
  | NFun of n_abstraction_with_type 
  | NApplyTerm of n_term * n_term
  | NBigLambdaTy of CoreTypes.TyParam.t * n_term
  | NTyAppl of n_term * n_type
  | NBigLambdaCoer of CoreTypes.TyCoercionParam.t * n_coerty * n_term
  | NApplyCoer of n_term * n_coercion
  | NCast of n_term * n_coercion
  | NReturn of n_term
  | NHandler of n_handler
  | NLet of n_term * n_term * n_term
  | NCall of n_effect * n_term * n_abstraction_with_type
  | NBind of n_term * n_abstraction
  | NHandle of n_term * n_term

and n_handler = 
  { effect_clauses: (n_effect, n_abstraction_2_args) Assoc.t
  ; return_clause: n_abstraction_with_type }

and n_type = 
  | NTyParam of CoreTypes.TyParam.t
  | NTyTuple of n_type list
  | NTyArrow of n_type * n_type
  | NTyHandler of n_type * n_type
  | NTyQual of n_coerty * n_type
  | NTyComp of n_type
  | NTyForall of CoreTypes.TyParam.t * n_type
  | NTyApply of CoreTypes.TyName.t * n_type list
  | NTyPrim of prim_ty

and prim_ty = NInt | NBool | NString | NFloat

and n_abstraction = (n_term * n_term)
and n_abstraction_with_type = (n_term * n_type * n_term)
and n_abstraction_2_args = (n_term * n_term * n_term)

and n_coerty = n_type * n_type

and n_coercion =
  | NCoerVar of CoreTypes.TyCoercionParam.t
  | NCoerRefl of n_type
  | NCoerArrow of n_coercion * n_coercion
  | NCoerHandler of n_coercion * n_coercion
  | NCoerHandToFun of n_coercion * n_coercion
  | NCoerFunToHand of n_coercion * n_coercion
  | NCoerForall of CoreTypes.TyParam.t * n_coercion
  | NCoerQual of n_coerty * n_coercion
  | NCoerComp of n_coercion
  | NCoerReturn of n_coercion
  | NCoerUnsafe of n_coercion
  | NCoerApp of n_coercion * n_coercion
  | NCoerInst of n_coercion * n_type
  | NCoerTrans of n_coercion * n_coercion
  (* STIEN: Might have to add more left-cases here later *)
  | NCoerLeftArrow of n_coercion
  | NCoerLeftHandler of n_coercion
  | NCoerRightArrow of n_coercion
  | NCoerRightHandler of n_coercion
  | NCoerPure of n_coercion

(********************** PRINT FUNCTIONS **********************)

let print_variable = CoreTypes.Variable.print ~safe:true

let rec print_term ?max_level t ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match t with
  | NVar x -> print "%t" (print_variable x)
  | NTuple ts -> Print.tuple print_term ts ppf
  | NFun abs -> print_abstraction_with_type abs ppf
  | NApplyTerm (t1, t2) -> print ~at_level:1 "((%t)@ (%t))"
        (print_term ~max_level:1 t1)
        (print_term ~max_level:0 t2)
  | NBigLambdaTy (x, t) ->
        print "/\\%t. %t " (CoreTypes.TyParam.print x) (print_term t)
  | NTyAppl (t, ty) -> print ~at_level:1 "((%t)@ (%t))"
        (print_term ~max_level:1 t)
        (print_type ~max_level:0 ty)
  | NBigLambdaCoer (x, coerty, t) -> 
        print "/\\%t : %t. %t " (CoreTypes.TyCoercionParam.print x) 
          (print_coerty coerty)
          (print_term t)
  | NApplyCoer (t, coer) -> print ~at_level:1 "((%t)@ (%t))"
        (print_term ~max_level:1 t)
        (print_coercion ~max_level:0 coer)
  | NCast (t, coer) ->
        print "(%t) |> [%t]" (print_term t) (print_coercion coer)
  | NReturn t -> print "return %t" (print_term t)
  | NHandler h ->
        print
        "{@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->\n             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]}"
        (print_abstraction_with_type h.return_clause)
        (print_effect_clauses (Assoc.to_list h.effect_clauses))
  | NLet (t1, t2, t3) ->
        print "let (%t = (%t)) in (%t)" (print_term t1) (print_term t2)
        (print_term t3)
  | NCall (eff, t, abs) ->
        print ~at_level:1 "call (%t) (%t) ((@[fun %t@]))" (print_effect eff)
        (print_term ~max_level:0 t)
        (print_abstraction_with_type abs)
  | NBind (t, abs) ->
        print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_term ~max_level:0 t)
        (print_abstraction abs)
  | NHandle (t, h) ->
        print ~at_level:1 "handle %t %t"
        (print_term ~max_level:0 t)
        (print_term ~max_level:0 h)

and print_coercion ?max_level coer ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match coer with
  | NCoerVar x -> CoreTypes.TyCoercionParam.print x ppf
  | NCoerRefl t -> print "< %t >" (print_type t)
  | NCoerArrow (c1, c2) -> print "%t -> %t" (print_coercion c1) (print_coercion c2)
  | NCoerHandler (c1, c2) -> print "%t ==> %t" (print_coercion c1) (print_coercion c2)
  | NCoerHandToFun (c1, c2) -> print "handToFun %t %t" (print_coercion c1) (print_coercion c2)
  | NCoerFunToHand (c1, c2) -> print "funToHand %t %t" (print_coercion c1) (print_coercion c2)
  | NCoerForall (x, c) -> print "forall %t. %t" (CoreTypes.TyParam.print x) (print_coercion c)
  | NCoerQual (ty, c) -> print "%t => %t" (print_coerty ty) (print_coercion c)
  | NCoerComp c -> print "Comp %t" (print_coercion c)
  | NCoerReturn c -> print "return %t" (print_coercion c)
  | NCoerUnsafe c -> print "unsafe %t" (print_coercion c)
  | NCoerApp (c1, c2) -> print "%t @ %t" (print_coercion c1) (print_coercion c2)
  | NCoerInst (c, t) -> print "%t [%t]" (print_coercion c) (print_type t)
  | NCoerTrans (c1, c2) -> print "%t >> %t" (print_coercion c1) (print_coercion c2)
  | NCoerLeftArrow c -> print "left %t" (print_coercion c)
  | NCoerRightArrow c -> print "right %t" (print_coercion c)
  | NCoerLeftHandler c -> print "left %t" (print_coercion c)
  | NCoerRightHandler c -> print "right %t" (print_coercion c)
  | NCoerPure c -> print "pure %t" (print_coercion c)

and print_type ?max_level ty ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | NTyParam x -> CoreTypes.TyParam.print x ppf
  | NTyTuple tys -> Print.tuple print_type tys ppf
  | NTyArrow (t1, t2) -> print "%t -> %t" (print_type t1) (print_type t2)
  | NTyHandler (t1, t2) -> print "%t ==> %t" (print_type t1) (print_type t2)
  | NTyQual (coerty, t) -> print "%t => %t" (print_coerty coerty) (print_type t)
  | NTyComp t -> print "Comp %t" (print_type t)
  | NTyForall (x, t) -> print "forall %t. %t" (CoreTypes.TyParam.print x) (print_type t)

and print_coerty ?max_level (t1, t2) ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print "%t <= %t" (print_type t1) (print_type t2)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_) as eff), a2) :: cases ->
      print ~at_level:1 "| %t -> %t %t" (print_effect eff)
        (print_abstraction2 a2)
        (print_effect_clauses cases)

and print_effect eff ppf = 
  Print.print ppf "Effect_%t" (CoreTypes.Effect.print eff)

and print_abstraction (t1, t2) ppf =
  Format.fprintf ppf "(fun %t -> %t)" (print_term t1)
    (print_term t2)

and print_abstraction2 (t1, t2, t3) ppf =
  Format.fprintf ppf "(fun %t %t -> %t)" (print_term t1) (print_term t2)
    (print_term t3)

and print_abstraction_with_type (t1, ty, t2) ppf =
  Format.fprintf ppf "%t:%t ->@;<1 2> %t" (print_term t1)
    (print_type ty)
    (print_term t2)


