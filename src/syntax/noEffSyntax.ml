(** Syntax of the NoEff language **)

module Variable = Symbol.Make (Symbol.String)

type variable = Variable.t

type n_effect = CoreTypes.Effect.t * (n_type * n_type)

and n_pattern =
  | PNVar of variable
  | PNAs of n_pattern * variable
  | PNTuple of n_pattern list
  | PNRecord of (CoreTypes.Field.t, n_pattern) Assoc.t
  | PNVariant of CoreTypes.Label.t * n_pattern option
  | PNConst of Const.t
  (* STIEN: Nodig voor tweede handler elaboration case van exeff naar noeff, maar eigenlijk juister om daarvoor een substitutie te maken denk ik, en dan te pattern matchen op k als variabele? Niet zeker of dat wel mag *)
  | PNCast of n_pattern * n_coercion
  | PNNonbinding

and n_term =
  | NVar of variable
  | NTuple of n_term list
  | NFun of n_abstraction_with_type
  | NApplyTerm of n_term * n_term
  | NBigLambdaCoer of CoreTypes.TyCoercionParam.t * n_coerty * n_term
  | NApplyCoer of n_term * n_coercion
  | NCast of n_term * n_coercion
  | NReturn of n_term
  | NHandler of n_handler
  | NLet of n_term * n_abstraction
  | NCall of n_effect * n_term * n_abstraction_with_type
  | NBind of n_term * n_abstraction
  | NHandle of n_term * n_term
  | NConst of Const.t
  | NEffect of n_effect
  | NLetRec of n_letrec_abstraction list * n_term
  | NMatch of n_term * n_type * n_abstraction list * Location.t
  | NOp of n_effect * n_term
  | NRecord of (CoreTypes.Field.t, n_term) Assoc.t
  | NVariant of CoreTypes.Label.t * n_term option

and n_handler =
  { effect_clauses: (n_effect, n_abstraction_2_args) Assoc.t
  ; return_clause: n_abstraction_with_type }

and n_type =
  (* Might remove this later to drop all polymorphism *)
  | NTyParam of CoreTypes.TyParam.t
  | NTyTuple of n_type list
  | NTyArrow of n_type * n_type
  | NTyHandler of n_type * n_type
  | NTyQual of n_coerty * n_type
  | NTyComp of n_type
  | NTyApply of CoreTypes.TyName.t * n_type list
  | NTyPrim of prim_ty
  | NTyBasic of string

and prim_ty = NInt | NBool | NString | NFloat

and n_tydef =
  | TyDefRecord of (CoreTypes.Field.t, n_type) Assoc.t
  | TyDefSum of (CoreTypes.Label.t, n_type option) Assoc.t
  | TyDefInline of n_type

and n_abstraction = (n_pattern * n_term)
and n_abstraction_with_type = (n_pattern * n_type * n_term)
and n_abstraction_2_args = (n_pattern * n_pattern * n_term)
and n_letrec_abstraction = (variable * n_type * n_type * n_abstraction)

and n_coerty = n_type * n_type

and n_coercion =
  | NCoerVar of CoreTypes.TyCoercionParam.t
  | NCoerRefl of n_type
  | NCoerArrow of n_coercion * n_coercion
  | NCoerHandler of n_coercion * n_coercion
  | NCoerHandToFun of n_coercion * n_coercion
  | NCoerFunToHand of n_coercion * n_coercion
  | NCoerQual of n_coerty * n_coercion
  | NCoerComp of n_coercion
  | NCoerReturn of n_coercion
  | NCoerUnsafe of n_coercion
  | NCoerApp of n_coercion * n_coercion
  | NCoerTrans of n_coercion * n_coercion
  (* STIEN: Might have to add more left-cases here later *)
  | NCoerLeftArrow of n_coercion
  | NCoerLeftHandler of n_coercion
  | NCoerRightArrow of n_coercion
  | NCoerRightHandler of n_coercion
  | NCoerPure of n_coercion
  | NCoerApply of CoreTypes.TyName.t * n_coercion list
  | NCoerTuple of n_coercion list

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
  | NLet (t1, (t2, t3)) ->
        print "let (%t = (%t)) in (%t)" (print_pattern t2) (print_term t1)
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
  | NConst c -> Const.print c ppf
  | NEffect (eff, (ty1, ty2)) -> print "Effect %t : %t %t" (CoreTypes.Effect.print eff) (print_type ty1) (print_type ty2)
  | NLetRec (lst, t) ->
        print ~at_level:2 "let rec @[<hov>%t@] in %t"
        (Print.sequence " and " print_let_rec_abstraction lst)
        (print_term t)
  | NMatch (t, _, lst, _) ->
        print ~at_level:2 "(match %t with @[<v>| %t@])" (print_term t)
        (Print.cases print_abstraction lst)
  | NOp (eff, t) -> print "Op %t %t" (print_effect eff) (print_term t)
  | NRecord recs -> Print.record CoreTypes.Field.print print_term recs ppf
  | NVariant (l, Some t) ->
        print "Variant %t %t" (CoreTypes.Label.print l) (print_term t)

and print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | PNVar var -> print "%t" (print_variable var)
  | PNAs (pat, var) -> print "As %t = %t" (print_variable var) (print_pattern p)
  | PNTuple ps -> Print.tuple print_pattern ps ppf
  | PNRecord recs -> Print.record CoreTypes.Field.print print_pattern recs ppf
  | PNVariant (l, Some t) ->
        print "Variant %t %t" (CoreTypes.Label.print l) (print_pattern t)
  | PNConst c -> Const.print c ppf
  | PNNonbinding -> print "_"

and print_let_rec_abstraction (f, arg_ty, res_ty, abs) ppf =
  Format.fprintf ppf "(%t : %t) %t"
    (print_variable f) (print_type (NTyArrow (arg_ty,res_ty))) (print_let_abstraction abs)

and print_let_abstraction (t1, t2) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern t1) (print_term t2)

and print_coercion ?max_level coer ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match coer with
  | NCoerVar x -> CoreTypes.TyCoercionParam.print x ppf
  | NCoerRefl t -> print "(< %t >)" (print_type t)
  | NCoerArrow (c1, c2) -> print "(%t -> %t)" (print_coercion c1) (print_coercion c2)
  | NCoerHandler (c1, c2) -> print "(%t ==> %t)" (print_coercion c1) (print_coercion c2)
  | NCoerHandToFun (c1, c2) -> print "(handToFun %t %t)" (print_coercion c1) (print_coercion c2)
  | NCoerFunToHand (c1, c2) -> print "(funToHand %t %t)" (print_coercion c1) (print_coercion c2)
  | NCoerQual (ty, c) -> print "(%t => %t)" (print_coerty ty) (print_coercion c)
  | NCoerComp c -> print "(Comp %t)" (print_coercion c)
  | NCoerReturn c -> print "(return %t)" (print_coercion c)
  | NCoerUnsafe c -> print "(unsafe %t)" (print_coercion c)
  | NCoerApp (c1, c2) -> print "(%t @ %t)" (print_coercion c1) (print_coercion c2)
  | NCoerTrans (c1, c2) -> print "(%t >> %t)" (print_coercion c1) (print_coercion c2)
  | NCoerLeftArrow c -> print "(leftA %t)" (print_coercion c)
  | NCoerRightArrow c -> print "(rightA %t)" (print_coercion c)
  | NCoerLeftHandler c -> print "(leftH %t)" (print_coercion c)
  | NCoerRightHandler c -> print "(rightH %t)" (print_coercion c)
  | NCoerPure c -> print "(pure %t)" (print_coercion c)
  | NCoerTuple ls -> print "tuplecoer"

and print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | NTyParam x -> CoreTypes.TyParam.print x ppf
  | NTyTuple tys -> Print.tuple print_type tys ppf
  | NTyArrow (t1, t2) -> print "%t -> %t" (print_type t1) (print_type t2)
  | NTyHandler (t1, t2) -> print "%t ==> %t" (print_type t1) (print_type t2)
  | NTyQual (coerty, t) -> print "%t => %t" (print_coerty coerty) (print_type t)
  | NTyComp t -> print "Comp %t" (print_type t)
  | NTyApply (t, []) -> print "%t" (CoreTypes.TyName.print t)
  | NTyApply (t, [s]) ->
      print ~at_level:1 "%t %t" (print_type ~max_level:1 s) (CoreTypes.TyName.print t)
  | NTyApply (t, ts) ->
      print ~at_level:1 "(%t) %t" (Print.sequence ", " print_type ts) (CoreTypes.TyName.print t)
  | NTyPrim t ->
    match t with
    | NInt -> print "Int"
    | NBool -> print "Bool"
    | NString -> print "String"
    | NFloat -> print "Float"

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

and print_effect (eff, _) ppf =
  Print.print ppf "Effect_%t" (CoreTypes.Effect.print eff)

and print_abstraction (t1, t2) ppf =
  Format.fprintf ppf "(fun %t -> %t)" (print_pattern t1)
    (print_term t2)

and print_abstraction2 (t1, t2, t3) ppf =
  Format.fprintf ppf "(fun %t %t -> %t)" (print_pattern t1) (print_pattern t2)
    (print_term t3)

and print_abstraction_with_type (t1, ty, t2) ppf =
  Format.fprintf ppf "%t:%t ->@;<1 2> %t" (print_pattern t1)
    (print_type ty)
    (print_term t2)
