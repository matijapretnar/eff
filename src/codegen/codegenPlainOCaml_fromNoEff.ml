module NoEff = NoEffSyntax
module OCamn = OcamlSyntax

let print_variable = NoEff.Variable.print ~safe:true

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p with
  | NoEff.PNVar x -> print "%t" (print_variable x)
  | NoEff.PNAs (p, x) ->
      print "%t as %t" (print_pattern p) (print_variable x)
  | NoEff.PNConst c -> Const.print c ppf
  | NoEff.PNTuple lst -> Print.tuple print_pattern lst ppf
  | NoEff.PNRecord lst -> Print.record print_pattern lst ppf
  | NoEff.PNVariant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | NoEff.PNVariant (lbl, None) -> print "%s" lbl
  | NoEff.PNVariant ("(::)", Some NoEff.PNTuple [p1; p2]) ->
      print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | NoEff.PNVariant (lbl, Some p) ->
      print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | NoEff.PNNonbinding -> print "_"


let rec print_term ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e with
  | NoEff.NVar x -> print "%t" (print_variable x)
  | NoEff.NConst c -> print "%t" (Const.print c)
  | NoEff.NTuple lst -> Print.tuple print_term lst ppf
  | NoEff.NRecord lst -> Print.record print_term lst ppf
  | NoEff.NVariant (lbl, None) -> print "%s" lbl
  | NoEff.NVariant (lbl, Some e) ->
      print ~at_level:1 "(%s %t)" lbl (print_term e)
  (* STIEN: Need to keep track of type? *)
  | NoEff.NFun (x, _, c) ->
      print "fun (%t) -> %t" (print_pattern x) (print_term c)
  | NoEff.NEffect eff -> print ~at_level:2 "effect %t" (print_effect eff)
  (* STIEN: TODO *)
  | Erasure.EHandler h ->
      print ~at_level:2
        "fun c -> handler {@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->\n             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]} c"
        (print_abstraction_with_ty h.Erasure.value_clause)
        (print_effect_clauses (Assoc.to_list h.Erasure.effect_clauses))
  | NoEff.NLetVal (p, e, c) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t" (print_pattern p)
        (print_term e) (print_term c)
  | NoEff.NApplyTerm (e1, e2) ->
      print ~at_level:1 "%t@ %t"
        (print_term ~max_level:1 e1)
        (print_term ~max_level:0 e2)
  (* STIEN: TODO *)
  | Erasure.EHandle (e, c) ->
      print ~at_level:1 "%t %t"
        (print_expression ~max_level:0 e)
        (print_computation ~max_level:0 c)
  | NoEff.NCall (eff, e, a) ->
      print ~at_level:1 "call %t %t (@[fun %t@])" (print_effect eff)
        (print_term ~max_level:0 e)
        (print_abstraction_with_ty a)
  | NoEff.NBind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_term ~max_level:0 c1)
        (print_abstraction a)
  | NoEff.NMatch (e, alist) ->
      print ~at_level:1 "match %t with %t"
        (print_term ~max_level:0 e)
        (print_cases alist)
  (* STIEN: Keep track of type? *)
  | NoEff.NLetRec ([(var, _, e)], c) ->
      print ~at_level:2 "let rec @[<hov>%t =@ %t@ in@]@ %t"
        (print_variable var) (print_term e) (print_term c)
  (* STIEN: NoEff.NOp: faalt in erasure exeff -> skeleff, wat hier doen? *)
  (* STIEN: NoEff.NBigLambdaCoer - cf. coercions *)
  (* STIEN: NoEff.NApplyCoer - cf. coercions*)
  (* STIEN: NoEff.NCast - cf. coercions *)
  (* STIEN: NoEff.NReturn - zou makkelijk moeten zijn, wel syntax checken *)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((eff_name, (t1, t2)) as eff), (p1, p2, c)) :: cases ->
      print ~at_level:1
        "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
        (print_effect eff) (print_pattern p1) (Types.print_target_ty t1)
        (print_pattern p2) (Types.print_target_ty t2) (print_term c)
        (print_effect_clauses cases)

and print_cases cases ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match cases with
  | [] -> ()
  | (p, c) :: cases ->
      print ~at_level:1 "| %t -> %t %t" (print_pattern p) (print_term c)
        (print_cases cases)

and print_abstraction (p, c) ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_term c)

and print_abstraction_with_ty (p, _, c) ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_term c)

(* ELABORATING COERCIONS AS FUNCTIONS *)
and elab_coercion (coer: NoEff.n_coercion): OCaml.term =
  match coer with
  | NoEff.NCoerRefl t ->
    let x = CoreTypes.Variable.new_fresh in
    OCaml.Lambda (OCaml.PVar x, OCaml.Var x)
  | NoEff.NCoerArrow (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    match f with
    | OCaml.Lambda (p_f, c_f) ->
      match g with
      | OCaml.Lambda (p_g, c_g) ->
        let x1 = CoreTypes.Variable.new_fresh in
        let x2 = CoreTypes.Variable.new_fresh in
        OCaml.Lambda (OCaml.PVar x1,
          OCaml.Lambda (OCaml.PVar x2,
            OCaml.Apply (g, OCaml.Apply x1, OCaml.Apply (f, x2))))
    | _ -> /* STIEN: fail here */
  | NoEff.NCoerHandler (arg, res) ->
    let f = elab_coercion arg in
    let g = elab_coercion res in
    match f with
    | OCaml.Lambda (p_f, c_f) ->
      match g with
      | OCaml.Lambda (p_g, c_g) ->
        let x1 = CoreTypes.Variable.new_fresh in
        let x2 = CoreTypes.Variable.new_fresh in
        OCaml.Lambda (OCaml.PVar x1,
          OCaml.Lambda (OCaml.PVar x2,
            // TODO
    | _ -> /* STIEN: fail here */
  | NoEff.NCoerHandToFun (arg, res) ->
    let arg_fun
  | NoEff.NCoerFunToHand (arg, res) ->
  | NoEff.NCoerQual
  | NoEff.NCoerReturn c ->
    let (pat, comp) = elab_coercion c in
    (pat, NoEff.NReturn comp)
  | NoEff.NCoerComp c ->
    fun m -> m >>= \x -> NoEff.NReturn (NoEff.NApplyTerm )
  | NoEff.NCoerUnsafe c ->
    fun x ->
      match x with
      | NoEff.NReturn y -> g y
      | _ -> error
  | NoEff.NCoerApp (c1, c2)
  | NoEff.NCoerTrans (c1, c2)
