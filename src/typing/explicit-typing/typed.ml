(** Syntax of the core language. *)

open Types
module Variable = Symbol.Make (Symbol.String)
module EffectMap = Map.Make (String)

type variable = Variable.t

type effect = OldUtils.effect * (Types.target_ty * Types.target_ty)

type 'term annotation = {term: 'term; location: Location.t}

type pattern = plain_pattern annotation

and plain_pattern =
  | PVar of variable
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (OldUtils.field, pattern) OldUtils.assoc
  | PVariant of OldUtils.label * pattern option
  | PConst of Const.t
  | PNonbinding

let rec pattern_vars p =
  match p.term with
  | PVar x -> [x]
  | PAs (p, x) -> x :: pattern_vars p
  | PTuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
  | PRecord lst -> List.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
  | PVariant (_, None) -> []
  | PVariant (_, Some p) -> pattern_vars p
  | PConst _ -> []
  | PNonbinding -> []


let annotate t loc = {term= t; location= loc}

type ty_coercion =
  | ReflTy of Types.target_ty
  | ArrowCoercion of ty_coercion * dirty_coercion
  | HandlerCoercion of dirty_coercion * dirty_coercion
  | TyCoercionVar of Params.TyCoercion.t
  | SequenceTyCoer of ty_coercion * ty_coercion
  | TupleCoercion of ty_coercion list
  | LeftArrow of ty_coercion
  | ForallTy of Params.Ty.t * ty_coercion
  | ApplyTyCoer of ty_coercion * target_ty
  | ForallDirt of Params.Dirt.t * ty_coercion
  | ApplyDirCoer of ty_coercion * dirt
  | PureCoercion of dirty_coercion
  | QualTyCoer of ct_ty * ty_coercion
  | QualDirtCoer of ct_dirt * ty_coercion
  | ApplyQualTyCoer of ty_coercion * ty_coercion
  | ApplyQualDirtCoer of ty_coercion * dirt_coercion
  | ForallSkel of Params.Skel.t * ty_coercion
  | ApplySkelCoer of ty_coercion * skeleton

and dirt_coercion =
  | ReflDirt of dirt
  | DirtCoercionVar of Params.DirtCoercion.t
  | Empty of dirt
  | UnionDirt of (Types.effect_set * dirt_coercion)
  | SequenceDirtCoer of dirt_coercion * dirt_coercion
  | DirtCoercion of dirty_coercion

and dirty_coercion =
  | BangCoercion of ty_coercion * dirt_coercion
  | RightArrow of ty_coercion
  | RightHandler of ty_coercion
  | LeftHandler of ty_coercion
  | SequenceDirtyCoer of (dirty_coercion * dirty_coercion)

(** Pure expressions *)
type expression = plain_expression annotation

and plain_expression =
  | Var of variable
  | BuiltIn of string * int
  | Const of Const.t
  | Tuple of expression list
  | Record of (OldUtils.field, expression) OldUtils.assoc
  | Variant of OldUtils.label * expression option
  | Lambda of (pattern * Types.target_ty * computation)
  | Effect of effect
  | Handler of handler
  | BigLambdaTy of Params.Ty.t * skeleton * expression
  | BigLambdaDirt of Params.Dirt.t * expression
  | BigLambdaSkel of Params.Skel.t * expression
  | CastExp of expression * ty_coercion
  | ApplyTyExp of expression * Types.target_ty
  | LambdaTyCoerVar of Params.TyCoercion.t * Types.ct_ty * expression
  | LambdaDirtCoerVar of Params.DirtCoercion.t * Types.ct_dirt * expression
  | ApplyDirtExp of expression * Types.dirt
  | ApplySkelExp of expression * Types.skeleton
  | ApplyTyCoercion of expression * ty_coercion
  | ApplyDirtCoercion of expression * dirt_coercion

(** Impure computations *)
and computation = plain_computation annotation

and plain_computation =
  | Value of expression
  | LetVal of expression * (pattern * Types.target_ty * computation)
  | LetRec of (variable * Types.target_ty * expression) list * computation
  | Match of expression * abstraction list
  | Apply of expression * expression
  | Handle of expression * computation
  | Call of effect * expression * abstraction_with_ty
  | Op of effect * expression
  | Bind of computation * abstraction
  | CastComp of computation * dirty_coercion
  | CastComp_ty of computation * ty_coercion
  | CastComp_dirt of computation * dirt_coercion

(** Handler definitions *)
and handler =
  { effect_clauses: (effect, abstraction2) OldUtils.assoc
  ; value_clause: abstraction_with_ty }

(** Abstractions that take one argument. *)
and abstraction = (pattern * computation) annotation

and abstraction_with_ty = (pattern * Types.target_ty * computation) annotation

(** Abstractions that take two arguments. *)
and abstraction2 = (pattern * pattern * computation) annotation

let abstraction_with_ty_to_abstraction a_w_ty =
  let p, _, c = a_w_ty.term in
  {term= (p, c); location= a_w_ty.location}


type omega_ct =
  | TyOmega of (Params.TyCoercion.t * Types.ct_ty)
  | DirtOmega of (Params.DirtCoercion.t * Types.ct_dirt)
  | SkelEq of skeleton * skeleton
  | TyParamHasSkel of (Params.Ty.t * skeleton)

type toplevel = (plain_toplevel * Location.t)

and plain_toplevel =
  (* | Tydef of (OldUtils.tyname, Params.t * Tctx.tydef) OldUtils.assoc *)
  (* | TopLet of (pattern * computation) list * (variable * Scheme.ty_scheme) list *)
  (* | TopLetRec of (variable * abstraction) list * (variable * Scheme.ty_scheme) list *)
  (* | External of variable * Type.ty * string *)
  | DefEffect of effect
  | Computation of computation
  | Use of string
  | Reset
  | Help
  | Quit

(* | TypeOf of computation *)

let var ?loc:(l = Location.unknown) v: expression =
  {term= Var v; location= l}

let lambda ?loc ((_, _, c) as abs) : expression =
  {term= Lambda abs; location= c.location}

let apply ?loc:(l = Location.unknown) e1 e2: computation =
  {term= Apply (e1,e2); location = l}

let call ?loc eff e abs : computation =
  {term= Call (eff, e, abs); location= e.location}

let handle ?loc e c : computation = {term= Handle (e, c); location= c.location}

let abstraction ?loc p c : abstraction = {term= (p, c); location= c.location}

let abstraction_with_ty ?loc p tty c : abstraction_with_ty =
  {term= (p, tty, c); location= c.location}


let abstraction2 ?loc p1 p2 c : abstraction2 =
  {term= (p1, p2, c); location= c.location}

let pvar ?loc:(l = Location.unknown) var : pattern =
  {term = PVar var; location = l}


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
  | PVariant (lbl, None) when lbl = OldUtils.nil -> print "[]"
  | PVariant (lbl, None) -> print "%s" lbl
  | PVariant ("(::)", Some {term= PTuple [p1; p2]}) ->
      print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | PVariant (lbl, Some p) ->
      print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | PNonbinding -> print "_"


let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.term with
  | Var x -> print "%t" (print_variable x)
  | BuiltIn (s, _) -> print "%s" s
  | Const c -> print "%t" (Const.print c)
  | Tuple lst -> Print.tuple print_expression lst ppf
  | Record lst -> Print.record print_expression lst ppf
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some e) -> print ~at_level:1 "%s %t" lbl (print_expression e)
  | Lambda (x, t, c) ->
      print "fun (%t:%t) -> (%t)" (print_pattern x) (Types.print_target_ty t)
        (print_computation c)
  | Handler h ->
      print
        "{@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->\n             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]}"
        (print_abstraction_with_ty h.value_clause)
        (print_effect_clauses h.effect_clauses)
  | Effect eff -> print ~at_level:2 "effect %t" (print_effect eff)
  | CastExp (e1, tc) ->
      print "(%t) |> [%t]" (print_expression e1) (print_ty_coercion tc)
  | BigLambdaTy (p, s, e) ->
      print "BigLambda_ty_%t:%t. %t " (Params.Ty.print p) (print_skeleton s)
        (print_expression e)
  | BigLambdaDirt (p, e) ->
      print "BigLambda_dirt_%t. %t " (Params.Dirt.print p) (print_expression e)
  | ApplyTyExp (e, tty) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (Types.print_target_ty tty)
  | LambdaTyCoerVar (p, (tty1, tty2), e) ->
      print "BigLambda_tyCoer_(%t:%t<=%t).( %t ) "
        (Params.TyCoercion.print p)
        (Types.print_target_ty tty1)
        (Types.print_target_ty tty2)
        (print_expression e)
  | LambdaDirtCoerVar (p, (tty1, tty2), e) ->
      print "BigLambda_DirtCoer_(%t:%t<=%t).( %t )"
        (Params.DirtCoercion.print p)
        (Types.print_target_dirt tty1)
        (Types.print_target_dirt tty2)
        (print_expression e)
  | ApplyDirtExp (e, tty) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (Types.print_target_dirt tty)
  | ApplyTyCoercion (e, tty) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (print_ty_coercion tty)
  | ApplyDirtCoercion (e, tty) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (print_dirt_coercion tty)
  | BigLambdaSkel (p, e) ->
      print "BigLambda_skel_%t. %t " (Params.Skel.print p) (print_expression e)
  | ApplySkelExp (e, sk) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 e)
        (Types.print_skeleton sk)


and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | Apply (e1, e2) ->
      print ~at_level:1 "((%t)@ (%t))"
        (print_expression ~max_level:1 e1)
        (print_expression ~max_level:0 e2)
  | Value e -> print ~at_level:1 "value (%t)" (print_expression ~max_level:0 e)
  | Match (e, []) ->
      print ~at_level:2 "(match %t with _ -> assert false)"
        (print_expression e)
  | Match (e, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])" (print_expression e)
        (Print.cases print_abstraction lst)
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
        (print_abstraction_with_ty a)
  | Op (eff, e) ->
      print ~at_level:1 "(#%t %t)" (print_effect eff) (print_expression e)
  | Bind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_computation ~max_level:0 c1)
        (print_abstraction a)
  | CastComp (c1, dc) ->
      print " ( (%t) |> [%t] ) " (print_computation c1)
        (print_dirty_coercion dc)
  | CastComp_ty (c1, dc) ->
      print " ( (%t) |> [%t] )" (print_computation c1) (print_ty_coercion dc)
  | CastComp_dirt (c1, dc) ->
      print "( (%t) |> [%t])" (print_computation c1) (print_dirt_coercion dc)
  | LetVal (e1, (p, ty, c1)) ->
      print "let (%t = (%t)) in (%t)" (print_pattern p) (print_expression e1)
        (print_computation c1)


and print_ty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | ReflTy p -> print "<%t>" (Types.print_target_ty p)
  | ArrowCoercion (tc, dc) ->
      print "%t -> %t" (print_ty_coercion tc) (print_dirty_coercion dc)
  | HandlerCoercion (dc1, dc2) ->
      print "%t ==> %t" (print_dirty_coercion dc1) (print_dirty_coercion dc2)
  | TyCoercionVar tcp -> print "%t " (Params.TyCoercion.print tcp)
  | SequenceTyCoer (tc1, tc2) ->
      print "%t ; %t" (print_ty_coercion tc1) (print_ty_coercion tc2)
  | PureCoercion dtyco -> print "pure(%t)" (print_dirty_coercion dtyco)
  | _ -> failwith "Not yet implemented"


and print_dirty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | BangCoercion (tc, dirtc) ->
      print "%t ! %t" (print_ty_coercion tc) (print_dirt_coercion dirtc)
  | LeftHandler tyco -> print "fst(%t)" (print_ty_coercion tyco)
  | RightHandler tyco -> print "snd(%t)" (print_ty_coercion tyco)
  | RightArrow tyco -> print "snd(%t)" (print_ty_coercion tyco)
  | SequenceDirtyCoer (c1, c2) ->
      print "(%t;%t)" (print_dirty_coercion c1) (print_dirty_coercion c2)


and print_dirt_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | ReflDirt p -> print "<%t>" (Types.print_target_dirt p)
  | DirtCoercionVar tcp -> print "%t" (Params.DirtCoercion.print tcp)
  | Empty d -> print "Empty__(%t)" (Types.print_target_dirt d)
  | UnionDirt (eset, dc) ->
      print "{%t} U %t" (Types.print_effect_set eset) (print_dirt_coercion dc)
  | DirtCoercion dtyco -> print "dirtOf(%t)" (print_dirty_coercion dtyco)
  | _ -> failwith "Not yet implemented"


and print_omega_ct ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c with
  | TyOmega (p, (ty1, ty2)) ->
      print "%t: (%t =< %t)"
        (Params.TyCoercion.print p)
        (Types.print_target_ty ty1)
        (Types.print_target_ty ty2)
  | DirtOmega (p, (ty1, ty2)) ->
      print "%t: (%t =< %t)"
        (Params.DirtCoercion.print p)
        (Types.print_target_dirt ty1)
        (Types.print_target_dirt ty2)
  | SkelEq (sk1, sk2) ->
      print "%t ~ %t" (Types.print_skeleton sk1) (Types.print_skeleton sk2)
  | TyParamHasSkel (tp, sk1) ->
      print "%t : %t" (Params.Ty.print tp) (Types.print_skeleton sk1)


and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] -> print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), a2) :: cases ->
      print ~at_level:1 "| %t -> %t %t" (print_effect eff)
        (print_abstraction2 a2)
        (print_effect_clauses cases)


and print_abstraction {term= p, c} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)


and print_abstraction_with_ty {term= p, tty, c} ppf =
  Format.fprintf ppf "%t:%t ->@;<1 2> %t" (print_pattern p)
    (Types.print_target_ty tty)
    (print_computation c)


and print_abstraction2 {term= p1, p2, c} ppf =
  Format.fprintf ppf "(fun %t %t -> %t)" (print_pattern p1) (print_pattern p2)
    (print_computation c)


and print_pure_abstraction {term= p, e} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_expression e)


and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c)


and print_top_let_abstraction (p, c) ppf =
  match c.term with
  | Value e ->
      Format.fprintf ppf "%t = %t" (print_pattern p)
        (print_expression ~max_level:0 e)
  | _ ->
      Format.fprintf ppf "%t = run %t" (print_pattern p)
        (print_computation ~max_level:0 c)


and print_let_rec_abstraction (x, ty, e) ppf =
  Format.fprintf ppf "%t : %t = %t" (print_variable x) (print_target_ty ty) (print_expression e)


let backup_location loc locs =
  match loc with None -> Location.union locs | Some loc -> loc


let rec refresh_pattern sbst p =
  let sbst', p' = refresh_pattern' sbst p.term in
  (sbst', {p with term= p'})


and refresh_pattern' sbst = function
  | PVar x ->
      let x' = Variable.refresh x in
      (OldUtils.update x x' sbst, PVar x')
  | PAs (p, x) ->
      let x' = Variable.refresh x in
      let sbst, p' = refresh_pattern (OldUtils.update x x' sbst) p in
      (sbst, PAs (p', x'))
  | PTuple ps ->
      let sbst, ps' =
        List.fold_right
          (fun p (sbst, ps') ->
            let sbst, p' = refresh_pattern sbst p in
            (sbst, p' :: ps') )
          ps (sbst, [])
      in
      (sbst, PTuple ps')
  | PRecord flds ->
      let sbst, flds' =
        List.fold_right
          (fun (lbl, p) (sbst, flds') ->
            let sbst, p' = refresh_pattern sbst p in
            (sbst, (lbl, p') :: flds') )
          flds (sbst, [])
      in
      (sbst, PRecord flds')
  | PVariant (lbl, None) -> (sbst, PVariant (lbl, None))
  | PVariant (lbl, Some p) ->
      let sbst, p' = refresh_pattern sbst p in
      (sbst, PVariant (lbl, Some p'))
  | (PConst _ | PNonbinding) as p -> (sbst, p)


let rec refresh_expr sbst e =
  let res = {e with term= refresh_expr' sbst e.term} in
  Print.debug "refres_expr" ; res


and refresh_expr' sbst = function
  | Var x as e -> (
    match OldUtils.lookup x sbst with Some x' -> Var x' | None -> e )
  | Lambda (p, ty, c) ->
      let sbst', p' = refresh_pattern sbst p in
      Lambda (p', ty, refresh_comp sbst' c)
  | Handler h -> Handler (refresh_handler sbst h)
  | Tuple es -> Tuple (List.map (refresh_expr sbst) es)
  | Record flds -> Record (OldUtils.assoc_map (refresh_expr sbst) flds)
  | Variant (lbl, e) -> Variant (lbl, OldUtils.option_map (refresh_expr sbst) e)
  | CastExp (e1, tyco) -> CastExp (refresh_expr sbst e1, tyco)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
  | BigLambdaTy (tyvar,sk,e) -> assert false
  | BigLambdaDirt (dvar,e) ->  (* TODO: refresh dirt var *)
      BigLambdaDirt (dvar, refresh_expr sbst e) 
  | BigLambdaSkel (skvar,e)-> assert false
  | LambdaTyCoerVar (tycovar,ct,e)-> assert false
  | LambdaDirtCoerVar (dcovar,ct,e) -> (* TODO: refresh dco var *)
      LambdaDirtCoerVar (dcovar,ct,refresh_expr sbst e)
  | CastExp (e,tyco) ->
      CastExp (refresh_expr sbst e, tyco)
  | ApplyTyExp (e,ty) ->
      ApplyTyExp (refresh_expr sbst e, ty)
  | ApplyDirtExp (e,d) ->
      ApplyDirtExp (refresh_expr sbst e, d)
  | ApplySkelExp (e,sk) ->
      ApplySkelExp (refresh_expr sbst e, sk)
  | ApplyTyCoercion (e,tyco) -> 
      ApplyTyCoercion (refresh_expr sbst e, tyco)
  | ApplyDirtCoercion (e,dco) ->
      ApplyDirtCoercion (refresh_expr sbst e, dco) 


and refresh_comp sbst c = {c with term= refresh_comp' sbst c.term}

and refresh_comp' sbst = function
  | Bind (c1, c2) -> Bind (refresh_comp sbst c1, refresh_abs sbst c2)
  | LetRec (li, c1) ->
      let new_xs, sbst' =
        List.fold_right
          (fun (x, _, _) (new_xs, sbst') ->
            let x' = Variable.refresh x in
            (x' :: new_xs, OldUtils.update x x' sbst') )
          li ([], sbst)
      in
      let li' =
        List.map (fun (x',(ty,e)) -> (x',ty,e)) (List.combine new_xs (List.map (fun (_, ty, e) -> (ty,refresh_expr sbst' e)) li))
      in
      LetRec (li', refresh_comp sbst' c1)
  | Match (e, li) -> Match (refresh_expr sbst e, List.map (refresh_abs sbst) li)
  | Apply (e1, e2) -> Apply (refresh_expr sbst e1, refresh_expr sbst e2)
  | Handle (e, c) -> Handle (refresh_expr sbst e, refresh_comp sbst c)
  | Call (eff, e, a) ->
      Call (eff, refresh_expr sbst e, refresh_abs_with_ty sbst a)
  | Value e -> Value (refresh_expr sbst e)
  | CastComp (c, dtyco) -> CastComp (refresh_comp sbst c, dtyco)


and refresh_handler sbst h =
  { effect_clauses= OldUtils.assoc_map (refresh_abs2 sbst) h.effect_clauses
  ; value_clause= refresh_abs_with_ty sbst h.value_clause }


and refresh_abs sbst a =
  let p, c = a.term in
  let sbst, p' = refresh_pattern sbst p in
  {a with term= (p', refresh_comp sbst c)}


and refresh_abs_with_ty sbst a =
  let p, ty, c = a.term in
  let sbst, p' = refresh_pattern sbst p in
  {a with term= (p', ty, refresh_comp sbst c)}


and refresh_abs2 sbst a2 =
  let p1, p2, c = a2.term in
  let sbst, p1' = refresh_pattern sbst p1 in
  let sbst, p2' = refresh_pattern sbst p2 in
  let c' = refresh_comp sbst c in
  {a2 with term= (p1', p2', c')}


let rec subst_expr sbst e = {e with term= subst_expr' sbst e.term}

and subst_expr' sbst = function
  | Var x as e -> (
    match OldUtils.lookup x sbst with Some e' -> e' | None -> e )
  | Lambda (xp, t, c) -> (
      let PVar v = xp.term in
      match OldUtils.lookup v sbst with
      | Some _ -> Lambda (xp, t, c)
      | None -> Lambda (xp, t, subst_comp sbst c) )
  | Handler h -> Handler (subst_handler sbst h)
  | Tuple es -> Tuple (List.map (subst_expr sbst) es)
  | Record flds -> Record (OldUtils.assoc_map (subst_expr sbst) flds)
  | Variant (lbl, e) -> Variant (lbl, OldUtils.option_map (subst_expr sbst) e)
  | (BuiltIn _ | Const _ | Effect _) as e -> e
  | CastExp (e, tyco) -> CastExp (subst_expr sbst e, tyco)
  | BigLambdaTy (tyvar, sk, e) -> BigLambdaTy (tyvar, sk, subst_expr sbst e)
  | BigLambdaDirt (dvar, e) -> BigLambdaDirt (dvar, subst_expr sbst e)
  | BigLambdaSkel (skvar, e) -> BigLambdaSkel (skvar, subst_expr sbst e)
  | ApplyTyExp (e, ty) -> ApplyTyExp (subst_expr sbst e, ty)
  | LambdaTyCoerVar (tycovar, ct, e) ->
      LambdaTyCoerVar (tycovar, ct, subst_expr sbst e)
  | LambdaDirtCoerVar (dcovar, ct, e) ->
      LambdaDirtCoerVar (dcovar, ct, subst_expr sbst e)
  | ApplyDirtExp (e, d) -> ApplyDirtExp (subst_expr sbst e, d)
  | ApplySkelExp (e, sk) -> ApplySkelExp (subst_expr sbst e, sk)
  | ApplyTyCoercion (e, tyco) -> ApplyTyCoercion (subst_expr sbst e, tyco)
  | ApplyDirtCoercion (e, dco) -> ApplyDirtCoercion (subst_expr sbst e, dco)


and subst_comp sbst c = {c with term= subst_comp' sbst c.term}

and subst_comp' sbst = function
  | Bind (c1, c2) -> Bind (subst_comp sbst c1, subst_abs sbst c2)
  | LetRec (li, c1) ->
      let li' =
        List.map
          (fun (x, ty, e) ->
            (* XXX Should we check that x does not appear in sbst? *)
            (x, ty, subst_expr sbst e) )
          li
      in
      LetRec (li', subst_comp sbst c1)
  | Match (e, li) -> Match (subst_expr sbst e, List.map (subst_abs sbst) li)
  | Apply (e1, e2) -> Apply (subst_expr sbst e1, subst_expr sbst e2)
  | Handle (e, c) -> Handle (subst_expr sbst e, subst_comp sbst c)
  | Call (eff, e, a) -> Call (eff, subst_expr sbst e, subst_abs_with_ty sbst a)
  | Value e -> Value (subst_expr sbst e)
  | CastComp (c, dtyco) -> CastComp (subst_comp sbst c, dtyco)


and subst_handler sbst h =
  { effect_clauses= OldUtils.assoc_map (subst_abs2 sbst) h.effect_clauses
  ; value_clause= subst_abs_with_ty sbst h.value_clause }


and subst_abs sbst a =
  let p, c = a.term in
  (* XXX Should we check that p & sbst have disjoint variables? *)
  {a with term= (p, subst_comp sbst c)}


and subst_abs_with_ty sbst a =
  let p, t, c = a.term in
  (* XXX Should we check that p & sbst have disjoint variables? *)
  {a with term= (p, t, subst_comp sbst c)}


and subst_abs2 sbst a2 =
  (* a2a2 @@ subst_abs sbst @@ a22a @@ a2 *)
  let p1, p2, c = a2.term in
  {a2 with term= (p1, p2, subst_comp sbst c)}


let assoc_equal eq flds flds' : bool =
  let rec equal_fields flds =
    match flds with
    | [] -> true
    | (f, x) :: flds ->
      match OldUtils.lookup f flds' with
      | Some x' when eq x x' -> equal_fields flds
      | _ -> false
  in
  List.length flds = List.length flds' && equal_fields flds


let rec make_equal_pattern eqvars p p' =
  make_equal_pattern' eqvars p.term p'.term


and make_equal_pattern' eqvars p p' =
  match (p, p') with
  | PVar x, PVar x' -> Some ((x, x') :: eqvars)
  | PAs (p, x), PAs (p', x') ->
      OldUtils.option_map
        (fun eqvars -> (x, x') :: eqvars)
        (make_equal_pattern eqvars p p')
  | PTuple ps, PTuple ps' ->
      List.fold_right2
        (fun p p' ->
          function
            | Some eqvars' -> make_equal_pattern eqvars' p p' | None -> None )
        ps ps' (Some eqvars)
  | PConst cst, PConst cst' when Const.equal cst cst' -> Some eqvars
  | PNonbinding, PNonbinding -> Some eqvars
  | PVariant (lbl, None), PVariant (lbl', None) when lbl = lbl' -> Some eqvars
  | PVariant (lbl, Some p), PVariant (lbl', Some p') when lbl = lbl' ->
      make_equal_pattern eqvars p p'
  | _, _ -> None


let rec alphaeq_expr eqvars e e' = alphaeq_expr' eqvars e.term e'.term

and alphaeq_expr' eqvars e e' =
  match (e, e') with
  | Var x, Var y -> List.mem (x, y) eqvars || Variable.compare x y = 0
  | Lambda a, Lambda a' -> assert false
  | Handler h, Handler h' -> alphaeq_handler eqvars h h'
  | Tuple es, Tuple es' -> List.for_all2 (alphaeq_expr eqvars) es es'
  | Record flds, Record flds' -> assoc_equal (alphaeq_expr eqvars) flds flds'
  | Variant (lbl, None), Variant (lbl', None) -> lbl = lbl'
  | Variant (lbl, Some e), Variant (lbl', Some e') ->
      lbl = lbl' && alphaeq_expr eqvars e e'
  | BuiltIn (f, n), BuiltIn (f', n') -> f = f' && n = n'
  | Const cst, Const cst' -> Const.equal cst cst'
  | Effect eff, Effect eff' -> eff = eff'
  | _, _ -> false


and alphaeq_comp eqvars c c' = alphaeq_comp' eqvars c.term c'.term

and alphaeq_comp' eqvars c c' =
  match (c, c') with
  | Bind (c1, c2), Bind (c1', c2') ->
      alphaeq_comp eqvars c1 c1' && alphaeq_abs eqvars c2 c2'
  | LetRec (li, c1), LetRec (li', c1') -> (* XXX Not yet implemented *)
                                          false
  | Match (e, li), Match (e', li') ->
      alphaeq_expr eqvars e e' && List.for_all2 (alphaeq_abs eqvars) li li'
  | Apply (e1, e2), Apply (e1', e2') ->
      alphaeq_expr eqvars e1 e1' && alphaeq_expr eqvars e2 e2'
  | Handle (e, c), Handle (e', c') ->
      alphaeq_expr eqvars e e' && alphaeq_comp eqvars c c'
  (*   | Call (eff, e, a), Call (eff', e', a') ->
    eff = eff' && alphaeq_expr eqvars e e' && alphaeq_abs eqvars a a' *)
  | Value e, Value e' ->
      alphaeq_expr eqvars e e'
  | _, _ -> false


and alphaeq_handler eqvars h h' = assert false

(*   assoc_equal (alphaeq_abs2 eqvars) h.effect_clauses h'.effect_clauses &&
  alphaeq_abs eqvars h.value_clause h'.value_clause *)
and alphaeq_abs eqvars {term= p, c} {term= p', c'} =
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
    match (p.term, e.term) with
    | PVar x, e -> OldUtils.update x e sbst
    | PAs (p, x), e' ->
        let sbst = extend_subst p e sbst in
        OldUtils.update x e' sbst
    | PNonbinding, _ -> sbst
    | PTuple ps, Tuple es -> List.fold_right2 extend_subst ps es sbst
    | PRecord ps, Record es -> (
        let rec extend_record ps es sbst =
          match ps with
          | [] -> sbst
          | (f, p) :: ps ->
              let e = List.assoc f es in
              extend_record ps es (extend_subst p e sbst)
        in
        try extend_record ps es sbst with Not_found ->
          Error.runtime ~loc:e.location "Incompatible records in substitution."
        )
    | PVariant (lbl, None), Variant (lbl', None) when lbl = lbl' -> sbst
    | PVariant (lbl, Some p), Variant (lbl', Some e) when lbl = lbl' ->
        extend_subst p e sbst
    | PConst c, Const c' when Const.equal c c' -> sbst
    | _, _ ->
        Error.runtime ~loc:e.location
          "Cannot substitute an expression in a pattern."
  in
  extend_subst p e []


let ( @@@ ) (inside1, outside1) (inside2, outside2) =
  (inside1 @ inside2, outside1 @ outside2)


let ( --- ) (inside, outside) bound =
  let remove_bound xs = List.filter (fun x -> not (List.mem x bound)) xs in
  (remove_bound inside, remove_bound outside)


let concat_vars vars = List.fold_right ( @@@ ) vars ([], [])

let rec free_vars_comp c =
  match c.term with
  | Value e -> free_vars_expr e
  | LetRec (li, c1) ->
      let xs, vars =
        List.fold_right
          (fun (x, ty, e) (xs, vars) -> (x :: xs, free_vars_expr e @@@ vars))
          li ([], free_vars_comp c1)
      in
      vars --- xs
  | Match (e, li) ->
      free_vars_expr e @@@ concat_vars (List.map free_vars_abs li)
  | Apply (e1, e2) -> free_vars_expr e1 @@@ free_vars_expr e2
  | Handle (e, c1) -> free_vars_expr e @@@ free_vars_comp c1
  | Call (_, e1, a1) -> free_vars_expr e1 @@@ free_vars_abs_with_ty a1
  | Bind (c1, a1) -> free_vars_comp c1 @@@ free_vars_abs a1
  | CastComp (c1, dtyco) -> free_vars_comp c1


and free_vars_expr e =
  match e.term with
  | Var v -> ([], [v])
  | Tuple es -> concat_vars (List.map free_vars_expr es)
  | Lambda a -> free_vars_plain_abs_with_ty a
  | Handler h -> free_vars_handler h
  | Record flds -> concat_vars (List.map (fun (_, e) -> free_vars_expr e) flds)
  | Variant (_, None) -> ([], [])
  | Variant (_, Some e) -> free_vars_expr e
  | CastExp (e', tyco) -> free_vars_expr e'
  | BuiltIn _ | Effect _ | Const _ -> ([], [])
  | BigLambdaTy _ -> assert false
  | BigLambdaDirt _ -> assert false
  | BigLambdaSkel _ -> assert false
  | ApplyTyExp (e, ty) -> free_vars_expr e
  | LambdaTyCoerVar _ -> assert false
  | LambdaDirtCoerVar _ -> assert false
  | ApplyDirtExp (e, d) -> free_vars_expr e
  | ApplySkelExp (e, sk) -> free_vars_expr e
  | ApplyTyCoercion (e, tyco) -> free_vars_expr e
  | ApplyDirtCoercion (e, dco) -> free_vars_expr e


and free_vars_handler h =
  free_vars_abs_with_ty h.value_clause
  @@@ concat_vars
        (List.map (fun (_, a2) -> free_vars_abs2 a2) h.effect_clauses)


and free_vars_finally_handler (h, finally_clause) =
  free_vars_handler h @@@ free_vars_abs finally_clause


and free_vars_abs a =
  let p, c = a.term in
  let inside, outside = free_vars_comp c --- pattern_vars p in
  (inside @ outside, [])


and free_vars_abs_with_ty a = free_vars_plain_abs_with_ty a.term

and free_vars_plain_abs_with_ty p_a =
  let p, _, c = p_a in
  let inside, outside = free_vars_comp c --- pattern_vars p in
  (inside @ outside, [])


and free_vars_abs2 a2 =
  (* free_vars_abs @@ a22a @@ a2 *)
  let p1, p2, c = a2.term in
  let inside, outside =
    free_vars_comp c --- pattern_vars p2 --- pattern_vars p1
  in
  (inside @ outside, [])


let occurrences x (inside, outside) =
  let count ys = List.length (List.filter (fun y -> x = y) ys) in
  (count inside, count outside)


let fresh_dirt_coer cons =
  let param = Params.DirtCoercion.fresh () in
  (DirtCoercionVar param, DirtOmega (param, cons))


let fresh_ty_with_skel skel =
  let ty_var = Params.Ty.fresh () in
  (Types.TyParam ty_var, TyParamHasSkel (ty_var, skel))


let fresh_dirty_with_skel skel =
  let ty, cons = fresh_ty_with_skel skel and drt = Types.fresh_dirt () in
  ((ty, drt), cons)


let fresh_ty_with_fresh_skel () =
  let skel_var = Params.Skel.fresh () in
  fresh_ty_with_skel (Types.SkelParam skel_var)


let fresh_dirty_with_fresh_skel () =
  let skel_var = Params.Skel.fresh () in
  fresh_dirty_with_skel (Types.SkelParam skel_var)


let fresh_ty_coer cons =
  let param = Params.TyCoercion.fresh () in
  (TyCoercionVar param, TyOmega (param, cons))


let fresh_dirty_coer ((ty1, drt1), (ty2, drt2)) =
  let ty_coer, ty_cons = fresh_ty_coer (ty1, ty2)
  and dirt_coer, dirt_cons = fresh_dirt_coer (drt1, drt2) in
  (BangCoercion (ty_coer, dirt_coer), ty_cons, dirt_cons)


let constraint_free_ty_vars = function
  | TyOmega (_, (Types.TyParam a, Types.TyParam b)) -> TyParamSet.of_list [a; b]
  | TyOmega (_, (Types.TyParam a, _)) -> TyParamSet.singleton a
  | TyOmega (_, (_, Types.TyParam a)) -> TyParamSet.singleton a
  | _ -> TyParamSet.empty


let constraint_free_row_vars = function
  | Types.ParamRow p -> DirtVarSet.singleton p
  | Types.EmptyRow -> DirtVarSet.empty


let constraint_free_dirt_vars = function
  | DirtOmega (_, (drt1, drt2)) ->
      DirtVarSet.union
        (constraint_free_row_vars drt1.Types.row)
        (constraint_free_row_vars drt2.Types.row)


let rec free_ty_vars_ty = function
  | Types.TyParam x -> [x]
  | Types.Arrow (a, c) -> free_ty_vars_ty a @ free_ty_var_dirty c
  | Types.Tuple tup -> List.flatten (List.map free_ty_vars_ty tup)
  | Types.Handler (c1, c2) -> free_ty_var_dirty c1 @ free_ty_var_dirty c2
  | Types.PrimTy _ -> []
  | Types.QualTy (_, a) -> free_ty_vars_ty a
  | Types.QualDirt (_, a) -> free_ty_vars_ty a
  | Types.TySchemeTy (ty_param, _, a) ->
      let free_a = free_ty_vars_ty a in
      List.filter (fun x -> not (List.mem x [ty_param])) free_a
  | Types.TySchemeDirt (dirt_param, a) -> free_ty_vars_ty a


and free_ty_var_dirty (a, _) = free_ty_vars_ty a

let rec free_dirt_vars_ty = function
  | Types.Arrow (a, c) -> free_dirt_vars_ty a @ free_dirt_vars_dirty c
  | Types.Tuple tup -> List.flatten (List.map free_dirt_vars_ty tup)
  | Types.Handler (c1, c2) -> free_dirt_vars_dirty c1 @ free_dirt_vars_dirty c2
  | Types.QualTy (_, a) -> free_dirt_vars_ty a
  | Types.QualDirt (_, a) -> free_dirt_vars_ty a
  | Types.TySchemeTy (ty_param, _, a) -> free_dirt_vars_ty a
  | Types.TySchemeDirt (dirt_param, a) ->
      let free_a = free_dirt_vars_ty a in
      List.filter (fun x -> not (List.mem x [dirt_param])) free_a
  | _ -> []


and free_dirt_vars_dirty (a, d) = free_dirt_vars_dirt d

and free_dirt_vars_dirt drt =
  DirtVarSet.elements (constraint_free_row_vars drt.Types.row)


let rec state_free_ty_vars st =
  List.fold_right
    (fun (_, ty) acc -> List.append (free_ty_vars_ty ty) acc)
    st []


let rec state_free_dirt_vars st =
  List.fold_right
    (fun (_, ty) acc -> List.append (free_dirt_vars_ty ty) acc)
    st []


(* free dirt variables in target terms *)

let rec free_dirt_vars_expression e =
  match e.term with
  | Var _ -> []
  | BuiltIn _ -> []
  | Const _ -> []
  | Tuple es -> List.concat (List.map free_dirt_vars_expression es)
  | Record _ -> assert false
  | Variant _ -> assert false
  | Lambda (pat, ty, c) -> free_dirt_vars_ty ty @ free_dirt_vars_computation c
  | Effect _ -> []
  | Handler h -> free_dirt_vars_abstraction_with_ty h.value_clause
  | BigLambdaTy (tp, sk, e) -> free_dirt_vars_expression e
  | BigLambdaDirt (dp, e) ->
      List.filter (fun x -> not (x == dp)) (free_dirt_vars_expression e)
  | BigLambdaSkel (skp, e) -> free_dirt_vars_expression e
  | CastExp (e, tc) ->
      free_dirt_vars_expression e @ free_dirt_vars_ty_coercion tc
  | ApplyTyExp (e, ty) -> free_dirt_vars_expression e @ free_dirt_vars_ty ty
  | LambdaTyCoerVar (tcp, ctty, e) -> free_dirt_vars_expression e
  | LambdaDirtCoerVar (dcp, ctd, e) -> free_dirt_vars_expression e
  | ApplyDirtExp (e, d) -> free_dirt_vars_expression e @ free_dirt_vars_dirt d
  | ApplySkelExp (e, sk) -> free_dirt_vars_expression e
  | ApplyTyCoercion (e, tc) ->
      free_dirt_vars_expression e @ free_dirt_vars_ty_coercion tc
  | ApplyDirtCoercion (e, dc) ->
      free_dirt_vars_expression e @ free_dirt_vars_dirt_coercion dc

and free_dirt_vars_computation c =
  match c.term with
  | Value e -> free_dirt_vars_expression e
  | LetVal (e, (p, ty, c)) ->
      free_dirt_vars_expression e @ free_dirt_vars_computation c
  | LetRec _ -> assert false
  | Match (e, cases) ->
      free_dirt_vars_expression e
      @ List.concat (List.map free_dirt_vars_abstraction cases)
  | Apply (e1, e2) ->
      free_dirt_vars_expression e1 @ free_dirt_vars_expression e2
  | Handle (e, c) -> free_dirt_vars_expression e @ free_dirt_vars_computation c
  | Call (_, e, awty) -> assert false
  | Op (_, e) -> free_dirt_vars_expression e
  | Bind (c, a) -> free_dirt_vars_computation c @ free_dirt_vars_abstraction a
  | CastComp (c, dc) ->
      free_dirt_vars_computation c @ free_dirt_vars_dirty_coercion dc
  | CastComp_ty (c, tc) ->
      free_dirt_vars_computation c @ free_dirt_vars_ty_coercion tc
  | CastComp_dirt (c, dc) ->
      free_dirt_vars_computation c @ free_dirt_vars_dirt_coercion dc

and free_dirt_vars_abstraction {term= _, c} = free_dirt_vars_computation c

and free_dirt_vars_abstraction_with_ty {term= _, ty, c} =
  free_dirt_vars_ty ty @ free_dirt_vars_computation c

and free_dirt_vars_ty_coercion = function
  | ReflTy ty -> free_dirt_vars_ty ty
  | ArrowCoercion (tc, dc) ->
      free_dirt_vars_ty_coercion tc @ free_dirt_vars_dirty_coercion dc
  | HandlerCoercion (dc1, dc2) ->
      free_dirt_vars_dirty_coercion dc1 @ free_dirt_vars_dirty_coercion dc2
  | TyCoercionVar tcp -> []
  | SequenceTyCoer (tc1, tc2) ->
      free_dirt_vars_ty_coercion tc1 @ free_dirt_vars_ty_coercion tc2
  | TupleCoercion tcs -> List.flatten (List.map free_dirt_vars_ty_coercion tcs)
  | LeftArrow tc -> free_dirt_vars_ty_coercion tc
  | ForallTy (_, tc) -> free_dirt_vars_ty_coercion tc
  | ApplyTyCoer (tc, ty) ->
      free_dirt_vars_ty_coercion tc @ free_dirt_vars_ty ty
  | ForallDirt (dp, tc) ->
      List.filter (fun x -> not (x == dp)) (free_dirt_vars_ty_coercion tc)
  | ApplyDirCoer (tc, d) ->
      free_dirt_vars_ty_coercion tc @ free_dirt_vars_dirt d
  | PureCoercion dc -> free_dirt_vars_dirty_coercion dc
  | QualTyCoer (ctty, tc) -> free_dirt_vars_ty_coercion tc
  | QualDirtCoer (ctd, tc) -> free_dirt_vars_ty_coercion tc
  | ApplyQualTyCoer (tc1, tc2) ->
      free_dirt_vars_ty_coercion tc1 @ free_dirt_vars_ty_coercion tc2
  | ApplyQualDirtCoer (tc, dc) ->
      free_dirt_vars_ty_coercion tc @ free_dirt_vars_dirt_coercion dc
  | ForallSkel (skp, tc) -> free_dirt_vars_ty_coercion tc
  | ApplySkelCoer (tc, sk) -> free_dirt_vars_ty_coercion tc

and free_dirt_vars_dirt_coercion = function
  | ReflDirt d -> free_dirt_vars_dirt d
  | DirtCoercionVar dcv -> []
  | Empty d -> free_dirt_vars_dirt d
  | UnionDirt (_, dc) -> free_dirt_vars_dirt_coercion dc
  | SequenceDirtCoer (dc1, dc2) ->
      free_dirt_vars_dirt_coercion dc1 @ free_dirt_vars_dirt_coercion dc2
  | DirtCoercion dc -> free_dirt_vars_dirty_coercion dc

and free_dirt_vars_dirty_coercion = function
  | BangCoercion (tc, dc) ->
      free_dirt_vars_ty_coercion tc @ free_dirt_vars_dirt_coercion dc
  | RightArrow tc -> free_dirt_vars_ty_coercion tc
  | RightHandler tc -> free_dirt_vars_ty_coercion tc
  | LeftHandler tc -> free_dirt_vars_ty_coercion tc
  | SequenceDirtyCoer (dc1, dc2) ->
      free_dirt_vars_dirty_coercion dc1 @ free_dirt_vars_dirty_coercion dc2
