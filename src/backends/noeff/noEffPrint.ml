open NoEffSyntax

(* print header ? *)
(* ------------------------------- *)
type ('eff_arg, 'eff_res) effect = ..

type 'a computation = 
  | Value : 'a -> 'a computation
  | Call :
      ('eff_arg, 'eff_res) effect * 'eff_arg * ('eff_res -> 'a computation)
        -> 'a computation

type ('a, 'b) handler_clauses =
  {
    value_clause : 'a -> 'b;
    effect_clauses : 'eff_arg 'eff_res. ('eff_arg, 'eff_res) effect ->
      'eff_arg -> ('eff_res -> 'b) -> 'b

  }

let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler =
    function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff
        in clause arg (fun y -> handler (k y))
  in
  handler

(* ------------------------------- *)

let print = Format.fprintf

let pp_header ppf = print ppf 
  "let reflTy"

let rec pp_sequence sep pp xs ppf =
  match xs with
    | [] -> ()
    | [x] -> pp x ppf
    | x :: xs -> print ppf ("%t" ^^ sep ^^ "%t") (pp x) (pp_sequence sep pp xs)

let pp_tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp lst)

let pp_label label ppf = CoreTypes.Label.print label ppf

let pp_tyname ty_name ppf = CoreTypes.TyName.print ty_name ppf

let pp_typaram ty_param ppf = print ppf "'ty%t" (CoreTypes.TyParam.print ~safe:true ty_param)

let pp_variable var ppf = CoreTypes.Variable.print var ppf

let pp_field pp sep (field, value) ppf =
  print ppf "%t %s %t" (CoreTypes.Field.print field) sep (pp value)

let pp_record pp sep assoc ppf =
  let lst = Assoc.to_list assoc in
  print ppf "{@[<hov>%t@]}" (pp_sequence "; " (pp_field pp sep) lst)

let rec pp_type noeff_ty ppf = 
  match noeff_ty with
    | TyVar p -> print ppf "%t" (pp_typaram p)
    | TyApply (tyName, []) -> print ppf "%t" (pp_tyname tyName)
    | TyApply (tyName, tys) -> print ppf "(%t) %t" (Print.sequence ", " pp_type tys) (pp_tyname tyName)
    | TyTuple [] -> print ppf "unit"
    | TyTuple tys -> print ppf "@[<hov>(%t)@]" (Print.sequence " * " pp_type tys)
    | TyBasic t -> print ppf "%t" (Const.print_ty t)
    | TyArrow (ty1, ty2) -> print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
    | TyHandler (ty1, ty2) -> print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
    | TyForAll (t, ty) -> print ppf "%t" (pp_type ty)
    | TyQualification (tyc, ty) -> pp_type ty ppf
    | TyComputation ty -> print ppf "%t computation" (pp_type ty)

let rec pp_pattern pat ppf = 
  match pat with
    | PVar v -> print ppf "%t" (pp_variable v)
    | PAs (p, v) -> print ppf "%t as %t" (pp_pattern p) (pp_variable v)
    | PTuple pats -> print ppf "%t" (pp_tuple pp_pattern pats)
    | PRecord rcd -> print ppf "%t" (pp_record pp_pattern "=" rcd)
    | PVariant (l, p) -> print ppf "(%t @[<hov>%t@])" (pp_label l) (pp_pattern p)
    | PConst c -> print ppf "%t" (Const.print c)
    | PNonbinding -> print ppf "_"

let pp_tuple pp tpl ppf = 
  match tpl with
    | [] -> print ppf "()"
    | xs -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp xs)

let pp_effect (e, (ty1, ty2)) ppf = CoreTypes.Effect.print e ppf

let pp_coercion coer ppf =
  match coer with
    | CoerVar v -> failwith __LOC__
    | ReflTy _ -> print ppf "ReflTyIzHeaderja"
    | ReflVar t -> failwith __LOC__
    | CoerArrow (c1, c2) -> failwith __LOC__
    | CoerHandler (c1, c2) -> failwith __LOC__
    | HandToFun (c1, c2) -> failwith __LOC__
    | FunToHand (c1, c2) -> failwith __LOC__
    | Forall (t, c) -> failwith __LOC__
    | CoerQualification (tyc, c) -> failwith __LOC__
    | CoerComputation c -> failwith __LOC__
    | CoerReturn c -> failwith __LOC__
    | Unsafe c -> failwith __LOC__
    | SequenceCoercion (c1, c2) -> failwith __LOC__
    | TupleCoercion cs -> failwith __LOC__
    | ApplyCoercion (t, cs) -> failwith __LOC__
    | ApplyTyCoer (c, ty) -> failwith __LOC__
    | ApplyQualTyCoer (c1, c2) -> failwith __LOC__
    | LeftArrow c -> failwith __LOC__

let rec pp_effect_cls eff_cls ppf = failwith __LOC__

let rec pp_term noEff_term ppf =
  match noEff_term with
    | Var v -> print ppf "%t" (pp_variable v)
    | BuiltIn (s, _) -> print ppf "%s" s
    | Const c -> print ppf "%t" (Const.print c)
    | Tuple ts -> print ppf "%t" (pp_tuple pp_term ts)
    | Record rcd -> print ppf "%t" (pp_record pp_term "=" rcd)
    | Variant (l, Tuple [hd; tl]) when l = CoreTypes.cons ->
        print ppf "@[<hov>(%t::%t)@]" (pp_term hd) (pp_term tl)
    | Variant (l, t1) -> print ppf "(%t @[<hov>%t@])" (pp_label l) (pp_term t1)
    | Lambda abs_ty -> print ppf "@[<hv 2>fun %t@]" (pp_abs_with_ty abs_ty)
    | Effect (et, _) -> CoreTypes.Effect.print et ppf
    | Apply (t1, t2) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t1) (pp_term t2)
    | BigLambdaTy (_, t) -> pp_term t ppf
    | ApplyTy (t, _) -> pp_term t ppf
    | BigLambdaCoerVar (tycp, tyc, t) -> pp_term t ppf
    | ApplyTyCoercion (t, c) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_coercion c) (pp_term t)
    | Cast (t, c) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_coercion c) (pp_term t) 
    | Return t -> print ppf "value %t" (pp_term t)
    | Handler {effect_clauses = eff_cls; value_clause = val_cl} ->
        print ppf "handler {@[<hov>value_clause = %t;@] @[<hov>effect_claueses = %t;@] }" 
        (pp_abs_with_ty val_cl) (pp_effect_cls eff_cls)
    | LetVal (t1, (pat, ty, t2)) -> print ppf "@[<hv>@[<hv>let %t = %t in@] @,%t@]" (pp_pattern pat) (pp_term t1) (pp_term t2)
    | LetRec (defs, t2) -> print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (pp_let_rec defs) (pp_term t2)
    | Match (t, cases) -> print ppf "@[<hv>(match %t with@, | %t)@]" (pp_term t)
        (pp_sequence "@, | " pp_abs cases)
    | Call (e, t, abs_ty) -> print ppf "@[<hov 2> call (%t) @,(%t) @,(%t)@]" (pp_effect e) (pp_term t) (pp_abs_with_ty abs_ty)
    | Op (e, t) -> print ppf "@[<hov 2> call (%t) @,(%t) @,(%s)@]" (pp_effect e) (pp_term t) "(fun x -> x)"
    | Bind (t, abs) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t) (pp_abs abs)
    | Handle (t1, t2) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t1) (pp_term t2)

and pp_abs (p, t) ppf = print ppf "@[<h>(%t ->@ %t)@]" (pp_pattern p) (pp_term t)

and pp_abs_with_ty (p, ty, t) ppf = print ppf "@[<h>((%t : %t) ->@ %t)@]"  (pp_pattern p) (pp_type ty) (pp_term t)

and pp_let_rec lst ppf = failwith __LOC__

let pp_def_effect (eff, (ty1, ty2)) ppf = 
  print ppf "@[effect %t : %t ->@ %t@]@." (CoreTypes.Effect.print eff) (pp_type ty1) (pp_type ty2)

let pp_let t ppf = failwith __LOC__

let pp_external name symbol_name translation ppf =
  match translation with
  | NoEffExternal.Unknown ->
      print ppf "let %t = failwith \"Unknown external symbol %s.\"@."
        (pp_variable name)
        symbol_name
  | NoEffExternal.Exists t ->
      print ppf "let %t = %s@." (pp_variable name) t

let pp_cmd cmd ppf = 
  match cmd with
    | Term t -> print ppf "%t@." (pp_term t)  (* TODO check if ok *)
    | DefEffect (e, (ty1, ty2)) -> pp_def_effect (e, (ty1, ty2)) ppf
    | TopLet defs -> print ppf "@[<hv>%t@]@." (pp_let defs)
    | TopLetRec defs -> print ppf "@[<hv>%t@]@." (pp_let_rec defs)
    | External (x, ty, f) -> (
        match Assoc.lookup f NoEffExternal.values with
          | None -> Error.runtime "Unknown external symbol %s." f
          | Some (NoEffExternal.Unknown as unknown) ->
              Print.warning
                ( "External symbol %s cannot be compiled. It has been replaced "
                 ^^ "with [failwith \"Unknown external symbol %s.\"]." )
                f f ;
                pp_external x f unknown ppf
          | Some (NoEffExternal.Exists s as known) ->
              pp_external x f known ppf )
    | TyDef defs -> failwith __LOC__
