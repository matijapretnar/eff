open NoEffSyntax

(* print header ? *)
(* ------------------------------- *)

(* ------------------------------- *)

let print = Format.fprintf

let pp_header ppf = print ppf 
"type ('eff_arg, 'eff_res) effect = ..

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

let rec (>>) (c : 'a computation) (f : 'a -> 'b computation) =
  match c with
  | Value x -> f x
  | Call (eff, arg, k) -> Call (eff, arg, ((fun y  -> (k y) >> f)))

let rec handler (h : ('a, 'b) handler_clauses) : 'a computation -> 'b =
  let rec handler =
    function
    | Value x -> h.value_clause x
    | Call (eff, arg, k) ->
        let clause = h.effect_clauses eff
        in clause arg (fun y -> handler (k y))
  in
  handler

let coer_refl_ty term = term

let rec coer_computation coer comp = 
  match comp with
    | Value t -> Value (coer t)
    | Call (eff, arg, k) -> Call (eff, arg, fun x -> coer_computation coer (k x)) 
      
let coer_return coer term = Value (coer term)

let coer_unsafe coer (Value v) = coer v
"

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

let protected =
  ["and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done"]
  @ ["downto"; "else"; "end"; "exception"; "external"; "false"; "for"; "fun"]
  @ ["function"; "functor"; "if"; "in"; "include"; "inherit"; "initializer"]
  @ ["land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match"; "method"]
  @ ["mod"; "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or"]
  @ ["private"; "rec"; "sig"; "struct"; "then"; "to"; "true"; "try"; "type"]
  @ ["val"; "virtual"; "when"; "while"; "with"; "continue"]

let pp_variable var ppf = 
let printer desc n =
    (* [mod] has privileges because otherwise it's stupid *)
    if desc = "mod" then Format.fprintf ppf "_op_%d (* %s *)" n desc
    else (
      if List.mem desc protected then
        Print.warning
          "Warning: Protected keyword [%s]. Must be fixed by hand!@." desc ;
      match desc.[0] with
      | 'a' .. 'z' | '_' -> Format.fprintf ppf "%s" desc
      | '$' -> (
        match desc with
        | "$c_thunk" -> Format.fprintf ppf "_comp_%d" n
        | "$id_par" -> Format.fprintf ppf "_id_%d" n
        | "$anon" -> Format.fprintf ppf "_anon_%d" n
        | "$bind" -> Format.fprintf ppf "_b_%d" n
        | _ -> Format.fprintf ppf "_x_%d" n )
      | _ -> Format.fprintf ppf "_op_%d (* %s *)" n desc )
  in
  CoreTypes.Variable.fold printer var

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

let rec pp_coercion coer ppf =
  (* The cases not matched here should be handled in pp_term *)
  match coer with
    | CoerVar v -> print ppf "CoerVar %t" (CoreTypes.TyCoercionParam.print v)
    | ReflTy _ -> print ppf "coer_refl_ty"
    | ReflVar t -> print ppf "ReflVar"
    | CoerArrow (c1, c2) -> print ppf "CoerArrow"
    | CoerHandler (c1, c2) -> print ppf "CoerHandler"
    | HandToFun (c1, c2) -> print ppf "HandToFun"
    | FunToHand (c1, c2) -> print ppf "FunToHand"
    | Forall (t, c) -> print ppf "Forall"
    | CoerQualification (tyc, c) -> print ppf "CoerQualification"
    | CoerComputation c -> print ppf "coer_computation (%t)" (pp_coercion c)
    | CoerReturn c -> print ppf "coer_return"
    | Unsafe c -> print ppf "coer_unsafe"
    | SequenceCoercion (c1, c2) -> print ppf "SequenceCoercion"
    | TupleCoercion cs -> print ppf "TupleCoercion"
    | ApplyCoercion (t, cs) -> print ppf "ApplyCoercion"
    | ApplyTyCoer (c, ty) -> print ppf "ApplyTyCoer"
    | ApplyQualTyCoer (c1, c2) -> print ppf "ApplyQualTyCoer"
    | LeftArrow c -> print ppf "LeftArrow"

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
    | Apply (t1, t2) -> (
        match t1 with 
          | Cast (t, CoerArrow (c1, c2)) -> print ppf "%t" (pp_term (Cast (Apply (t, Cast (t2, c1)), c2)))
          | Cast (t, HandToFun (c1, c2)) -> print ppf "%t" (pp_term (Cast (Handle (Return (Cast (t2, c1)), t), c2)))
          | _ -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t1) (pp_term t2))
    | BigLambdaTy (_, t) -> pp_term t ppf
    | ApplyTy (Cast (t, Forall (a, c)), ty) -> print ppf "%t" 
        (pp_term (Cast (ApplyTy (t, ty), NoEffSubstitute.substitute_tyvar_in_coercion a ty c)))
    | ApplyTy (t, _) -> pp_term t ppf
    | BigLambdaCoerVar (tycp, tyc, t) -> print ppf "%t" (pp_term t)
    | ApplyTyCoercion (BigLambdaCoerVar (cp, pi, t), c1) -> print ppf "%t" (pp_term (NoEffSubstitute.substitute_coer_var_in_term cp c1 t))
    | ApplyTyCoercion (Cast (t, CoerQualification (pi, c1)), c2) -> print ppf "%t" (pp_term (Cast (ApplyTyCoercion (t, c2), c1)))
    | ApplyTyCoercion (t, c) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t) (pp_coercion c) 
    | Cast (t, c) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_coercion c) (pp_term t) 
    | Return t -> print ppf "Value %t" (pp_term t)
    | Handler {effect_clauses = eff_cls; value_clause = val_cl} ->
        print ppf "handler {@[<hov>value_clause = %t;@] @[<hov>effect_claueses = %t;@] }" 
        (pp_abs_with_ty val_cl) (pp_effect_cls eff_cls)
    | LetVal (t1, (pat, ty, t2)) -> print ppf "@[<hv>@[<hv>let %t = %t in@] @,%t@]" (pp_pattern pat) (pp_term t1) (pp_term t2)
    | LetRec (defs, t2) -> print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (pp_let_rec defs) (pp_term t2)
    | Match (t, cases) -> print ppf "@[<hv>(match %t with@, | %t)@]" (pp_term t)
        (pp_sequence "@, | " pp_abs cases)
    | Call (e, t, abs_ty) -> print ppf "@[<hov 2> call (%t) @,(%t) @,(%t)@]" (pp_effect e) (pp_term t) (pp_abs_with_ty abs_ty)
    | Op (e, t) -> print ppf "@[<hov 2> call (%t) @,(%t) @,(%s)@]" (pp_effect e) (pp_term t) "(fun x -> x)"
    | Bind (t, abs) -> print ppf "@[<hov 2>((%t) >> (%t))@]" (pp_term t) (pp_abs abs)
    | Handle (NoEffSyntax.Call (e, t1, (pat, ty, t)), Cast (t2, FunToHand (c1, c2))) -> print ppf "%t"
        (pp_term (NoEffSyntax.Call (e, t1, (pat, ty, Handle (t, Cast (t2, FunToHand (c1, c2)))))))
    | Handle (Return t1, Cast (t2, FunToHand (c1, c2))) -> print ppf "%t" (pp_term (Cast (Apply (t2, Cast (t1, c1)), c2)))
    | Handle (t1, t2) -> (
        match t2 with 
          | Cast (t, CoerHandler (c1, c2)) -> print ppf "%t" (pp_term (Cast (Handle (Cast (t1, c1), t) , c2)))
          | _ -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t1) (pp_term t2))

and pp_abs (p, t) ppf = print ppf "@[<h>(%t ->@ %t)@]" (pp_pattern p) (pp_term t)

and pp_abs_with_ty (p, ty, t) ppf = print ppf "@[<h>((%t : %t) ->@ %t)@]"  (pp_pattern p) (pp_type ty) (pp_term t)

and pp_let_rec lst ppf = 
  let pp_var_ty_term (v, ty, t) ppf = print ppf "@[<hv 2>and (%t : %t) = @,%t@]" (pp_variable v) (pp_type ty) (pp_term t) in
  match lst with
    | [] -> ()
    | (v, ty, t) :: tl -> print ppf "@[<hv 2>let rec (%t : %t) = @,%t@] @,%t" 
        (pp_variable v) (pp_type ty) (pp_term t) (pp_sequence " " pp_var_ty_term tl)

and pp_effect_cls eff_cls ppf = 
  let pp_effect_abs2 (eff, (pat1, pat2, t)) ppf = print ppf "@[<hv 2>| %t -> fun %t %t -> %t @]"
    (pp_effect eff) (pp_pattern pat1) (pp_pattern pat2) (pp_term t) in
  print ppf 
  "@[<h>(fun (type a) (type b) (eff : (a, b) effect) -> 
  (match eff with
    %t  
  ) @)@]" 
  (pp_sequence " " pp_effect_abs2 (Assoc.to_list eff_cls))

let pp_def_effect (eff, (ty1, ty2)) ppf = 
  print ppf "@[effect %t : %t ->@ %t@]@." (CoreTypes.Effect.print eff) (pp_type ty1) (pp_type ty2)

let pp_lets lst ppf = 
   let pp_one_let (p, ty, t) ppf = print ppf "@[<hv 2>and (%t : %t) = @,%t@]" (pp_pattern p) (pp_type ty) (pp_term t) in
  match lst with
    | [] -> ()
    | (p, ty, t) :: tl -> print ppf "@[<hv 2>let rec (%t : %t) = @,%t@] @,%t" 
        (pp_pattern p) (pp_type ty) (pp_term t) (pp_sequence " " pp_one_let tl)

let pp_external name symbol_name translation ppf =
  match translation with
  | NoEffExternal.Unknown ->
      print ppf "let %t = failwith \"Unknown external symbol %s.\"@."
        (pp_variable name)
        symbol_name
  | NoEffExternal.Exists t ->
      print ppf "let %t = %s@." (pp_variable name) t

let pp_tydef (name, (params, tydef)) ppf =
  let pp_def tydef ppf =
    match tydef with
    | TyDefRecord assoc -> print ppf "%t" (pp_record pp_type ":" assoc)
    | TyDefSum assoc ->
        let lst = Assoc.to_list assoc in
        let print_cons ty_opt ppf =
          match ty_opt with
          | lbl, None -> print ppf "%t" (MulticoreSymbol.print_label lbl)
          | lbl, Some ty ->
              print ppf "%t of %t"
                (MulticoreSymbol.print_label lbl)
                (pp_type ty)
        in
        print ppf "@[<hov>%t@]" (pp_sequence "@, | " print_cons lst)
    | TyDefInline ty -> print ppf "%t" (pp_type ty)
  in
  match params with
  | [] ->
      print ppf "@[type %t = %t@]@."
        (MulticoreSymbol.print_tyname name)
        (pp_def tydef)
  | lst ->
      print ppf "@[type (%t) %t = %t@]@."
        (pp_sequence ", " MulticoreSymbol.print_typaram params)
        (MulticoreSymbol.print_tyname name)
        (pp_def tydef)

let pp_cmd cmd ppf = 
  match cmd with
    | Term t -> print ppf "%t@." (pp_term t)  (* TODO check if ok *)
    | DefEffect (e, (ty1, ty2)) -> pp_def_effect (e, (ty1, ty2)) ppf
    | TopLet defs -> print ppf "@[<hv>%t@]@." (pp_lets defs)
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
    | TyDef defs -> print ppf "%t@." (pp_sequence "@, and " pp_tydef defs)
