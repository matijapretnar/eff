open NoEffSyntax

let print = Format.fprintf

let rec pp_sequence sep pp xs ppf =
  match xs with
    | [] -> ()
    | [x] -> pp x ppf
    | x :: xs -> print ppf ("%t" ^^ sep ^^ "%t") (pp x) (pp_sequence sep pp xs)

let pp_label label ppf = failwith __LOC__

let pp_tyname ty_name ppf = failwith __LOC__

let pp_typaram ty_param ppf = print ppf "'ty%t" (CoreTypes.TyParam.print ~safe:true ty_param)

let pp_variable var ppf = failwith __LOC__

let rec pp_type noEff_ty ppf = 
  match noEff_ty with
    | TyVar p -> print ppf "%t" (pp_typaram p)
    | TyApply (tyName, []) -> print ppf "%t" (pp_tyname tyName)
    | TyApply (tyName, tys) -> print ppf "(%t) %t" (Print.sequence ", " pp_type tys) (pp_tyname tyName)
    | TyTuple [] -> print ppf "unit"
    | TyTuple tys -> print ppf "@[<hov>(%t)@]" (Print.sequence " * " pp_type tys)
    | TyBasic t -> print ppf "%t" (Const.print_ty t)
    | TyArrow (ty1, ty2) -> print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
    | TyHandler (ty1, ty2) -> failwith __LOC__
    | TyForAll (t, ty) -> failwith __LOC__
    | TyQualification (tyc, ty) -> failwith __LOC__
    | TyComputation ty -> failwith __LOC__

let pp_field pp sep (field, value) ppf =
  print ppf "%t %s %t" (CoreTypes.Field.print field) sep (pp value)

let pp_tuple pp tpl ppf = 
  match tpl with
    | [] -> print ppf "()"
    | xs -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp xs)

let pp_record pp sep assoc ppf =
  let lst = Assoc.to_list assoc in
  print ppf "{@[<hov>%t@]}" (pp_sequence "; " (pp_field pp sep) lst)

let pp_abs_with_ty awty ppf = failwith __LOC__ "(%t : %t)-> %t"

let pp_effect (t, (ty1, ty2)) ppf = CoreTypes.Effect.print t

let pp_case case ppf = failwith __LOC__

let pp_coercion coer ppf =
  match coer with
     | ReflTy _ -> print ppf "ReflTyIzHeaderja"


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
    | Lambda awty -> print ppf "@[<hv 2>fun %t@]" (pp_abs_with_ty awty)
    | Effect (et, _) -> (* print ppf "%s" (CoreTypes.Effect.print et ppf) *) failwith __LOC__
    | Apply (t1, t2) -> print ppf "@[<hov 2>(%t) @,(%t)@]" (pp_term t1) (pp_term t2)
    | BigLambdaTy (_, t) -> failwith __LOC__
    | ApplyTy (t, _) -> failwith __LOC__
    | BigLambdaCoerVar (tycp, tyc, t) -> failwith __LOC__
    | ApplyTyCoercion (t, c) -> failwith __LOC__
    | Cast (t, c) -> print ppf "@[<hov 2>(%t) :> (%t)@]" (pp_term t) (pp_coercion c)
    | Return t -> failwith __LOC__
    | Handler h -> failwith __LOC__
    | LetVal (t1, abs_ty) -> print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (pp_let t1) (pp_abs_with_ty abs_ty)
    | LetRec (vs_tys_ts, t2) -> print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (pp_let_rec vs_tys_ts) (pp_term t2)
    | Match (t, cases) -> print ppf "@[<hv>(match %t with@, | %t)@]" (pp_term t)
        (pp_sequence "@, | " pp_case cases)
    | Call (e, t, awty) -> failwith __LOC__
    | Op (e, t) -> failwith __LOC__
    | Bind (t, abs) -> failwith __LOC__
    | Handle (t1, t2) -> failwith __LOC__

and pp_let_rec lst ppf = failwith __LOC__

and pp_let t ppf = failwith __LOC__

let pp_cmd cmd ppf = failwith __LOC__
