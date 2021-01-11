open Utils
open Language

type variable = CoreTypes.Variable.t
(** Syntax of the core language. *)

type effect = CoreTypes.Effect.t

type label = CoreTypes.Label.t

type field = CoreTypes.Field.t

(** Types used by MulticoreOcaml. *)
type ty =
  | TyApply of CoreTypes.TyName.t * ty list
  | TyParam of CoreTypes.TyParam.t
  | TyBasic of Const.ty
  | TyTuple of ty list
  | TyArrow of ty * ty

type tydef =
  | TyDefRecord of (CoreTypes.Field.t, ty) Assoc.t
  | TyDefSum of (CoreTypes.Label.t, ty option) Assoc.t
  | TyDefInline of ty

(** Patterns *)
type pattern =
  | PVar of variable
  | PAnnotated of pattern * ty
  | PAs of pattern * variable
  | PTuple of pattern list
  | PRecord of (field, pattern) Assoc.t
  | PVariant of label * pattern option
  | PConst of Const.t
  | PNonbinding

(** Pure expressions *)
type term =
  | Var of variable
  | Const of Const.t
  | Annotated of term * ty
  | Tuple of term list
  | Record of (field, term) Assoc.t
  | Variant of label * term option
  | Lambda of abstraction
  | Function of match_case list
  | Effect of effect
  | Let of (pattern * term) list * term
  | LetRec of (variable * abstraction) list * term
  | Match of term * match_case list
  | Apply of term * term
  | Check of term

and match_case =
  | ValueClause of abstraction
  | EffectClause of effect * abstraction2

and abstraction = pattern * term
(** Abstractions that take one argument. *)

and abstraction2 = pattern * pattern * term
(** Abstractions that take two arguments. *)

type cmd =
  | Term of term
  | DefEffect of effect * (ty * ty)
  | TopLet of (pattern * term) list
  | TopLetRec of (variable * abstraction) list
  | External of (variable * Type.ty * string)
  | TyDef of (label * (CoreTypes.TyParam.t list * tydef)) list

let print = Format.fprintf

(* ------------------------------------------------------------------------ *)
(* Auxiliary printing functions *)

let print_sequence (type a) =
  (* This trick is needed to make it strongly polymorphic.
      Thanks Jane Street Tech Blog. *)
  let rec sequence sep (pp : a -> Format.formatter -> unit) vs ppf =
    match vs with
    | [] -> ()
    | [ v ] -> pp v ppf
    | v :: vs -> print ppf ("%t" ^^ sep ^^ "%t") (pp v) (sequence sep pp vs)
  in
  sequence

let print_field pp sep (f, v) ppf =
  print ppf "%t %s %t" (MulticoreSymbol.print_field f) sep (pp v)

let print_tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (print_sequence ", " pp lst)

let print_record pp sep assoc ppf =
  let lst = Assoc.to_list assoc in
  print ppf "{@[<hov>%t@]}" (print_sequence "; " (print_field pp sep) lst)

let rec print_term t ppf =
  match t with
  | Var x -> print ppf "%t" (MulticoreSymbol.print_variable x)
  | Const c -> print ppf "%t" (Const.print c)
  | Annotated (t, ty) -> print ppf "(%t : %t)" (print_term t) (print_type ty)
  | Tuple lst -> print ppf "%t" (print_tuple print_term lst)
  | Record assoc -> print ppf "%t" (print_record print_term "=" assoc)
  | Variant (lbl, None) when lbl = CoreTypes.nil -> print ppf "[]"
  | Variant (lbl, None) -> print ppf "%t" (MulticoreSymbol.print_label lbl)
  | Variant (lbl, Some (Tuple [ hd; tl ])) when lbl = CoreTypes.cons ->
      print ppf "@[<hov>(%t::%t)@]" (print_term hd) (print_term tl)
  | Variant (lbl, Some t) ->
      print ppf "(%t @[<hov>%t@])"
        (MulticoreSymbol.print_label lbl)
        (print_term t)
  | Lambda a -> print ppf "@[<hv 2>fun %t@]" (print_abstraction a)
  | Function lst ->
      print ppf "@[<hv>(function @, | %t)@]"
        (print_sequence "@, | " print_case lst)
  | Effect eff -> print ppf "%t" (MulticoreSymbol.print_effect eff)
  | Let (lst, t) ->
      print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (print_let lst) (print_term t)
  | LetRec (lst, t) ->
      print ppf "@[<hv>@[<hv>%tin@] @,%t@]" (print_let_rec lst) (print_term t)
  | Match (t, []) ->
      (* Absurd case *)
      print ppf
        ("@[<hv>(match %t with | _ ->"
       ^^ " failwith \"void successfully matched\")@]")
        (print_term t)
  | Match (t, lst) ->
      print ppf "@[<hv>(match %t with@, | %t)@]" (print_term t)
        (print_sequence "@, | " print_case lst)
  | Apply (Effect eff, (Lambda _ as t2)) ->
      print ppf "perform (%t (%t))"
        (MulticoreSymbol.print_effect eff)
        (print_term t2)
  | Apply (Effect eff, t2) ->
      print ppf "perform (%t %t)"
        (MulticoreSymbol.print_effect eff)
        (print_term t2)
  | Apply (t1, t2) ->
      print ppf "@[<hov 2>(%t) @,(%t)@]" (print_term t1) (print_term t2)
  | Check _t ->
      Print.warning
        "[#check] commands are ignored when compiling to Multicore OCaml."

and print_pattern p ppf =
  match p with
  | PVar x -> print ppf "%t" (MulticoreSymbol.print_variable x)
  | PAs (p, x) ->
      print ppf "%t as %t" (print_pattern p) (MulticoreSymbol.print_variable x)
  | PAnnotated (p, ty) ->
      print ppf "(%t : %t)" (print_pattern p) (print_type ty)
  | PConst c -> print ppf "%t" (Const.print c)
  | PTuple lst -> print ppf "%t" (print_tuple print_pattern lst)
  | PRecord assoc -> print ppf "%t" (print_record print_pattern "=" assoc)
  | PVariant (lbl, None) when lbl = CoreTypes.nil -> print ppf "[]"
  | PVariant (lbl, None) -> print ppf "%t" (MulticoreSymbol.print_label lbl)
  | PVariant (lbl, Some (PTuple [ hd; tl ])) when lbl = CoreTypes.cons ->
      print ppf "@[<hov>(%t::%t)@]" (print_pattern hd) (print_pattern tl)
  | PVariant (lbl, Some p) ->
      print ppf "(%t @[<hov>%t@])"
        (MulticoreSymbol.print_label lbl)
        (print_pattern p)
  | PNonbinding -> print ppf "_"

and print_type ty ppf =
  match ty with
  | TyArrow (t1, t2) ->
      print ppf "@[<h>(%t ->@ %t)@]" (print_type t1) (print_type t2)
  | TyBasic b -> print ppf "%t" (Const.print_ty b)
  | TyApply (t, []) -> print ppf "%t" (MulticoreSymbol.print_tyname t)
  | TyApply (t, ts) ->
      print ppf "(%t) %t"
        (Print.sequence ", " print_type ts)
        (MulticoreSymbol.print_tyname t)
  | TyParam p -> print ppf "%t" (MulticoreSymbol.print_typaram p)
  | TyTuple [] -> print ppf "unit"
  | TyTuple ts -> print ppf "@[<hov>(%t)@]" (Print.sequence " * " print_type ts)

and print_tydef (name, (params, tydef)) ppf =
  let print_def tydef ppf =
    match tydef with
    | TyDefRecord assoc -> print ppf "%t" (print_record print_type ":" assoc)
    | TyDefSum assoc ->
        let lst = Assoc.to_list assoc in
        let print_cons ty_opt ppf =
          match ty_opt with
          | lbl, None -> print ppf "%t" (MulticoreSymbol.print_label lbl)
          | lbl, Some ty ->
              print ppf "%t of %t"
                (MulticoreSymbol.print_label lbl)
                (print_type ty)
        in
        print ppf "@[<hov>%t@]" (print_sequence "@, | " print_cons lst)
    | TyDefInline ty -> print ppf "%t" (print_type ty)
  in
  match params with
  | [] ->
      print ppf "@[type %t = %t@]@."
        (MulticoreSymbol.print_tyname name)
        (print_def tydef)
  | _lst ->
      print ppf "@[type (%t) %t = %t@]@."
        (print_sequence ", " MulticoreSymbol.print_typaram params)
        (MulticoreSymbol.print_tyname name)
        (print_def tydef)

and print_def_effect (eff, (ty1, ty2)) ppf =
  print ppf "@[effect %t : %t ->@ %t@]@."
    (MulticoreSymbol.print_effect eff)
    (print_type ty1) (print_type ty2)

and print_top_let defs ppf = print ppf "@[<hv>%t@]@." (print_let defs)

and print_top_let_rec defs ppf = print ppf "@[<hv>%t@]@." (print_let_rec defs)

and print_external name symbol_name translation ppf =
  match translation with
  | MulticoreExternal.Unknown ->
      print ppf "let %t = failwith \"Unknown external symbol %s.\"@."
        (MulticoreSymbol.print_variable name)
        symbol_name
  | MulticoreExternal.Exists t ->
      print ppf "let %t = %s@." (MulticoreSymbol.print_variable name) t

and print_tydefs tydefs ppf =
  print ppf "%t@." (print_sequence "@, and " print_tydef tydefs)

and print_abstraction (p, t) ppf =
  print ppf "%t ->@ %t" (print_pattern p) (print_term t)

and print_let lst ppf =
  let rec sequence lst ppf =
    match lst with
    | [] -> ()
    | abs :: tl ->
        let p_lst, t = abs_to_multiarg_abs abs in
        print ppf "@[<hv 2>and %t = @,%t@] @,%t"
          (print_sequence " " print_pattern p_lst)
          (print_term t) (sequence tl)
  in
  (* First one *)
  match lst with
  | [] -> ()
  | abs :: tl ->
      let p_lst, t = abs_to_multiarg_abs abs in
      print ppf "@[<hv 2>let %t = @,%t@] @,%t"
        (print_sequence " " print_pattern p_lst)
        (print_term t) (sequence tl)

and print_let_rec lst ppf =
  let rec sequence lst ppf =
    match lst with
    | [] -> ()
    | (name, abs) :: tl ->
        let p_lst, t = abs_to_multiarg_abs abs in
        print ppf "@[<hv 2>and %t %t = @,%t@] @,%t"
          (MulticoreSymbol.print_variable name)
          (print_sequence " " print_pattern p_lst)
          (print_term t) (sequence tl)
  in
  (* First one *)
  match lst with
  | [] -> ()
  | (name, abs) :: tl ->
      let p_lst, t = abs_to_multiarg_abs abs in
      print ppf "@[<hv 2>let rec %t %t = @,%t@] @,%t"
        (MulticoreSymbol.print_variable name)
        (print_sequence " " print_pattern p_lst)
        (print_term t) (sequence tl)

and abs_to_multiarg_abs (p, t) =
  match t with
  | Lambda abs ->
      let p_list, t' = abs_to_multiarg_abs abs in
      (p :: p_list, t')
  | _ -> ([ p ], t)

and print_case case ppf =
  match case with
  | ValueClause abs -> print ppf "@[<hv 2>%t@]" (print_abstraction abs)
  | EffectClause (eff, (p1, p2, t)) ->
      if p2 = PNonbinding then
        print ppf "@[<hv 2>effect (%t %t) %t -> @,%t@]"
          (MulticoreSymbol.print_effect eff)
          (print_pattern p1) (print_pattern p2) (print_term t)
      else
        print ppf
          ("@[<hv 2>effect (%t %t) %t ->@,"
         ^^ "(let %t x = continue (Obj.clone_continuation %t) x in @,%t)@]")
          (MulticoreSymbol.print_effect eff)
          (print_pattern p1) (print_pattern p2) (print_pattern p2)
          (print_pattern p2) (print_term t)

let print_cmd cmd ppf =
  match cmd with
  | Term t ->
      print ppf "let _ = @.@[<hv>(_ocaml_tophandler) (fun _ -> @,%t@,)@];;@."
        (print_term t)
  | DefEffect (eff, (ty1, ty2)) -> print_def_effect (eff, (ty1, ty2)) ppf
  | TopLet defs -> print_top_let defs ppf
  | TopLetRec defs -> print_top_let_rec defs ppf
  | TyDef tydefs -> print_tydefs tydefs ppf
  | External (x, _ty, f) -> (
      match Assoc.lookup f MulticoreExternal.values with
      | None -> Error.runtime "Unknown external symbol %s." f
      | Some (MulticoreExternal.Unknown as unknown) ->
          Print.warning
            ("External symbol %s cannot be compiled. It has been replaced "
           ^^ "with [failwith \"Unknown external symbol %s.\"].")
            f f;
          print_external x f unknown ppf
      | Some (MulticoreExternal.Exists _s as known) ->
          print_external x f known ppf)
