open Utils
open SyntaxNoEff
module OurPrimitives = Primitives
open Language

type optimization_config = { purity_aware_translation : bool }

type state = {
  inlinable_primitives :
    (Language.Term.Variable.t, Language.Primitives.primitive_value) Assoc.t;
  optimization_config : optimization_config;
}

let initial_state optimization_config =
  { inlinable_primitives = Assoc.empty; optimization_config }

let add_primitive_values state primitive_values =
  {
    state with
    inlinable_primitives =
      Assoc.concat primitive_values state.inlinable_primitives;
  }

let print = Format.fprintf

let rec pp_sequence sep pp xs ppf =
  match xs with
  | [] -> ()
  | [ x ] -> pp x ppf
  | x :: xs -> print ppf ("%t" ^^ sep ^^ "%t") (pp x) (pp_sequence sep pp xs)

let pp_tuple pp lst ppf =
  match lst with
  | [] -> print ppf "()"
  | lst -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp lst)

let pp_label label ppf = Type.Label.print label ppf
let pp_tyname ty_name ppf = Language.TyName.print ty_name ppf

let pp_typaram ty_param ppf =
  print ppf "'ty%d" (Type.TyParam.fold (fun _ n -> n) ty_param)

let protected =
  [ "and"; "as"; "assert"; "asr"; "begin"; "class"; "constraint"; "do"; "done" ]
  @ [ "downto"; "else"; "end"; "exception"; "external"; "false"; "for"; "fun" ]
  @ [ "function"; "functor"; "if"; "in"; "include"; "inherit"; "initializer" ]
  @ [ "land"; "lazy"; "let"; "lor"; "lsl"; "lsr"; "lxor"; "match"; "method" ]
  @ [
      "mod"; "module"; "mutable"; "new"; "nonrec"; "object"; "of"; "open"; "or";
    ]
  @ [ "private"; "rec"; "sig"; "struct"; "then"; "to"; "true"; "try"; "type" ]
  @ [ "val"; "virtual"; "when"; "while"; "with"; "continue" ]
  @ [ "&&"; "||"; "not" ]

let pp_variable ?(safe = true) state var ppf =
  match Assoc.lookup var state.inlinable_primitives with
  | Some s -> Format.fprintf ppf "%s" (OurPrimitives.primitive_source s)
  | None ->
      let printer desc n =
        (* [mod] has privileges because otherwise it's stupid *)
        if desc = "mod" then Format.fprintf ppf "_op_%d (* %s *)" n desc
        else (
          if List.mem desc protected then
            Print.warning
              "Warning: Protected keyword [%s]. Must be fixed by hand!@." desc;
          match desc.[0] with
          | 'a' .. 'z' | '_' ->
              if safe then Format.fprintf ppf "_%s_%d" desc n
              else Format.fprintf ppf "%s" desc
          | '$' -> (
              match desc with
              | "$c_thunk" -> Format.fprintf ppf "_comp_%d" n
              | "$id_par" -> Format.fprintf ppf "_id_%d" n
              | "$anon" -> Format.fprintf ppf "_anon_%d" n
              | "$bind" -> Format.fprintf ppf "_b_%d" n
              | _ -> Format.fprintf ppf "_x_%d" n)
          | _ -> Format.fprintf ppf "_op_%d (* %s *)" n desc)
      in
      Language.Term.Variable.fold printer var

let pp_field pp sep (field, value) ppf =
  print ppf "%t %s %t" (Type.Field.print field) sep (pp value)

let pp_record pp sep flds ppf =
  let lst = Type.Field.Map.bindings flds in
  print ppf "{@[<hov>%t@]}" (pp_sequence "; " (pp_field pp sep) lst)

let rec pp_type noeff_ty ppf =
  match noeff_ty with
  | NTyParam p -> print ppf "%t" (pp_typaram p)
  | NTyApply (tyName, []) -> print ppf "%t" (pp_tyname tyName)
  | NTyApply (tyName, tys) ->
      print ppf "(%t) %t" (Print.sequence ", " pp_type tys) (pp_tyname tyName)
  | NTyTuple [] -> print ppf "unit"
  | NTyTuple tys -> print ppf "@[<hov>(%t)@]" (Print.sequence " * " pp_type tys)
  | NTyBasic t -> print ppf "%t" (Const.print_ty t)
  | NTyArrow (ty1, ty2) ->
      print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
  | NTyHandler (ty1, ty2) ->
      print ppf "@[<h>(%t ->@ %t)@]" (pp_type ty1) (pp_type ty2)
  | NTyComp ty -> print ppf "%t computation" (pp_type ty)

let rec pp_pattern ?(safe = true) state pat ppf =
  match pat with
  | PNVar v -> print ppf "%t" (pp_variable ~safe state v)
  | PNAs (p, v) ->
      print ppf "%t as %t" (pp_pattern ~safe state p) (pp_variable state v)
  | PNTuple pats -> print ppf "%t" (pp_tuple (pp_pattern ~safe state) pats)
  | PNRecord rcd -> print ppf "%t" (pp_record (pp_pattern ~safe state) "=" rcd)
  | PNVariant (lbl, None) when lbl = Type.nil -> print ppf "[]"
  | PNVariant (lbl, None) -> print ppf "%t" (Type.Label.print lbl)
  | PNVariant (lbl, Some (PNTuple [ v1; v2 ])) when lbl = Type.cons ->
      print ppf "(%t :: %t)"
        (pp_pattern ~safe state v1)
        (pp_pattern ~safe state v2)
  | PNVariant (lbl, Some p) ->
      print ppf "(%t @[<hov>%t@])" (Type.Label.print lbl)
        (pp_pattern ~safe state p)
  | PNConst c -> print ppf "%t" (Const.print c)
  | PNNonbinding -> print ppf "_"

let pp_tuple pp tpl ppf =
  match tpl with
  | [] -> print ppf "()"
  | xs -> print ppf "(@[<hov>%t@])" (pp_sequence ", " pp xs)

let pp_effect (e, (_ty1, _ty2)) ppf = Effect.print e ppf

let rec pp_coercion ?max_level coer ppf =
  (* The cases not matched here should be handled in pp_term *)
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match coer with
  | NCoerVar v -> print "%t" (Type.TyCoercionParam.print ~safe:true v)
  | NCoerRefl -> print "coer_refl_ty"
  | NCoerArrow (w1, w2) ->
      print ~at_level:1 "coer_arrow %t %t"
        (pp_coercion ~max_level:0 w1)
        (pp_coercion ~max_level:0 w2)
  | NCoerHandler (w1, w2) ->
      print ~at_level:1 "coer_handler %t %t"
        (pp_coercion ~max_level:0 w1)
        (pp_coercion ~max_level:0 w2)
  | NCoerHandToFun (w1, w2) ->
      print ~at_level:1 "coer_hand_to_fun %t %t"
        (pp_coercion ~max_level:0 w1)
        (pp_coercion ~max_level:0 w2)
  | NCoerFunToHand (w1, w2) ->
      print ~at_level:1 "coer_fun_to_hand %t %t"
        (pp_coercion ~max_level:0 w1)
        (pp_coercion ~max_level:0 w2)
  | NCoerComp w ->
      print ~at_level:1 "coer_computation %t" (pp_coercion ~max_level:0 w)
  | NCoerReturn w ->
      print ~at_level:1 "coer_return %t" (pp_coercion ~max_level:0 w)
  | NCoerUnsafe NCoerRefl -> print "force_unsafe"
  | NCoerUnsafe w ->
      print ~at_level:1 "coer_unsafe %t" (pp_coercion ~max_level:0 w)
  | NCoerTuple cs ->
      print ~at_level:1 "coer_tuple_%d %t" (List.length cs)
        (pp_tuple pp_coercion cs)
  | NCoerApply (t, cs) ->
      print ~at_level:1 "coer_%t %t" (Language.TyName.print t)
        (Print.sequence " " (pp_coercion ~max_level:0) cs)

let pp_lets keyword pp_let_def lst ppf =
  let pp_and_let let_def ppf =
    print ppf "@[<hv 2>and %t@]" (pp_let_def let_def)
  in
  match lst with
  | [] -> ()
  | let_def :: tl ->
      print ppf "@[<hv 2>%s %t@] @,%t" keyword (pp_let_def let_def)
        (pp_sequence " " pp_and_let tl)

let pp_coercion_vars ws =
  Print.sequence " " (Type.TyCoercionParam.print ~safe:true) ws

let rec pp_term ?max_level ?(top_level = false) state noEff_term ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match noEff_term with
  | NVar v when v.coercions = [] -> print "%t" (pp_variable state v.variable)
  | NVar v ->
      print ~at_level:1 "%t %t"
        (pp_variable state v.variable)
        (Print.sequence " " (pp_coercion ~max_level:0) v.coercions)
  | NConst c -> print "%t" (Const.print c)
  | NTuple ts -> print "%t" (pp_tuple (pp_term state ~max_level:1) ts)
  | NRecord rcd -> print "%t" (pp_record (pp_term state) "=" rcd)
  (* Note that t is not necessarily a pair, it can be coerced *)
  | NVariant (l, Some t) when l = Type.cons -> (
      match t with
      | NTuple [ x; xs ] ->
          print ~at_level:1 "@[<hov>(%t :: %t)@]"
            (pp_term state ~max_level:0 x)
            (pp_term state ~max_level:0 xs)
      | _ ->
          print ~at_level:1 "@[<hov>(fun (x, xs) -> (x :: xs)) (%t)@]"
            (pp_term state ~max_level:0 t))
  | NVariant (l, None) when l = Type.nil -> print "[]"
  | NVariant (l, None) -> print "%t" (pp_label l)
  | NVariant (l, Some t1) ->
      print ~at_level:1 "%t @[<hov>%t@]" (pp_label l)
        (pp_term state ~max_level:0 t1)
  | NFun abs_ty ->
      print ~at_level:2 "@[<hv 2>fun %t@]" (pp_abs_with_ty state abs_ty)
  | NApplyTerm (t1, t2) ->
      print ~at_level:1 "@[<hov 2>%t @,%t@]"
        (pp_term state ~max_level:1 t1)
        (pp_term state ~max_level:0 t2)
  (*| NCast (t, (NCoerReturn (NCoerRefl _) as _c)) ->
      print ~at_level:2 "Value (%t)" (pp_term t) *)
  | NCast (t, c) ->
      print ~at_level:1 "@[<hov 2>%t @,%t@]"
        (pp_coercion ~max_level:1 c)
        (pp_term state ~max_level:0 t)
  | NReturn t -> print ~at_level:1 "Value %t" (pp_term state ~max_level:0 t)
  | NHandler { effect_clauses; return_clause; finally_clause } ->
      (* Top level handlers need to be printed in a fully applied form,
         otherwise value restriction kicks in when compiling the
         resulting files with OCaml*)
      if top_level then
        let v = Variable.fresh "cmd" in
        print ~at_level:2
          "(fun %t -> handler {@[<hov>value_clause = (fun %t);@] \
           @[<hov>effect_clauses = %t;@]} (@[<hov>(fun %t)@]) %t)"
          (pp_variable state v)
          (pp_abs_with_ty state return_clause)
          (pp_effect_cls state effect_clauses)
          (pp_abs_with_ty state finally_clause)
          (pp_term state (SyntaxNoEff.NVar { variable = v; coercions = [] }))
      else
        print ~at_level:2
          "handler {@[<hov>value_clause = (fun %t);@] @[<hov>effect_clauses = \
           %t;@]} (@[<hov>(fun %t)@])"
          (pp_abs_with_ty state return_clause)
          (pp_effect_cls state effect_clauses)
          (pp_abs_with_ty state finally_clause)
  | NLet (t1, (pat, t2)) ->
      print ~at_level:2 "@[<hv>@[<hv>let %t = %t in@] @,%t@]"
        (pp_pattern state pat) (pp_term state t1) (pp_term state t2)
  | NLetRec (defs, t2) ->
      print ~at_level:2 "@[<hv>@[<hv>%tin@] @,%t@]" (pp_let_rec state defs)
        (pp_term state t2)
  | NMatch (t, []) ->
      print ~at_level:2 "@[<hv>match %t with@, _ -> assert false@]"
        (pp_term state t)
  | NMatch
      ( t1,
        [
          (PNConst (Boolean true), NConst (Boolean true));
          (PNConst (Boolean false), t2);
        ] ) ->
      print ~at_level:2 "%t || %t"
        (pp_term state ~max_level:0 t1)
        (pp_term state ~max_level:0 t2)
  | NMatch
      ( t1,
        [
          (PNConst (Boolean true), t2);
          (PNConst (Boolean false), NConst (Boolean false));
        ] ) ->
      print ~at_level:2 "%t && %t"
        (pp_term state ~max_level:0 t1)
        (pp_term state ~max_level:0 t2)
  | NMatch
      ( t,
        [
          (PNConst (Const.Boolean true), t1); (PNConst (Const.Boolean false), t2);
        ] ) ->
      print ~at_level:2 "@[<hv>if %t then %t else %t @]" (pp_term state t)
        (pp_term state t1) (pp_term state t2)
  | NMatch (t, cases) ->
      print ~at_level:2 "@[<hv>begin match %t with @, %t end @]"
        (pp_term state t)
        (pp_sequence "@, | " (pp_abs state) cases)
  | NCall (e, t, abs_ty) ->
      print ~at_level:2 "@[<hov 2> Call (%t, (%t), (fun %t))@]" (pp_effect e)
        (pp_term state t)
        (pp_abs_with_ty state abs_ty)
  | NBind (t, abs) ->
      print ~at_level:2 "@[<hov 2>%t >>= (fun %t)@]"
        (pp_term state ~max_level:1 t)
        (pp_abs state abs)
  | NHandle (t1, t2) ->
      print ~at_level:1 "@[<hov 2>%t @,%t@]"
        (pp_term state ~max_level:1 t2)
        (pp_term state ~max_level:0 t1)
  | NDirectPrimitive p ->
      print ~at_level:1 "(%s)" (OurPrimitives.primitive_source p)

and pp_abs state (p, t) ppf =
  print ppf "@[<h> %t ->@ %t@]" (pp_pattern state p) (pp_term state t)

and pp_abs_with_ty state (p, ty, t) ppf =
  print ppf "@[<h>(%t: %t) ->@ %t@]" (pp_pattern state p) (pp_type ty)
    (pp_term state t)

and pp_let_rec state lst ppf =
  let pp_let_rec_def (x, (p, t)) ppf =
    print ppf "%t %t = @,%t" (pp_variable state x) (pp_pattern state p)
      (pp_term state t)
  in
  pp_lets "let rec" pp_let_rec_def (Assoc.to_list lst) ppf

and pp_top_let_rec state lst ppf =
  let pp_top_let_rec_def (x, (ws, (p, t))) ppf =
    print ppf "%t %t %t = @,%t" (pp_variable state x) (pp_coercion_vars ws)
      (pp_pattern state p) (pp_term state t)
  in
  pp_lets "let rec" pp_top_let_rec_def lst ppf

and pp_effect_cls state eff_cls ppf =
  let pp_effect_abs2 (((_, (ty1, _)) as eff), (pat1, pat2, t)) ppf =
    print ppf "@[<hv 2>| %t -> fun (%t : %t) %t -> %t @]" (pp_effect eff)
      (pp_pattern state pat1) (pp_type ty1) (pp_pattern state pat2)
      (pp_term state t)
  in
  print ppf
    "@[<h>(fun (type a) (type b) (eff : (a, b) eff_internal_effect) : (a -> (b \
     -> _) -> _) -> \n\
    \  (match eff with\n\
    \    %t  \n\
    \    | eff' -> (fun arg k -> Call (eff', arg, k))\n\
    \      ))@]"
    (pp_sequence " " pp_effect_abs2 (Assoc.to_list eff_cls))

let pp_def_effect (eff, (ty1, ty2)) ppf =
  print ppf
    "@[type(_, _) eff_internal_effect += %t : (%t, %t) eff_internal_effect \
     @]@.;;"
    (Effect.print eff) (pp_type ty1) (pp_type ty2)

let pp_let_def ?(top_level = false) state (p, ws, t) ppf =
  print ppf "%t %t = @,%t" (pp_pattern state p) (pp_coercion_vars ws)
    (pp_term ~top_level state t)

let pp_external state name symbol_name ppf =
  print ppf "let %t = ( %s )@.;;" (pp_variable state name) symbol_name

let pp_tydef (name, (params, tydef)) ppf =
  let pp_def tydef ppf =
    match tydef with
    | TyDefRecord assoc -> print ppf "%t" (pp_record pp_type ":" assoc)
    | TyDefSum assoc ->
        let lst = Type.Field.Map.bindings assoc in
        let print_cons ty_opt ppf =
          match ty_opt with
          | lbl, None -> print ppf "%t" (Type.Label.print lbl)
          | lbl, Some ty ->
              print ppf "%t of %t" (Type.Label.print lbl) (pp_type ty)
        in
        print ppf "@[<hov>%t@]" (pp_sequence "@, | " print_cons lst)
    | TyDefInline ty -> print ppf "%t" (pp_type ty)
  in
  match params with
  | [] -> print ppf "@[%t = %t@]@." (Language.TyName.print name) (pp_def tydef)
  | _lst ->
      print ppf "@[(%t) %t = %t@]@."
        (pp_sequence ", " pp_typaram params)
        (Language.TyName.print name)
        (pp_def tydef)

let pp_cmd state cmd ppf =
  match cmd with
  | Term ([], t) -> print ppf "%t@.;;" (pp_term state t)
  | Term (ws, t) ->
      print ppf "fun %t -> %t@.;;" (pp_coercion_vars ws) (pp_term state t)
  | DefEffect e -> pp_def_effect e ppf
  | TopLet defs ->
      print ppf "%t@.;; let %t = %t@.;;"
        (pp_lets "let" (pp_let_def ~top_level:true state) defs)
        (Print.sequence ","
           (fun (f, _, _) -> pp_pattern ~safe:false state f)
           defs)
        (Print.sequence "," (fun (f, _, _) -> pp_pattern state f) defs)
  | TopLetRec defs ->
      print ppf "%t@.;; let %t = %t@.;;"
        (pp_top_let_rec state (Assoc.to_list defs))
        (Print.sequence ","
           (fun (f, _) -> pp_variable state ~safe:false f)
           (Assoc.to_list defs))
        (Print.sequence ","
           (fun (f, _) -> pp_variable state f)
           (Assoc.to_list defs))
  | TyDef defs -> print ppf "type %t@.;;" (pp_sequence "@, and " pp_tydef defs)
