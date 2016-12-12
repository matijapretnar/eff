(** PRINTER STATE *)

type state = {
  debug: bool;
}

let initial = {
  debug = true;
}


(** TYPES *)

let print_type_param (Type.Ty_Param n) ppf =
   Format.fprintf ppf "'t%d" n

let rec print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Type.Apply ("empty", _) ->
      print "unit"
  | Type.Apply (ty_name, args) ->
      print ~at_level:1 "%t %s" (print_args args) ty_name
  | Type.Param p ->
      print "%t" (print_type_param p)
  | Type.Basic t ->
      print "%s" t
  | Type.Tuple tys ->
      print ~at_level:1 "%t" (Print.sequence "*" print_type tys)
  | Type.Arrow (ty, drty) ->
      print ~at_level:2 "%t -> %t" (print_type ~max_level:1 ty) (print_dirty_type drty)
  | Type.Handler ((ty1, _), (ty2, _)) ->
      print ~at_level:2 "(%t, ???, %t) handler" (print_type ty1) (print_type ty2)

and print_dirty_type (ty, drt) ppf =
  Format.fprintf ppf "_"

and print_args (tys, _, _) ppf =
  match tys with
  | [] -> ()
  | _ -> Format.fprintf ppf "(%t)" (Print.sequence "," print_type tys)


(** TYPE DEFINITIONS *)

let rec print_params (tys, _, _) ppf =
  match tys with
  | [] -> ()
  | _ -> Format.fprintf ppf "(%t)" (Print.sequence "," print_type_param tys)

let print_tydef_body ty_def ppf =
  match ty_def with
  | Tctx.Record flds ->
      let print_field (fld, ty) ppf = Format.fprintf ppf "%s: %t" fld (print_type ty) in
      Format.fprintf ppf "{@[<hov>%t@]}" (Print.sequence "; " print_field flds)
  | Tctx.Sum variants ->
      let print_variant (lbl, ty) ppf =
        match ty with
        | None -> Format.fprintf ppf "%s" lbl
        | Some ty -> Format.fprintf ppf "%s of %t" lbl (print_type ~max_level:0 ty)
      in
      Format.fprintf ppf "@[<hov>%t@]" (Print.sequence "|" print_variant variants)
  | Tctx.Inline ty -> print_type ty ppf

let print_tydef (name, (params, body)) ppf =
  Format.fprintf ppf "%t %s = %t" (print_params params) name (print_tydef_body body)

let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs)


(** SYNTAX *)

let print_variable = Typed.Variable.print

let format_region (Type.Region_Param i) = i

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

let print_effect_region (eff, (region)) ppf = Print.print ppf "Effect_%s -> %d" eff (format_region region)

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.Typed.term with
  | Typed.PVar x ->
      print "%t" (print_variable x)
  | Typed.PAs (p, x) ->
      print "%t as %t" (print_pattern p) (print_variable x)
  | Typed.PConst c ->
      Const.print c ppf
  | Typed.PTuple lst ->
      Print.tuple print_pattern lst ppf
  | Typed.PRecord lst ->
      Print.record print_pattern lst ppf
  | Typed.PVariant (lbl, None) when lbl = Common.nil ->
      print "[]"
  | Typed.PVariant (lbl, None) ->
      print "%s" lbl
  | Typed.PVariant ("(::)", Some ({ Typed.term = Typed.PTuple [p1; p2] })) ->
      print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | Typed.PVariant (lbl, Some p) ->
      print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | Typed.PNonbinding ->
      print "_"

let is_pure_function e =
  Scheme.is_pure_function_type ~loc:e.Typed.location e.Typed.scheme

let is_pure_abstraction {Typed.term = (_, c)} =
  Scheme.is_pure c.Typed.scheme

let is_pure_handler e =
  false

let rec print_expression ?max_level st e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Typed.term with
  | Typed.Var x ->
      print "%t" (print_variable x)
  | Typed.BuiltIn s ->
      print "%s" s
  | Typed.Const c ->
      print "%t" (Const.print c)
  | Typed.Tuple lst ->
      Print.tuple (print_expression st) lst ppf
  | Typed.Record lst ->
      Print.record (print_expression st) lst ppf
  | Typed.Variant (lbl, None) ->
      print "%s" lbl
  | Typed.Variant (lbl, Some e) ->
      print ~at_level:1 "%s %t" lbl (print_expression st e)
  | Typed.Lambda a ->
      let pure = is_pure_function e in
      print ~at_level:2 "fun %t" (print_abstraction ~pure st a)
  | Typed.Handler h ->
      let pure = is_pure_handler e in
      print "%t" (print_handler ~pure st h)
  | Typed.Effect eff ->
      print ~at_level:2 "effect %t" (print_effect eff)
  | Typed.Pure c ->
      print ~at_level:1 "%t" (print_computation ~max_level:0 ~pure:true st c)

and print_function_argument ?max_level st e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  if is_pure_function e then
    print "(fun x -> value (%t x))" (print_expression ~max_level:1 st e)
  else
    print_expression ~max_level:0 st e ppf

and print_computation ?max_level ~pure st c ppf =
  let is_pure_computation = Scheme.is_pure ~loc:c.Typed.location c.Typed.scheme in
  let expect_pure_computation = pure in
  if st.debug then
    Print.debug ~loc:c.Typed.location "%t@.expect: %b, is: %b@.BEGIN@.%t@.END"
      (Scheme.print_dirty_scheme c.Typed.scheme)
      expect_pure_computation
      is_pure_computation
      (print_computation' ~pure {initial with debug=false} c);
  match expect_pure_computation, is_pure_computation with
  | true, true ->
      print_computation' ?max_level ~pure:true st c ppf
  | true, false ->
      assert false
  | false, true ->
      Print.print ?max_level ppf "value %t" (print_computation' ~max_level:0 ~pure:true st c)
  | false, false ->
      print_computation' ?max_level ~pure:false st c ppf
and print_computation' ?max_level ~pure st c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
      print ~at_level:1 "%t@ %t"
        (print_expression ~max_level:1 st e1)
        (print_function_argument ~max_level:0 st e2)
  | Typed.Value e ->
      (* assert pure; *)
      print ~at_level:1 "%t" (print_expression ~max_level:0 st e)
  | Typed.Match (e, []) ->
      print ~at_level:2 "(match %t with _ -> assert false)"
        (print_expression st e)
  | Typed.Match (e, lst) ->
      print ~at_level:2 "(match %t with @[<v>| %t@])"
        (print_expression st e)
        (Print.cases (print_abstraction ~pure st) lst)
  | Typed.Handle (e, c) ->
      print ~at_level:1 "handle %t %t"
        (print_expression ~max_level:0 st e)
        (print_computation ~max_level:0 ~pure:false st c)
  | Typed.Let (lst, c) ->
      print ~at_level:2 "%t" (print_multiple_bind ~pure st (lst, c))
  | Typed.LetRec (lst, c) ->
      print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " (print_let_rec_abstraction st) lst) (print_computation ~pure st c)
  | Typed.Call (eff, e, a) ->
      assert (not pure);
      print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 st e) (print_abstraction ~pure st a)
  | Typed.Bind (c1, {Typed.term = (p, c2)}) when pure ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
        (print_pattern p)
        (print_computation ~max_level:0 ~pure st c1)
        (print_computation ~pure st c2)
  | Typed.Bind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
        (print_computation ~max_level:0 ~pure st c1)
        (print_abstraction ~pure st a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
        (print_pattern p)
        (print_expression st e)
        (print_computation ~pure st c)

and print_handler ~pure st h ppf =
  Print.print ppf
    "{@[<hov>
      value_clause = (@[fun %t@]);@ 
      finally_clause = (@[fun %t@]);@ 
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with %t) : a -> (b -> _ computation) -> _ computation))
    @]}"
    (print_abstraction ~pure st h.Typed.value_clause)
    (print_abstraction ~pure st h.Typed.finally_clause)
    (print_effect_clauses ~pure st h.Typed.effect_clauses)

and print_effect_clauses ~pure st eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
      print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), {Typed.term = (p1, p2, c)}) :: cases ->
      print ~at_level:1
        "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
        (print_effect eff)
        (print_pattern p1) (print_type t1)
        (print_pattern p2) (print_type t2)
        (print_computation ~pure st c)
        (print_effect_clauses ~pure st cases)

and print_abstraction ~pure st {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation ~pure st c)

and print_multiple_bind ~pure st (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation ~pure:false st c')
  | (p, c) :: lst ->
      if pure then
        Format.fprintf ppf "let %t = %t in %t"
        (print_pattern p) (print_computation ~pure st c) (print_multiple_bind ~pure st (lst, c'))
      else
        Format.fprintf ppf "%t >> fun %t -> %t"
        (print_computation ~pure st c) (print_pattern p) (print_multiple_bind ~pure st (lst, c'))

(* and print_let_abstraction st (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation st c) *)

and print_top_let_abstraction st (p, c) ppf =
  match c.Typed.term with
  | Typed.Value e -> 
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 st e)
  | _ -> 
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 ~pure:false st c)

and print_let_rec_abstraction st (x, a) ppf =
  let pure = is_pure_abstraction a in
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction ~pure st a)


(** COMMANDS *)

let compiled_filename fn = fn ^ ".ml"

let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs)

let print_computation_effects ?max_level c ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    let get_dirt (_,(_,dirt),_) = dirt in
    let get_type (_,(ty,dirt),_) = ty in
    let rest = (get_dirt(c.Typed.scheme)).Type.rest in
    let rest_int (Type.Dirt_Param i) = i in
    (* Here we have access to the effects *)
    (
    Format.fprintf ppf "Effects of a computation: \n";
    let f elem =
        Format.fprintf ppf "\t%t\n" (print_effect_region elem) in
        List.iter f (get_dirt(c.Typed.scheme)).Type.ops;
    Format.fprintf ppf "\nRest: %d\n" (rest_int rest);
    Format.fprintf ppf "Type: %t\n" (print_type (get_type(c.Typed.scheme)));
    )

let print_command st (cmd, _) ppf =
  match cmd with
  | Typed.DefEffect (eff, (ty1, ty2)) ->
      Print.print ppf "type (_, _) effect += %t : (%t, %t) effect" (print_effect eff) (print_type ty1) (print_type ty2)
  | Typed.Computation c ->
      print_computation ~pure:false st c ppf
  | Typed.TopLet (defs, _) ->
      Print.print ppf "let %t" (Print.sequence "\nand\n" (print_top_let_abstraction st) defs)
(*   | Typed.TopLetRec (defs, _) ->
      Print.print ppf "let rec %t" (Print.sequence "\nand\n" (print_let_rec_abstraction st) defs)
 *)  | Typed.Use fn ->
      Print.print ppf "#use %S" (compiled_filename fn)
  | Typed.External (x, ty, f) ->
      Print.print ppf "let %t = ( %s )" (print_variable x) f
  | Typed.Tydef tydefs ->
      print_tydefs tydefs ppf
  | Typed.Reset ->
      Print.print ppf "(* #reset directive not supported by OCaml *)"
  | Typed.Quit ->
      Print.print ppf "(* #quit directive not supported by OCaml *)"
  | Typed.TypeOf _ ->
      Print.print ppf "(* #type directive not supported by OCaml *)"
  | Typed.Help ->
      Print.print ppf "(* #help directive not supported by OCaml *)"

let print_commands cmds ppf =
  let st = initial in
  Print.sequence "\n\n;;\n\n" (print_command st) cmds ppf


(** THE REST *)

let print_computation_effects ?max_level c ppf =
    let print ?at_level = Print.print ?max_level ?at_level ppf in
    let get_dirt (_,(_,dirt),_) = dirt in
    (* Here we have access to the effects *)
    (Format.fprintf ppf "Effects of a computation: \n";
    let f elem =
        Format.fprintf ppf "\t%t" (print_effect elem) in
        List.iter f (get_dirt(c.Typed.scheme)).Type.ops;)
