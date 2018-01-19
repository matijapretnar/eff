(** TYPES *)


(* let rec print_type ?max_level ty ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match ty with
  | Erasure.Apply ("empty", _) ->
    print "unit"
  | Erasure.Apply (ty_name, args) ->
    print ~at_level:1 "%t %s" (print_args args) ty_name
  | Erasure.TyParam p ->
    print "%t" (Params.print_ty_param p)
  | Erasure.Basic t ->
    print "(%s)" t
  | Erasure.Tuple tys ->
    print ~at_level:1 "(%t)" (Print.sequence "*" print_type tys)
  | Erasure.Arrow (ty, drty) ->
    print ~at_level:2 "(%t -> %t)" (print_type ~max_level:1 ty) (print_dirty_type drty)
  | Erasure.Handler {value=drty1; finally=drty2} ->
    print ~at_level:2 "(%t -> %t)" (print_dirty_type drty1) (print_dirty_type drty2)
 *)
(* and print_dirty_type ty ppf =
  Format.fprintf ppf "%t computation" (print_type ~max_level:0 ty)
 *)
(* and print_args tys ppf =
  match tys with
  | [] -> ()
  | _ -> Format.fprintf ppf "(%t)" (Print.sequence "," print_type tys)
 *)

(** TYPE DEFINITIONS *)

(* let rec print_params params ppf =
  match Params.project_ty_params params with
  | [] -> ()
  | tys -> Format.fprintf ppf "(%t)" (Print.sequence "," Params.print_type_param tys) *)

(* let print_tydef_body ty_def ppf =
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
  | Tctx.Inline ty -> print_type ty ppf *)

(* let print_tydef (name, (params, body)) ppf =
  Format.fprintf ppf "%t %s = %t" (print_params params) name (print_tydef_body body) *)

(* let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs) *)


(** SYNTAX *)

let print_variable = Erasure.Variable.print ~safe:true

let print_effect (eff, _) ppf = Print.print ppf "Effect_%s" eff

(* let print_effect_region (eff, (region)) ppf = Print.print ppf "Effect_%s -> %t" eff (Params.print_region_param region) *)

let rec print_pattern ?max_level p ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match p.Erasure.term with
  | Erasure.PEVar x ->
    print "%t" (print_variable x)
  | Erasure.PEAs (p, x) ->
    print "%t as %t" (print_pattern p) (print_variable x)
  | Erasure.PEConst c ->
    Const.print c ppf
  | Erasure.PETuple lst ->
    Print.tuple print_pattern lst ppf
  | Erasure.PERecord lst ->
    Print.record print_pattern lst ppf
  | Erasure.PEVariant (lbl, None) when lbl = OldUtils.nil ->
    print "[]"
  | Erasure.PEVariant (lbl, None) ->
    print "%s" lbl
  | Erasure.PEVariant ("(::)", Some ({ Erasure.term = Erasure.PETuple [p1; p2] })) ->
    print ~at_level:1 "((%t) :: (%t))" (print_pattern p1) (print_pattern p2)
  | Erasure.PEVariant (lbl, Some p) ->
    print ~at_level:1 "(%s @[<hov>%t@])" lbl (print_pattern p)
  | Erasure.PENonbinding ->
    print "_"


(* let compiled_filename fn = fn ^ ".ml" *)

(* let print_tydefs tydefs ppf =
  Format.fprintf ppf "type %t" (Print.sequence "\nand\n" print_tydef tydefs) *)

let rec print_expression ?max_level e ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Erasure.term with
  | Erasure.EVar x ->
      print "%t" (print_variable x)
  | Erasure.EBuiltIn (s, n) ->
      if n = 1 then
        print ~at_level:1 "lift_unary %s" s
      else if n = 2 then
        print ~at_level:1 "lift_binary %s" s
      else
        assert false
  | Erasure.EConst c ->
      print "%t" (Const.print c)
  | Erasure.ETuple lst ->
      Print.tuple print_expression lst ppf
  | Erasure.ERecord lst ->
      Print.record print_expression lst ppf
  | Erasure.EVariant (lbl, None) ->
      print "%s" lbl
  | Erasure.EVariant (lbl, Some e) ->
      print ~at_level:1 "(%s %t)" lbl (print_expression e)
  | Erasure.ELambda (x, _, c) ->
    print "fun (%t) -> %t" (print_pattern x) (print_computation c)
  | Erasure.EEffect eff ->
      print ~at_level:2 "effect %t" (print_effect eff)
  | Erasure.EHandler h ->
      print ~at_level:2 "fun c -> handler {@[<hov> value_clause = (@[fun %t@]);@ effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
             ((match x with %t) : a -> (b -> _ computation) -> _ computation)) @]} c"
      (print_abstraction_with_ty h.Erasure.value_clause)
      (print_effect_clauses h.Erasure.effect_clauses)
  | EBigLambdaSkel (_, e) -> print "%t" (print_expression e)
  | EApplySkelExp (e, _)-> print "%t" (print_expression e)

and print_computation ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Erasure.term with
  | Erasure.EValue e ->
      print ~at_level:1 "value %t" (print_expression ~max_level:0 e)
  | Erasure.ELetVal (x, e, c) ->
      print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t" (print_variable x) (print_expression e) (print_computation c)
  | Erasure.EApply (e1, e2) ->
      print ~at_level:1 "%t@ %t" (print_expression ~max_level:1 e1) (print_expression ~max_level:0 e2)
  | Erasure.EHandle (e, c) ->
      print ~at_level:1 "%t %t" (print_expression ~max_level:0 e) (print_computation ~max_level:0 c)
  | Erasure.ECall (eff, e, a) ->
      print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction_with_ty a)
  | Erasure.EBind (c1, a) ->
      print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]" (print_computation ~max_level:0 c1) (print_abstraction a)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
      print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((eff_name, (t1, t2)) as eff), {Erasure.term = (p1, p2, c)}) :: cases ->
      print ~at_level:1 "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
      (print_effect eff) (print_pattern p1) (Types.print_target_ty t1) (print_pattern p2) (Types.print_target_ty t2) (print_computation c) (print_effect_clauses cases)

and print_abstraction {Erasure.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

and print_abstraction_with_ty {Erasure.term = (p,_, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation c)

(* and print_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation c) *)

(* and print_top_let_abstraction (p, c) ppf =
  match c.Erasure.term with
  | Erasure.Value e ->
    Format.fprintf ppf "%t = %t" (print_pattern p) (print_expression ~max_level:0 e)
  | _ ->
    Format.fprintf ppf "%t = run %t" (print_pattern p) (print_computation ~max_level:0 c) *)

(* and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a) *)

(* let print_command (cmd, _) ppf =
  match cmd with
  | Erasure.DefEffect (eff, (ty1, ty2)) as full_effect ->
      Print.print ppf "type (_, _) effect += %s : (%t, %t) effect" (eff) (Types.print_target_ty ty1) (Types.print_target_ty ty2)
  | Erasure.Computation c ->
      print_computation c ppf *)
(*   | Erasure.TopLet (defs, _) ->
      Print.print ppf "let %t" (Print.sequence "\nand\n" print_top_let_abstraction defs)
  | Erasure.TopLetRec (defs, _) ->
      Print.print ppf "let rec %t" (Print.sequence "\nand\n" print_let_rec_abstraction defs)
  | Erasure.Use fn ->
      Print.print ppf "#use %S" (compiled_filename fn)
  | Erasure.External (x, ty, f) ->
      begin match ty with
      | Erasure.Arrow (_, (Erasure.Arrow _, _)) -> Print.print ppf "let %t x = lift_binary ( %s ) x" (print_variable x) f
      | Erasure.Arrow (_, _) -> Print.print ppf "let %t x = lift_unary ( %s ) x" (print_variable x) f
      end 
  | Erasure.Tydef tydefs ->
      print_tydefs tydefs ppf
  | Erasure.TypeOf _ ->
      Print.print ppf "(* #type directive not supported by OCaml *)"
*)
(*   | Erasure.Reset ->
      Print.print ppf "(* #reset directive not supported by OCaml *)"
  | Erasure.Quit ->
      Print.print ppf "(* #quit directive not supported by OCaml *)"
 
  | Erasure.Help ->
      Print.print ppf "(* #help directive not supported by OCaml *)"
 *)