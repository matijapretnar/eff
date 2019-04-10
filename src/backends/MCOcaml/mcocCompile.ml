(* Evaluation of the intermediate language, big step. *)
open CoreUtils
module Core = UntypedSyntax
module MCOC = McocSyntax

module type Formatters = sig
  val warnings : Format.formatter
  val response : Format.formatter
  val output : Format.formatter
  val printing : bool
end

module Backend (F : Formatters) : BackendSignature.T = struct
  
  let warnings_ppf = F.warnings

  let response_ppf = F.response

  let output_ppf = F.output

  type state = {printing: bool; mute_depth: int; prog: string}

  let initial_state = {printing= F.printing; mute_depth= 0; prog= ""}

  let load_mode state =
    {state with printing= false; mute_depth= state.mute_depth + 1}

  let execute_mode state =
    if state.mute_depth <= 1 then
      {state with printing= F.printing; mute_depth = 0}
    else
      {state with mute_depth= state.mute_depth - 1}

  (* Auxiliary functions *)
  let update state translation =
    let actual_translation = Format.flush_str_formatter () in
    let _ = 
      if state.printing then
        (Format.fprintf response_ppf "%s@." actual_translation)
      else
        ()
    in
    {state with prog = state.prog ^ actual_translation}

  let issue_warning txt = 
    Format.fprintf warnings_ppf "Warning: %s@." txt

  let state_ppf = Format.str_formatter

  let translate = Format.fprintf

  (* Translations *)
  let translate_sequence (type a) =
    (* This trick is needed to make it strongly polymorphic.
       Thanks Jane Street Tech Blog. *)
    let rec sequence sep (translator : a -> Format.formatter -> unit) vs ppf
      =
      match vs with
      | [] -> ()
      | [v] -> (translator v ppf)
      | v :: vs ->
          translate ppf "%t@,%s%t" 
            (translator v) sep (sequence sep translator vs)
    in
    sequence

  let translate_field translator (f, v) ppf =
    translate ppf "%t = %t" (McocSymbol.print_field f) (translator v)

  let translate_field_type translator (f, v) ppf =
    translate ppf "%t : %t" (McocSymbol.print_field f) (translator v)
  
  let translate_tuple translator lst ppf =
    match lst with
    | [] -> translate ppf "()"
    | lst ->
      translate ppf "(@[<hov>%t@])" 
        (translate_sequence ", " translator lst)
  
  let translate_record translator assoc ppf =
    let lst = Assoc.to_list assoc in
    translate ppf "{@[<hov>%t@]}"
      (translate_sequence "; " (translate_field translator) lst)

  let translate_record_type translator assoc ppf =
    let lst = Assoc.to_list assoc in
    translate ppf "{@[<hov>%t@]}"
      (translate_sequence "; " (translate_field_type translator) lst)

  let rec translate_abstraction (p, t) ppf =
    translate ppf "%t ->@ %t" (translate_pattern p) (translate_term t)

  and translate_let (p, t) ppf =
    translate ppf "%t = @,%t" (translate_pattern p) (translate_term t)

  and translate_let_rec (name, (p, t)) ppf =
    translate ppf "%t %t = @,%t"
      (McocSymbol.print_variable name)
      (translate_pattern p) (translate_term t)

  and translate_tydef (name, (params, tydef)) ppf =
    let translate_def tydef ppf =
      match tydef with
      | MCOC.TyDefRecord assoc -> 
          translate ppf "%t" (translate_record_type translate_type assoc)
      | MCOC.TyDefSum assoc ->
          let lst = Assoc.to_list assoc in
          let cons_translator ty_opt ppf =
            match ty_opt with
            | (lbl, None) -> translate ppf "%t" (McocSymbol.print_label lbl)
            | (lbl, Some ty) ->
                translate ppf "%t of %t"
                  (McocSymbol.print_label lbl) (translate_type ty)
          in
          translate ppf "@[<hov>%t@]"
            (translate_sequence " | " cons_translator lst)
      | MCOC.TyDefInline ty -> translate ppf "%t" (translate_type ty)
    in
    match params with
    | [] ->
        translate ppf "@[type %t = %t@]@."
          (McocSymbol.print_tyname name) (translate_def tydef)
    | lst ->
        translate ppf "@[type (%t) %t = %t@]@."
          (translate_sequence ", " McocSymbol.print_typaram params)
          (McocSymbol.print_tyname name) (translate_def tydef)

  and translate_case case ppf =
    match case with
    | MCOC.ValueClause abs ->
        translate ppf "@[<hv 2>%t@]" (translate_abstraction abs)
    | MCOC.EffectClause (eff, (p1, p2, t)) ->
        translate ppf 
          ( "@[<hv 2>effect (%t %t) %t ->@," ^^
            "(let %t x = continue (Obj.clone_continuation %t) x in @,%t)@]" )
          (McocSymbol.print_effect eff) (translate_pattern p1)
          (translate_pattern p2) (translate_pattern p2)
          (translate_pattern p2) (translate_term t)
    
  and translate_term t ppf =
    match t with
    | MCOC.Var x -> translate ppf "%t" (McocSymbol.print_variable x)
    | MCOC.Const c -> translate ppf "%t" (Const.print c)
    | MCOC.Annotated (t, ty) -> 
        translate ppf "(%t : %t)" (translate_term t) (translate_type ty)
    | MCOC.Tuple lst -> translate ppf "%t" (translate_tuple translate_term lst)
    | MCOC.Record assoc ->
        translate ppf "%t" (translate_record translate_term assoc)
    | MCOC.Variant (lbl, None) when lbl = CoreTypes.nil -> translate ppf "[]"
    | MCOC.Variant (lbl, None) -> translate ppf "%t" (McocSymbol.print_label lbl)
    | MCOC.Variant (lbl, Some (MCOC.Tuple [hd; tl])) when lbl = CoreTypes.cons ->
        translate ppf "@[<hov>(%t)::(%t)@]"
          (translate_term hd) (translate_term tl)
    | MCOC.Variant (lbl, Some t) ->
        translate ppf "%t @[<hov>%t@]" 
          (McocSymbol.print_label lbl) (translate_term t)
    | MCOC.Lambda a -> translate ppf "@[<hv 2>fun %t@]" (translate_abstraction a)
    | MCOC.Effect eff -> translate ppf "%t" (McocSymbol.print_effect eff)
    | MCOC.Let (lst, t) -> 
        translate ppf "@[<hov>@[<hv 2>let %t@] @,in @,%t@]"
          (translate_sequence "@,and " translate_let lst)
          (translate_term t)
    | MCOC.LetRec (lst, t) ->
        translate ppf "@[@[<hv 2>let rec %t@] @,in@ @,%t@]"
          (translate_sequence "@,and " translate_let_rec lst)
          (translate_term t)
    | MCOC.Match (t, []) ->
        (* Absurd case *)
        translate ppf 
          ("@[<hv>(match %t with | _ ->"
           ^^ " failwith \"void successfully matched\")@]")
          (translate_term t) 
    | MCOC.Match (t, lst) ->
        translate ppf "@[<hv>(match %t with@, | %t)@]"
          (translate_term t) (translate_sequence " | " translate_case lst)
    | MCOC.Apply (MCOC.Effect eff, t2) ->
        translate ppf "perform (%t (%t))"
          (McocSymbol.print_effect eff) (translate_term t2)
    | MCOC.Apply (t1, t2) ->
        translate ppf "@[<hov 2>(%t) @,(%t)@]" (translate_term t1) (translate_term t2)
    | MCOC.Check t -> 
        issue_warning 
          "[#check] commands are ignored when compiling to Multicore OCaml."

  and translate_pattern p ppf =
    match p with
    | MCOC.PVar x ->
        translate ppf "%t"
          (McocSymbol.print_variable ~warnings:(Some warnings_ppf) x)
    | MCOC.PAs (p, x) ->
        translate ppf "%t as %t"
          (translate_pattern p) (McocSymbol.print_variable x)
    | MCOC.PAnnotated (p, ty) -> 
        translate ppf "(%t : %t)" (translate_pattern p) (translate_type ty)
    | MCOC.PConst c -> translate ppf "%t" (Const.print c)
    | MCOC.PTuple lst -> 
        translate ppf "%t" (translate_tuple translate_pattern lst)
    | MCOC.PRecord assoc ->
        translate ppf "%t" (translate_record translate_pattern assoc)
    | MCOC.PVariant (lbl, None) when lbl = CoreTypes.nil -> translate ppf "[]"
    | MCOC.PVariant (lbl, None) -> 
        translate ppf "%t" (McocSymbol.print_label lbl)
    | MCOC.PVariant (lbl, Some (MCOC.PTuple lst))
      when lbl = CoreTypes.cons ->
        translate ppf "[@[<hov>%t@]]"
          (translate_sequence "; " translate_pattern lst)
    | MCOC.PVariant (lbl, Some p) ->
        translate ppf "%t @[<hov>%t@]"
          (McocSymbol.print_label lbl) (translate_pattern p)
    | MCOC.PNonbinding -> translate ppf "_"

  and translate_type ty ppf =
    match ty with
    | MCOC.TyArrow (t1, t2) ->
        translate ppf "@[<h>%t ->@ %t@]"
          (translate_type t1) (translate_type t2)
    | MCOC.TyBasic b -> translate ppf "%s" b
    | MCOC.TyApply (t, []) -> 
        (* we warn when the empty type is translated *)    
        translate ppf "%t" (McocSymbol.print_tyname ~warnings:(Some warnings_ppf) t)
    | MCOC.TyApply (t, [s]) ->
        translate ppf "%t %t" (translate_type s) (McocSymbol.print_tyname t)
    | MCOC.TyApply (t, ts) ->
        translate ppf "(%t) %t"
          (Print.sequence ", " translate_type ts) (McocSymbol.print_tyname t)
    | MCOC.TyParam p -> translate ppf "%t" (McocSymbol.print_typaram p)
    | MCOC.TyTuple [] -> translate ppf "unit"
    | MCOC.TyTuple ts ->
        translate ppf "@[<hov>%t@]" (Print.sequence " * " translate_type ts)

  let translate_def_effect (eff, (ty1, ty2)) ppf =
    translate ppf "@[effect %t : %t ->@ %t@]@."
      (McocSymbol.print_effect eff) (translate_type ty1) (translate_type ty2) 

  let translate_top_let defs ppf =
    translate ppf "@[<hv 2>let %t@]@."
      (translate_sequence "@,and " translate_let defs)

  let translate_top_let_rec defs ppf = 
    translate ppf "@[<hv 2>let rec %t@]@."
      (translate_sequence "@,and " translate_let_rec defs)

  let translate_external name symbol_name translation ppf =
    match translation with
    | McocExternal.Unknown ->
        translate ppf "let %t = failwith \"Unknown external symbol %s.\"@."
          (McocSymbol.print_variable name) symbol_name
    | McocExternal.Exists t ->
        translate ppf "let %t = %s@."
        (McocSymbol.print_variable name) t

  let translate_tydefs tydefs ppf = 
    translate ppf "%t@." (translate_sequence " and " translate_tydef tydefs)

  (* Processing functions *)
  let process_computation state c ty = 
    let t = MCOC.of_computation c in
    update state (translate state_ppf "%t@." (translate_term t))

  let process_type_of state c ty = 
    issue_warning 
      "[#typeof] commands are ignored when compiling to Multicore OCaml." ;
    state

  let process_reset state = 
    issue_warning 
      "[#reset] commands are ignored when compiling to Multicore OCaml." ;
    state

  let process_help state =
    issue_warning 
      ("[#help] commands are ignored when compiling to Multicore OCaml."
      ^ " Not even gods can help you here.") ;
    state
  
  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = MCOC.of_type ty1 in
    let ty2' = MCOC.of_type ty2 in
    let translation = translate_def_effect (eff, (ty1', ty2')) state_ppf in
    update state translation

  let process_top_let state defs vars =
    let converter (p, c) = (MCOC.of_pattern p, MCOC.of_computation c) in
    let defs' = List.map converter defs in
    let translation = translate_top_let defs' state_ppf in
    update state translation

  let process_top_let_rec state defs vars =
    let converter (p, c) = (MCOC.of_pattern p, MCOC.of_computation c) in
    let defs' = Assoc.map converter defs |> Assoc.to_list in
    let translation = translate_top_let_rec defs' state_ppf in
    update state translation

  let process_external state (x, ty, f) =
    match Assoc.lookup f McocExternal.values with
      | None -> Error.runtime "Unknown external symbol %s." f
      | Some (McocExternal.Unknown as unknown) ->
          let warning_text = 
            Printf.sprintf
              ("External symbol %s cannot be compiled. It has been replaced "
              ^^ "with [failwith \"Unknown external symbol %s.\"].") f f
          in
          issue_warning warning_text;
          let translation = translate_external x f unknown state_ppf in
          update state translation
      | Some ((McocExternal.Exists s) as known) ->
          let translation = translate_external x f known state_ppf in
          update state translation

  let process_tydef state tydefs = 
    let converter (ty_params, tydef) = (ty_params, MCOC.of_tydef tydef) in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    let translation = translate_tydefs tydefs' state_ppf in
    update state translation

  let finalize state = Format.fprintf output_ppf "%s" state.prog

end