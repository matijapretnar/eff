(* Evaluation of ExEff, big step via SkelEff. *)
open CoreUtils
module Multicore = MulticoreSyntax
module FromSkelEff = SkelEffToMulticore

module type BackendParameters = sig
  val output_file : string
end

module Backend (P : BackendParameters) : BackendSignature.T = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)
  type state = {prog: string}

  let initial_state = {prog= ""}

  (* Auxiliary functions *)
  let update state translation =
    let actual_translation = Format.flush_str_formatter () in
    Format.fprintf !Config.output_formatter "%s@?" actual_translation ;
    {prog= state.prog ^ actual_translation}

  let state_ppf = Format.str_formatter

  let translate = Format.fprintf

  (* ------------------------------------------------------------------------ *)
  (* Auxiliary translations *)

  let translate_sequence (type a) =
    (* This trick is needed to make it strongly polymorphic.
       Thanks Jane Street Tech Blog. *)
    let rec sequence sep (translator : a -> Format.formatter -> unit) vs ppf =
      match vs with
      | [] -> ()
      | [v] -> translator v ppf
      | v :: vs ->
          translate ppf
            ("%t" ^^ sep ^^ "%t")
            (translator v)
            (sequence sep translator vs)
    in
    sequence

  let translate_field translator sep (f, v) ppf =
    translate ppf "%t %s %t" (MulticoreSymbol.print_field f) sep (translator v)

  let translate_tuple translator lst ppf =
    match lst with
    | [] -> translate ppf "()"
    | lst ->
        translate ppf "(@[<hov>%t@])" (translate_sequence ", " translator lst)

  let translate_record translator sep assoc ppf =
    let lst = Assoc.to_list assoc in
    translate ppf "{@[<hov>%t@]}"
      (translate_sequence "; " (translate_field translator sep) lst)

  (* ------------------------------------------------------------------------ *)
  (* Translations *)

  let rec translate_term t ppf =
    match t with
    | Multicore.Var x -> translate ppf "%t" (MulticoreSymbol.print_variable x)
    | Multicore.Const c -> translate ppf "%t" (Const.print c)
    | Multicore.Annotated (t, ty) ->
        translate ppf "(%t : %t)" (translate_term t) (translate_type ty)
    | Multicore.Tuple lst ->
        translate ppf "%t" (translate_tuple translate_term lst)
    | Multicore.Record assoc ->
        translate ppf "%t" (translate_record translate_term "=" assoc)
    | Multicore.Variant (lbl, None) when lbl = CoreTypes.nil ->
        translate ppf "[]"
    | Multicore.Variant (lbl, None) ->
        translate ppf "%t" (MulticoreSymbol.print_label lbl)
    | Multicore.Variant (lbl, Some (Multicore.Tuple [hd; tl]))
      when lbl = CoreTypes.cons ->
        translate ppf "@[<hov>(%t::%t)@]" (translate_term hd)
          (translate_term tl)
    | Multicore.Variant (lbl, Some t) ->
        translate ppf "(%t @[<hov>%t@])"
          (MulticoreSymbol.print_label lbl)
          (translate_term t)
    | Multicore.Lambda a ->
        translate ppf "@[<hv 2>fun %t@]" (translate_abstraction a)
    | Multicore.Function lst ->
        translate ppf "@[<hv>(function @, | %t)@]"
          (translate_sequence "@, | " translate_case lst)
    | Multicore.Effect eff ->
        translate ppf "%t" (MulticoreSymbol.print_effect eff)
    | Multicore.Let (lst, t) ->
        translate ppf "@[<hv>@[<hv>%tin@] @,%t@]" (translate_let lst)
          (translate_term t)
    | Multicore.LetRec (lst, t) ->
        translate ppf "@[<hv>@[<hv>%tin@] @,%t@]" (translate_let_rec lst)
          (translate_term t)
    | Multicore.Match (t, []) ->
        (* Absurd case *)
        translate ppf
          ( "@[<hv>(match %t with | _ ->"
          ^^ " failwith \"void successfully matched\")@]" )
          (translate_term t)
    | Multicore.Match (t, lst) ->
        translate ppf "@[<hv>(match %t with@, | %t)@]" (translate_term t)
          (translate_sequence "@, | " translate_case lst)
    | Multicore.Apply (Multicore.Effect eff, (Multicore.Lambda _ as t2)) ->
        translate ppf "perform (%t (%t))"
          (MulticoreSymbol.print_effect eff)
          (translate_term t2)
    | Multicore.Apply (Multicore.Effect eff, t2) ->
        translate ppf "perform (%t %t)"
          (MulticoreSymbol.print_effect eff)
          (translate_term t2)
    | Multicore.Apply (t1, t2) ->
        translate ppf "@[<hov 2>(%t) @,(%t)@]" (translate_term t1)
          (translate_term t2)
    | Multicore.Check t ->
        Print.warning
          "[#check] commands are ignored when compiling to Multicore OCaml."

  and translate_pattern p ppf =
    match p with
    | Multicore.PVar x -> translate ppf "%t" (MulticoreSymbol.print_variable x)
    | Multicore.PAs (p, x) ->
        translate ppf "%t as %t" (translate_pattern p)
          (MulticoreSymbol.print_variable x)
    | Multicore.PAnnotated (p, ty) ->
        translate ppf "(%t : %t)" (translate_pattern p) (translate_type ty)
    | Multicore.PConst c -> translate ppf "%t" (Const.print c)
    | Multicore.PTuple lst ->
        translate ppf "%t" (translate_tuple translate_pattern lst)
    | Multicore.PRecord assoc ->
        translate ppf "%t" (translate_record translate_pattern "=" assoc)
    | Multicore.PVariant (lbl, None) when lbl = CoreTypes.nil ->
        translate ppf "[]"
    | Multicore.PVariant (lbl, None) ->
        translate ppf "%t" (MulticoreSymbol.print_label lbl)
    | Multicore.PVariant (lbl, Some (Multicore.PTuple [hd; tl]))
      when lbl = CoreTypes.cons ->
        translate ppf "@[<hov>(%t::%t)@]" (translate_pattern hd)
          (translate_pattern tl)
    | Multicore.PVariant (lbl, Some p) ->
        translate ppf "(%t @[<hov>%t@])"
          (MulticoreSymbol.print_label lbl)
          (translate_pattern p)
    | Multicore.PNonbinding -> translate ppf "_"

  and translate_type ty ppf =
    match ty with
    | Multicore.TyArrow (t1, t2) ->
        translate ppf "@[<h>(%t ->@ %t)@]" (translate_type t1)
          (translate_type t2)
    | Multicore.TyBasic b -> translate ppf "%s" b
    | Multicore.TyApply (t, []) ->
        translate ppf "%t" (MulticoreSymbol.print_tyname t)
    | Multicore.TyApply (t, ts) ->
        translate ppf "(%t) %t"
          (Print.sequence ", " translate_type ts)
          (MulticoreSymbol.print_tyname t)
    | Multicore.TyParam p ->
        translate ppf "%t" (MulticoreSymbol.print_typaram p)
    | Multicore.TyTuple [] -> translate ppf "unit"
    | Multicore.TyTuple ts ->
        translate ppf "@[<hov>(%t)@]" (Print.sequence " * " translate_type ts)

  and translate_tydef (name, (params, tydef)) ppf =
    let translate_def tydef ppf =
      match tydef with
      | Multicore.TyDefRecord assoc ->
          translate ppf "%t" (translate_record translate_type ":" assoc)
      | Multicore.TyDefSum assoc ->
          let lst = Assoc.to_list assoc in
          let cons_translator ty_opt ppf =
            match ty_opt with
            | lbl, None -> translate ppf "%t" (MulticoreSymbol.print_label lbl)
            | lbl, Some ty ->
                translate ppf "%t of %t"
                  (MulticoreSymbol.print_label lbl)
                  (translate_type ty)
          in
          translate ppf "@[<hov>%t@]"
            (translate_sequence "@, | " cons_translator lst)
      | Multicore.TyDefInline ty -> translate ppf "%t" (translate_type ty)
    in
    match params with
    | [] ->
        translate ppf "@[type %t = %t@]@."
          (MulticoreSymbol.print_tyname name)
          (translate_def tydef)
    | lst ->
        translate ppf "@[type (%t) %t = %t@]@."
          (translate_sequence ", " MulticoreSymbol.print_typaram params)
          (MulticoreSymbol.print_tyname name)
          (translate_def tydef)

  and translate_def_effect (eff, (ty1, ty2)) ppf =
    translate ppf "@[effect %t : %t ->@ %t@]@."
      (MulticoreSymbol.print_effect eff)
      (translate_type ty1) (translate_type ty2)

  and translate_top_let defs ppf =
    translate ppf "@[<hv>%t@]@." (translate_let defs)

  and translate_top_let_rec defs ppf =
    translate ppf "@[<hv>%t@]@." (translate_let_rec defs)

  and translate_external name symbol_name translation ppf =
    match translation with
    | MulticoreExternal.Unknown ->
        translate ppf "let %t = failwith \"Unknown external symbol %s.\"@."
          (MulticoreSymbol.print_variable name)
          symbol_name
    | MulticoreExternal.Exists t ->
        translate ppf "let %t = %s@." (MulticoreSymbol.print_variable name) t

  and translate_tydefs tydefs ppf =
    translate ppf "%t@." (translate_sequence "@, and " translate_tydef tydefs)

  and translate_abstraction (p, t) ppf =
    translate ppf "%t ->@ %t" (translate_pattern p) (translate_term t)

  and translate_let lst ppf =
    let rec sequence lst ppf =
      match lst with
      | [] -> ()
      | abs :: tl ->
          let p_lst, t = abs_to_multiarg_abs abs in
          translate ppf "@[<hv 2>and %t = @,%t@] @,%t"
            (translate_sequence " " translate_pattern p_lst)
            (translate_term t) (sequence tl)
    in
    (* First one *)
    match lst with
    | [] -> ()
    | abs :: tl ->
        let p_lst, t = abs_to_multiarg_abs abs in
        translate ppf "@[<hv 2>let %t = @,%t@] @,%t"
          (translate_sequence " " translate_pattern p_lst)
          (translate_term t) (sequence tl)

  and translate_let_rec lst ppf =
    let rec sequence lst ppf =
      match lst with
      | [] -> ()
      | (name, abs) :: tl ->
          let p_lst, t = abs_to_multiarg_abs abs in
          translate ppf "@[<hv 2>and %t %t = @,%t@] @,%t"
            (MulticoreSymbol.print_variable name)
            (translate_sequence " " translate_pattern p_lst)
            (translate_term t) (sequence tl)
    in
    (* First one *)
    match lst with
    | [] -> ()
    | (name, abs) :: tl ->
        let p_lst, t = abs_to_multiarg_abs abs in
        translate ppf "@[<hv 2>let rec %t %t = @,%t@] @,%t"
          (MulticoreSymbol.print_variable name)
          (translate_sequence " " translate_pattern p_lst)
          (translate_term t) (sequence tl)

  and abs_to_multiarg_abs (p, t) =
    match t with
    | Multicore.Lambda abs ->
        let p_list, t' = abs_to_multiarg_abs abs in
        (p :: p_list, t')
    | _ -> ([p], t)

  and translate_case case ppf =
    match case with
    | Multicore.ValueClause abs ->
        translate ppf "@[<hv 2>%t@]" (translate_abstraction abs)
    | Multicore.EffectClause (eff, (p1, p2, t)) ->
        if p2 = Multicore.PNonbinding then
          translate ppf "@[<hv 2>effect (%t %t) %t -> @,%t@]"
            (MulticoreSymbol.print_effect eff)
            (translate_pattern p1) (translate_pattern p2) (translate_term t)
        else
          translate ppf
            ( "@[<hv 2>effect (%t %t) %t ->@,"
            ^^ "(let %t x = continue (Obj.clone_continuation %t) x in @,%t)@]"
            )
            (MulticoreSymbol.print_effect eff)
            (translate_pattern p1) (translate_pattern p2)
            (translate_pattern p2) (translate_pattern p2) (translate_term t)

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state c ty =
    (* Erasure ExEff -> SkelEff *)
    let c' = Erasure.typed_to_erasure_comp Assoc.empty c in
    let t = FromSkelEff.of_computation c' in
    update state
      (translate state_ppf
         "let _ = @.@[<hv>(_ocaml_tophandler) (fun _ -> @,%t@,)@];;@."
         (translate_term t))

  let process_type_of state c ty =
    Print.warning
      "[#typeof] commands are ignored when compiling to Multicore OCaml." ;
    state

  let process_def_effect state (eff, (ty1, ty2)) =
    let ty1' = FromSkelEff.of_type ty1 in
    let ty2' = FromSkelEff.of_type ty2 in
    let translation = translate_def_effect (eff, (ty1', ty2')) state_ppf in
    update state translation

  let process_top_let state defs vars =
    let converter (p, c) =
      (FromSkelEff.of_pattern (Erasure.typed_to_erasure_pattern p),
        FromSkelEff.of_computation (Erasure.typed_to_erasure_comp Assoc.empty c))
    in
    let defs' = List.map converter defs in
    let translation = translate_top_let defs' state_ppf in
    update state translation

  let process_top_let_rec state defs vars =
    let converter (p, c) =
      (FromSkelEff.of_pattern (Erasure.typed_to_erasure_pattern p),
        FromSkelEff.of_computation (Erasure.typed_to_erasure_comp Assoc.empty c))
    in
    let defs' = Assoc.map converter defs |> Assoc.to_list in
    let translation = translate_top_let_rec defs' state_ppf in
    update state translation

  let process_external state (x, ty, f) =
    match Assoc.lookup f MulticoreExternal.values with
    | None -> Error.runtime "Unknown external symbol %s." f
    | Some (MulticoreExternal.Unknown as unknown) ->
        Print.warning
          ( "External symbol %s cannot be compiled. It has been replaced "
          ^^ "with [failwith \"Unknown external symbol %s.\"]." )
          f f ;
        let translation = translate_external x f unknown state_ppf in
        update state translation
    | Some (MulticoreExternal.Exists s as known) ->
        let translation = translate_external x f known state_ppf in
        update state translation

  let process_tydef state tydefs =
    let converter (ty_params, tydef) = (ty_params, FromSkelEff.of_tydef tydef) in
    let tydefs' = Assoc.map converter tydefs |> Assoc.to_list in
    let translation = translate_tydefs tydefs' state_ppf in
    update state translation

  let finalize state =
    let channel = open_out P.output_file in
    let output_ppf = Format.formatter_of_out_channel channel in
    Format.fprintf output_ppf "%s" state.prog ;
    close_out channel
end
