open Utils
open Language
open Type

type state = (TyName.t, type_data) Assoc.t (* make me a map *)

let initial_state =
  Assoc.of_list
    [
      ( Type.bool_tyname,
        { params = empty_tydef_params; type_def = Inline bool_ty } );
      ( Type.unit_tyname,
        { params = empty_tydef_params; type_def = Inline unit_ty } );
      ( Type.int_tyname,
        { params = empty_tydef_params; type_def = Inline int_ty } );
      ( Type.string_tyname,
        { params = empty_tydef_params; type_def = Inline string_ty } );
      ( Type.float_tyname,
        { params = empty_tydef_params; type_def = Inline float_ty } );
      ( Type.list_tyname,
        let a_ty =
          Type.tyParam Type.list_ty_param (Skeleton.Param Type.list_skel)
        in
        let list_nil = (Type.nil, None) in
        let list_cons =
          ( Type.cons,
            Some
              (tuple
                 [
                   a_ty;
                   apply
                     ( Type.list_tyname,
                       TyParam.Map.singleton Type.list_ty_param (a_ty, Covariant)
                     );
                 ]) )
        in
        {
          params =
            {
              empty_tydef_params with
              type_params =
                TyParam.Map.singleton Type.list_ty_param
                  (Skeleton.Param Type.list_skel, Covariant);
              skel_params = Skeleton.Param.Set.singleton Type.list_skel;
            };
          type_def = Sum (Type.Field.Map.of_bindings [ list_nil; list_cons ]);
        } );
      ( Type.empty_tyname,
        { params = empty_tydef_params; type_def = Sum Type.Field.Map.empty } );
    ]

let rec find_some f = function
  | [] -> None
  | hd :: tl -> ( match f hd with Some y -> Some y | None -> find_some f tl)

(** [find_variant lbl] returns the information about the variant type that defines the
    label [lbl]. *)
let find_variant lbl st =
  let construct = function
    | ty_name, { params; type_def = Sum vs } -> (
        match Type.Field.Map.find_opt lbl vs with
        | Some us -> Some (ty_name, params, vs, us)
        | None -> None)
    | _ -> None
  in
  find_some construct (Assoc.to_list st)

(** [find_field fld] returns the information about the record type that defines the field
    [fld]. *)

let find_field fld (st : state) =
  let construct = function
    | ty_name, { params; type_def = Record flds } -> (
        match Type.Field.Map.find_opt fld flds with
        | Some _ -> Some (ty_name, params, flds)
        | None -> None)
    | _ -> None
  in
  find_some construct (Assoc.to_list st)

let apply_to_tydef_params tyname (ps : tydef_params) p_map =
  apply
    ( tyname,
      p_map
      |> TyParam.Map.map (fun p ->
             let skel, variance = TyParam.Map.find p ps.type_params in
             (tyParam p skel, variance)) )

(** [infer_variant lbl] finds a variant type that defines the label [lbl] and returns it
    with refreshed type parameters and additional information needed for type
    inference. *)
let infer_variant lbl st =
  match find_variant lbl st with
  | None -> assert false
  | Some (ty_name, ps, _, u) ->
      let ps', fresh_subst, p_map = Substitution.of_tydef_parameters ps in
      let u' =
        Option.map
          (fun x -> Substitution.apply_substitutions_to_type fresh_subst x)
          u
      in
      (u', apply_to_tydef_params ty_name ps' p_map)

(** [infer_field fld] finds a record type that defines the field [fld] and returns it with
    refreshed type parameters and additional information needed for type inference. *)
let infer_field fld st =
  match find_field fld st with
  | None -> assert false
  | Some (ty_name, ps, us) ->
      let ps', fresh_subst, p_map = Substitution.of_tydef_parameters ps in
      let us' =
        Type.Field.Map.map
          (Substitution.apply_substitutions_to_type fresh_subst)
          us
      in
      (apply_to_tydef_params ty_name ps' p_map, (ty_name, us'))

(** [extend_type_definitions tydefs state] checks that the simulatenous type definitions [tydefs] are
    well-formed and returns the extended type context. *)
let extend_type_definitions tydefs st =
  (* We wish we wrote this in eff, where we could have transactional memory. *)
  let extend_tydef name { params; type_def } st' =
    Assoc.update name { params; type_def } st'
  in
  Type.Field.Map.fold extend_tydef tydefs st
