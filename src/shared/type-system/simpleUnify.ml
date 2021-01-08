open Utils
open Language

(** [unify sbst loc t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)
let solve cstr type_context =
  let rec unify loc t1 t2 subst =
    let t1 = Type.subst_ty subst t1 in
    let t2 = Type.subst_ty subst t2 in
    match (t1, t2) with
    | t1, t2 when t1 = t2 -> subst
    | Type.TyParam p, t | t, Type.TyParam p ->
        if Type.occurs_in_ty p t then
          let t1, t2 = Type.beautify2 t1 t2 in
          Error.typing ~loc
            "This expression has a forbidden cyclic type %t = %t."
            (Type.print t1) (Type.print t2)
        else Type.compose_subst (Assoc.update p t Assoc.empty) subst
    | Type.Arrow (u1, v1), Type.Arrow (u2, v2) ->
        subst |> unify loc v1 v2 |> unify loc u2 u1
    | Type.Tuple lst1, Type.Tuple lst2 when List.length lst1 = List.length lst2
      ->
        List.fold_left2
          (fun subst' t1' t2' -> unify loc t1' t2' subst')
          subst lst1 lst2
    | Type.Apply (t1, lst1), Type.Apply (t2, lst2)
      when t1 = t2 && List.length lst1 = List.length lst2 ->
        List.fold_left2
          (fun subst' t1' t2' -> unify loc t1' t2' subst')
          subst lst1 lst2
    (* The following two cases cannot be merged into one, as the whole matching
       fails if both types are Apply, but only the second one is transparent. *)
    | Type.Apply (t1, lst1), t2
      when TypeContext.transparent ~loc t1 type_context -> (
        match TypeContext.ty_apply ~loc t1 lst1 type_context with
        | TypeContext.Inline t -> unify loc t2 t subst
        | TypeContext.Sum _ | TypeContext.Record _ ->
            assert false (* None of these are transparent *))
    | t1, (Type.Apply _ as t2) -> unify loc t2 t1 subst
    | Type.Handler h1, Type.Handler h2 ->
        subst
        |> unify loc h2.Type.value h1.Type.value
        |> unify loc h1.Type.finally h2.Type.finally
    | t1, t2 ->
        let t1, t2 = Type.beautify2 t1 t2 in
        Error.typing ~loc
          "This expression has type %t but it should have type %t."
          (Type.print t1) (Type.print t2)
  in
  List.fold_right
    (fun (t1, t2, loc) -> unify loc t1 t2)
    cstr Type.identity_subst
