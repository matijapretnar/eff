(** [unify sbst pos t1 t2] solves the equation [t1 = t2] and stores the
    solution in the substitution [sbst]. *)
let solve cstr =
  let sbst = ref Type.identity_subst in
  let rec unify pos t1 t2 =
    let t1 = Type.subst_ty !sbst t1 in
    let t2 = Type.subst_ty !sbst t2 in
    match t1, t2 with

    | (t1, t2) when t1 = t2 -> ()

    | (Type.TyParam p, t) | (t, Type.TyParam p) ->
        if Type.occurs_in_ty p t
        then
          let sbst = Type.beautify2 t1 t2 in
          Error.typing ~pos:pos
            "This expression has a forbidden cylclic type %t = %t."
            (Print.ty sbst ([], [], []) t1)
            (Print.ty sbst ([], [], []) t2)
        else
          sbst := Type.compose_subst {Type.identity_subst with Type.subst_ty = [(p, t)]} !sbst

    | (Type.Arrow (u1, (v1, _)), Type.Arrow (u2, (v2, _))) ->
        unify pos v1 v2;
        unify pos u2 u1

    | (Type.Tuple lst1, Type.Tuple lst2)
        when List.length lst1 = List.length lst2 ->
        List.iter2 (unify pos) lst1 lst2

    | (Type.Record lst1, Type.Record lst2) ->
        assert false

    | (Type.Sum lst1, Type.Sum lst2) ->
        assert false

    | (Type.Apply (t1, lst1), Type.Apply (t2, lst2))
        when t1 = t2 && List.length lst1 = List.length lst2  ->
        List.iter2 (unify pos) lst1 lst2

    (* The following two cases cannot be merged into one, as the whole matching
       fails if both types are Apply, but only the second one is transparent. *)
    | (Type.Apply (t1, lst1), t2) when Tctx.transparent ~pos:pos t1 ->
        unify pos t2 (Tctx.ty_apply ~pos:pos t1 lst1)

    | (t1, (Type.Apply _ as t2)) ->
        unify pos t2 t1

    | (Type.Handler h1, Type.Handler h2) ->
        unify pos h2.Type.value h1.Type.value;
        unify pos h1.Type.finally h2.Type.finally

    | (Type.Effect lst1, Type.Effect lst2) ->
        assert false

    | (t1, t2) ->
        let sbst = Type.beautify2 t1 t2 in
        Error.typing ~pos:pos
          "This expression has type %t but it should have type %t."
          (Print.ty sbst ([],[],[]) t1) (Print.ty sbst ([],[],[]) t2)
  in
  List.iter (fun (t1, t2, pos) -> unify pos t1 t2) (List.rev cstr);
  !sbst
