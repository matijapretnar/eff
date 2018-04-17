
(********************)
(* HELPER FUNCTIONS *)
(********************)

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc

(* [linear_record r] verifies that a record or a record pattern has linear field names. *)
let linear_record lst = OldUtils.injective fst lst

(**********************************)
(* ABSTRACTION SMART CONSTRUCTORS *)
(**********************************)

let abstraction ?loc p c : Typed.abstraction =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  {
    term = (p, c);
    scheme = Scheme.abstract ~loc p.scheme c.scheme;
    location = loc;
  }

let abstraction2 ?loc p1 p2 c : Typed.abstraction2 =
  let loc = backup_location loc [p1.Typed.location; p2.Typed.location; c.Typed.location] in
  {
    term = (p1, p2, c);
    scheme = Scheme.abstract2 ~loc p1.scheme p2.scheme c.scheme;
    location = loc;
  }

(*********************************)
(* EXPRESSION SMART CONSTRUCTORS *)
(*********************************)

let lambdavar ?loc x ty =
  let loc = backup_location loc [] in
  let sch = Scheme.var ~loc x ty in
  let term = Typed.LambdaVar x in
  Typed.annotate term sch loc

let letvar ?loc x sch =
  let loc = backup_location loc [] in
  let term = Typed.LetVar x in
  Typed.annotate term sch loc

let const ?loc c =
  let loc = backup_location loc [] in
  let term = Typed.Const c in
  let sch = Scheme.const ~loc c in
  Typed.annotate term sch loc

let record ?loc lst =
  let loc = backup_location loc (List.map (fun (_, e) -> e.Typed.location) lst) in
  match lst with
  | [] -> assert false
  | ((fld, _) :: _) as lst ->
    if not (linear_record lst) then
      Error.typing ~loc "Fields in a record must be distinct";
    begin match Tctx.infer_field fld with
      | None -> Error.typing ~loc "Unbound record field label %s" fld
      | Some (ty, (ty_name, fld_tys)) ->
        if List.length lst <> List.length fld_tys then
          Error.typing ~loc "The record of type %s has an incorrect number of fields" ty_name;
        let infer (fld, e) (ctx, constraints) =
          begin match OldUtils.lookup fld fld_tys with
            | None -> Error.typing ~loc "Unexpected field %s in a record of type %s" fld ty_name
            | Some fld_ty ->
              let e_ctx, e_ty, e_constraints = e.Typed.scheme in
              e_ctx @ ctx, Unification.add_ty_constraint ~loc e_ty fld_ty constraints
          end
        in
        let ctx, constraints = List.fold_right infer lst ([], Unification.empty) in
        let sch = Scheme.solve_ty (ctx, ty, constraints) in
        let term = Typed.Record lst in
        Typed.annotate term sch loc
    end

let variant ?loc (lbl, e) =
  let loc = backup_location loc (match e with None -> [] | Some e -> [e.Typed.location]) in
  begin match Tctx.infer_variant lbl with
    | None -> Error.typing ~loc "Unbound constructor %s" lbl
    | Some (ty, arg_ty) ->
      let sch = begin match e, arg_ty with
        | None, None -> ([], ty, Unification.empty)
        | Some e, Some arg_ty ->
          let e_ctx, e_ty, e_constraints = e.Typed.scheme in
          let constraints = Unification.add_ty_constraint ~loc e_ty arg_ty e_constraints in
          Scheme.solve_ty (e_ctx, ty, constraints)
        | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
        | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
      end
      in
      let term = Typed.Variant (lbl, e) in
      Typed.annotate term sch loc
  end

let lambda ?loc p c =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  let term = Typed.Lambda (p, c) in
  let sch = Scheme.lambda ~loc p.Typed.scheme c.Typed.scheme in
  Typed.annotate term sch loc

let tuple ?loc es =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) es) in
  let term = Typed.Tuple es in
  let sch = Scheme.tuple ~loc (List.map (fun e -> e.Typed.scheme) es) in
  Typed.annotate term sch loc

let effect ?loc ((eff_name, (ty_par, ty_res)) as eff) =
  let loc = backup_location loc [] in
  let sch = Scheme.effect ~loc ty_par ty_res eff_name in
  let term = Typed.Effect eff in
  Typed.annotate term sch loc

let handler ?loc effect_clauses value_clause =
  let loc = backup_location loc (value_clause.Typed.location :: (List.map (fun (_, e) -> e.Typed.location) effect_clauses)) in
  let term = Typed.Handler {
    effect_clauses=effect_clauses;
    value_clause=value_clause
  } in
  let sch = Scheme.handler ~loc (List.map (fun (eff, e) -> (eff, e.Typed.scheme)) effect_clauses) value_clause.Typed.scheme in
  Typed.annotate term sch loc

(**********************************)
(* COMPUTATION SMART CONSTRUCTORS *)
(**********************************)

let value ?loc e =
  let loc = backup_location loc [e.Typed.location] in
  let term = Typed.Value e in
  let sch = Scheme.value ~loc e.Typed.scheme in
  Typed.annotate term sch loc

let patmatch ?loc es cases =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) cases) in
  let term = Typed.Match (es, cases) in
  let sch = Scheme.patmatch ~loc es.Typed.scheme (List.map (fun e -> e.Typed.scheme) cases) in
  Typed.annotate term sch loc

let apply ?loc e1 e2 =
  let loc = backup_location loc [e1.Typed.location; e2.Typed.location] in
  let term = Typed.Apply (e1, e2) in
  let sch = Scheme.apply ~loc e1.Typed.scheme e2.Typed.scheme in
  Typed.annotate term sch loc

let handle ?loc e c =
  let loc = backup_location loc [e.Typed.location; c.Typed.location] in
  let sch = Scheme.handle ~loc e.Typed.scheme c.Typed.scheme in
  let term = Typed.Handle (e, c) in
  Typed.annotate term sch loc

let letrecbinding ?loc defs c =
  let loc = backup_location loc (
    c.Typed.location :: List.map (fun (_, a) -> a.Typed.location) defs
  ) in
  let term = Typed.LetRec (defs, c) in
  (* let defs, poly_tyschs, change = let_rec_defs ~loc defs in *)
  let sch = Scheme.letrecbinding ~loc c.Typed.scheme in
  Typed.annotate term sch loc

let bind ?loc c1 c2 =
  let loc = backup_location loc [c1.Typed.location; c2.Typed.location] in
  let sch = Scheme.letbinding ~loc c1.Typed.scheme c2.Typed.scheme in
  let term = Typed.Bind (c1, c2) in
  Typed.annotate term sch loc

let let_in ?loc e1 c2 =
  let loc = backup_location loc [] in
  bind ~loc (value ~loc e1) c2

let letbinding ?loc defs c =
  let loc = backup_location loc [] in
  List.fold_right (fun (p_def, c_def) binds ->
    match c_def.Typed.term with
    | Typed.Value e_def -> let_in ~loc e_def (abstraction ~loc p_def binds)
    | _ ->  bind ~loc c_def (abstraction ~loc p_def binds)
  ) defs c

(******************************)
(* PATTERN SMART CONSTRUCTORS *)
(******************************)

let pvar ?loc x =
  let loc = backup_location loc [] in
  let sch = Scheme.pvar ~loc x in
  let pattern = Typed.PVar x in
  Typed.annotate pattern sch loc

let pnonbinding ?loc =
  let loc = backup_location loc [] in
  let sch = Scheme.pnonbinding ~loc () in
  let pat = Typed.PNonbinding in
  Typed.annotate pat sch loc

let pconst ?loc const =
  let loc = backup_location loc [] in
  let sch = Scheme.pconst ~loc const in
  let pat = Typed.PConst const in
  Typed.annotate pat sch loc

let pas ?loc p x =
  let loc = backup_location loc [p.Typed.location] in
  let pat = Typed.PAs (p, x) in
  let sch = Scheme.pas ~loc p.Typed.scheme x in
  Typed.annotate pat sch loc

let ptuple ?loc ps =
  let loc = backup_location loc (List.map (fun p -> p.Typed.location) ps) in
  let sch = Scheme.ptuple ~loc (List.map (fun e -> e.Typed.scheme) ps) in
  let pat = Typed.PTuple ps in
  Typed.annotate pat sch loc

let precord ?loc fld lst =
  let loc = backup_location loc [] in
  begin match Tctx.infer_field fld with
    | None -> Error.typing ~loc "Unbound record field label %s" fld
    | Some (ty, (ty_name, fld_tys)) ->
      let infer (fld, p) (ctx, chngs) =
        begin match OldUtils.lookup fld fld_tys with
          | None -> Error.typing ~loc "Unexpected field %s in a pattern of type %s" fld ty_name
          | Some fld_ty ->
            let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
            ctx_p @ ctx, [
              Scheme.ty_cnstr ~loc fld_ty ty_p;
              Scheme.just cnstrs_p
            ] @ chngs
        end
      in
      let ctx, chngs = List.fold_right infer lst ([], []) in
      let sch = Scheme.precord ~loc ctx ty chngs in
      let pat = Typed.PRecord lst in
      Typed.annotate pat sch loc
  end

let pvariant_none ?loc lbl ty =
  let loc = backup_location loc [] in
  Typed.annotate (Typed.PVariant (lbl, None)) (Scheme.simple ty) loc

let pvariant_some ?loc lbl arg_ty ty p =
  let loc = backup_location loc [] in
  let ctx_p, ty_p, cnstrs_p = p.Typed.scheme in
  let chngs = [
    Scheme.ty_cnstr ~loc arg_ty ty_p;
    Scheme.just cnstrs_p
  ] in
  let sch = Scheme.precord ~loc ctx_p ty chngs in
  let pat = Typed.PVariant (lbl, Some p) in
  Typed.annotate pat sch loc
