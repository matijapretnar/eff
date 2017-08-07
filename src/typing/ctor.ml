
(********************)
(* HELPER FUNCTIONS *)
(********************)

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc

(* TEMPORARY *)
let abstraction ?loc p c : Typed.abstraction =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  {
    term = (p, c);
    scheme = Scheme.abstract ~loc p.scheme c.scheme;
    location = loc;
  }

(*********************************)
(* EXPRESSION SMART CONSTRUCTORS *)
(*********************************)

let var ?loc x ty_sch =
  let loc = backup_location loc [] in
  Typed.annotate (Typed.Var x) ty_sch loc

let const ?loc c =
  let loc = backup_location loc [] in
  let ty = match c with
    | Const.Integer _ -> Type.int_ty
    | Const.String _ -> Type.string_ty
    | Const.Boolean _ -> Type.bool_ty
    | Const.Float _ -> Type.float_ty
  in
  Typed.annotate (Typed.Const c) (Scheme.simple ty) loc

let lambda ?loc p c =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  let param_ty = Scheme.get_type p.Typed.scheme in
  let term = Typed.Lambda (p, param_ty, c) in
  let sch = Scheme.lambda ~loc p.Typed.scheme c.Typed.scheme in
  Typed.annotate term sch loc

(**********************************)
(* COMPUTATION SMART CONSTRUCTORS *)
(**********************************)

let value ?loc e =
  let loc = backup_location loc [e.Typed.location] in
  Typed.annotate (Typed.Value e) (Scheme.make_dirty e.Typed.scheme) loc

let apply ?loc e1 e2 =
  let loc = backup_location loc [e1.Typed.location; e2.Typed.location] in
  let ctx_e1, ty_e1, cnstrs_e1 = e1.Typed.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.Typed.scheme in
  let drty = Type.fresh_dirty () in
  let constraints = Unification.union cnstrs_e1 cnstrs_e2  in
  let constraints = Unification.add_ty_constraint ty_e1 (Type.Arrow (ty_e2, drty)) constraints in
  let drty_sch = (ctx_e1 @ ctx_e2, drty, constraints) in
  Typed.annotate (Typed.Apply (e1, e2)) drty_sch loc

(******************************)
(* PATTERN SMART CONSTRUCTORS *)
(******************************)

let pvar ?loc x =
  let loc = backup_location loc [] in
  let ty = Type.fresh_ty () in
  let scheme = Scheme.simple ty in
  let scheme = Scheme.add_to_context x ty scheme in
  let pattern = Typed.PVar x in
  Typed.annotate pattern scheme loc
