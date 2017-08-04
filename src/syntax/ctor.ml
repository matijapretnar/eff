
(********************)
(* HELPER FUNCTIONS *)
(********************)

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc

(*********************************)
(* EXPRESSION SMART CONSTRUCTORS *)
(*********************************)

let const ?loc c =
  let loc = backup_location loc [] in
  let ty = match c with
    | Const.Integer _ -> Type.int_ty
    | Const.String _ -> Type.string_ty
    | Const.Boolean _ -> Type.bool_ty
    | Const.Float _ -> Type.float_ty
  in
  Typed.annotate (Typed.Const c) (Scheme.simple ty) loc


(**********************************)
(* COMPUTATION SMART CONSTRUCTORS *)
(**********************************)

let value ?loc e =
  let loc = backup_location loc [e.Typed.location] in
  let ctx, ty, constraints = e.Typed.scheme in
  Typed.annotate (Typed.Value e) (ctx, (ty, Type.fresh_dirt ()), constraints) loc

(******************************)
(* PATTERN SMART CONSTRUCTORS *)
(******************************)
