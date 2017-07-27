open Typed

let x = target_expression(Var "test", PrimTy Intty);;

type ('term, 'ttype) target_term = {
  term: 'term;
  target_type: 'ttype;
  location: Location.t;
};;


let const ?loc c =
  let loc = backup_location loc [] in
  let ty = match c with
    | Const.Integer _ -> Types.IntTy
    | Const.String _ -> Types.StringTy
    | Const.Boolean _ -> Types.BoolTy
    | Const.Float _ -> Types.Float_ty
  in
  {
    term = Const c;
    target_type = PrimTy ty;
    location = loc;
  }