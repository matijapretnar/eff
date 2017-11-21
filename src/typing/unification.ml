(********************)
(* TYPE DEFINITIONS *)
(********************)

(* Typing constraint *)
type ty_cnstr = (Type.ty * Type.ty * Location.t)
(* Dirt constraint *)
type dirt_cnstr = (Type.dirt * Type.dirt * Location.t)

(* A constraint set *)
type t = {
  types : ty_cnstr list;
  dirts : dirt_cnstr list
}

(* represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) OldUtils.assoc

(***********************)
(* PRINTING OPERATIONS *)
(***********************)

(* Print constraints *)
let print constraints ppf =
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t %s %t)" (Type.print_ty x) (Symbols.less ()) (Type.print_ty y)) constraints.types ppf;
  Format.pp_print_string ppf " ; ";
  Print.sequence "," (fun (x, y, _) ppf -> Format.fprintf ppf "(%t %s %t)" (Type.print_dirt x) (Symbols.less ()) (Type.print_dirt y)) constraints.dirts ppf

(******************)
(* HELPER METHODS *)
(******************)

(* Add a type constraint to a constraint set *)
let add_type ty cnstr = {
  types = ty :: cnstr.types;
  dirts = cnstr.dirts
}

let add_dirt drt cnstr = {
  types = cnstr.types;
  dirts = drt :: cnstr.dirts
}

let combine_types types cnstr = List.fold_right add_type types cnstr

let combine_dirts types cnstr = List.fold_right add_dirt types cnstr

let subst_ty_cnstr sbst (ty1, ty2, loc) = (Type.subst_ty sbst ty1, Type.subst_ty sbst ty2, loc)

let subst_dirt_cnstr sbst (drt1, drt2, loc) = (Type.subst_dirt sbst drt1, Type.subst_dirt sbst drt2, loc)

(*************************)
(* CONSTRAINT OPERATIONS *)
(*************************)

(* The empty constraint set *)
let empty = {
  types = [];
  dirts = []
}

(* Add a type constraint to a constraint set *)
let add_ty_constraint ~loc ty1 ty2 cnstr = add_type (ty1, ty2, loc) cnstr

let add_dirt_constraint ~loc drt1 drt2 cnstr = add_dirt (drt1, drt2, loc) cnstr

let add_dirty_constraint ~loc (ty1, drt1) (ty2, drt2) cnstr = add_ty_constraint ~loc ty1 ty2 (add_dirt_constraint ~loc drt1 drt2 cnstr)

(* Combine two constraint sets to a single set *)
let union c1 c2 =
  let c' = combine_dirts c1.dirts c2 in
  let c'' = combine_types c1.types c' in
  c''

(* Combine mutliple constraint sets to a single set *)
let union_list c_list =
  List.fold_right union c_list empty

(* Perform a substitution *)
let subst sbst constraints =
  {types=List.map (subst_ty_cnstr sbst) constraints.types; dirts=List.map (subst_dirt_cnstr sbst) constraints.dirts }

let list_union = function
  | [] -> empty
  | [constraints] -> constraints
  | constraints :: constraints_lst -> List.fold_right union constraints_lst constraints

(************************************)
(* CONSTRAINT SUBSTITUTION POLARITY *)
(************************************)

(* replacement => match to correct type and polarity *)
type replacement = {
  ty_param_repl : Params.ty_param * bool -> Type.ty;
  dirt_param_repl : Params.dirt_param * bool -> Type.dirt;
}

let rec replace_dirt rpls polarity drt =
  begin match drt with
    | Type.Op _ -> drt
    | Type.DirtVar d -> (rpls.dirt_param_repl (d, polarity))
    | Type.DirtBottom -> Type.DirtBottom
    | Type.DirtUnion (d1, d2) -> Type.DirtUnion ((replace_dirt rpls polarity d1), (replace_dirt rpls polarity d2))
    | Type.DirtIntersection (d1, d2) -> Type.DirtIntersection ((replace_dirt rpls polarity d1), (replace_dirt rpls polarity d2))
  end

(** [replace_ty rpls ty] replaces type parameters in [ty] according to [rpls]. *)
let rec replace_ty rpls polarity ty =
  begin match ty with
    | Type.Apply (ty_name, args) -> Type.Apply (ty_name, replace_args rpls polarity args)
    | Type.TyVar p -> rpls.ty_param_repl (p, polarity)
    | Type.Prim _ as ty -> ty
    | Type.Tuple tys -> Type.Tuple (OldUtils.map (replace_ty rpls polarity) tys)
    | Type.Arrow (ty1, (ty2, drt)) ->
      let ty1 = replace_ty rpls (not polarity) ty1 in
      let drt = replace_dirt rpls polarity drt in
      let ty2 = replace_ty rpls polarity ty2 in
      Type.Arrow (ty1, (ty2, drt))
    | Type.Handler (drty1, drty2) ->
      let drty1 = replace_dirty rpls (not polarity) drty1 in
      let drty2 = replace_dirty rpls polarity drty2 in
      Type.Handler (drty1, drty2)
    | Type.Bottom when polarity == true -> Type.Bottom
    | Type.Top when polarity == false -> Type.Top
    | Type.Union (ty1, ty2) when polarity == true ->
      let ty1 = replace_ty rpls polarity ty1 in
      let ty2 = replace_ty rpls polarity ty2 in
      Type.Union (ty1, ty2)
    | Type.Intersection (ty1, ty2) when polarity == false ->
      let ty1 = replace_ty rpls polarity ty1 in
      let ty2 = replace_ty rpls polarity ty2 in
      Type.Intersection (ty1, ty2)
  end

(* and replace_dirt rpls polarity drt =
  let { Type.ops = new_ops; Type.rest = new_rest } = rpls.dirt_param_repl (drt.Type.rest, polarity) in
  { Type.ops = new_ops @ drt.ops; Type.rest = new_rest } *)

and replace_dirty rpls polarity (ty, drt) =
  let ty = replace_ty rpls polarity ty in
  let drt = replace_dirt rpls polarity drt in
  (ty, drt)

and replace_args rpls polarity (tys, drts) =
  let tys = OldUtils.map (replace_ty rpls polarity) tys in
  let drts = OldUtils.map (replace_dirt rpls polarity) drts in
  (tys, drts)
  
let subst_ty_cnstr_polar sbst (ty1, ty2, loc) = (replace_ty sbst true ty1, replace_ty sbst false ty2, loc)

let subst_dirt_cnstr_polar sbst (drt1, drt2, loc) = (replace_dirt sbst true drt1, replace_dirt sbst false drt2, loc)

let subst_polar sbst constraints =
  {types=List.map (subst_ty_cnstr_polar sbst) constraints.types; dirts=List.map (subst_dirt_cnstr_polar sbst) constraints.dirts }

let id_ty (p, polarity) = Type.TyVar p
let id_drt (d, polarity) = Type.simple_dirt d

let identity_subst = {
  ty_param_repl = (function (p, polarity) -> Type.TyVar p);
  dirt_param_repl = (function (d, polarity) -> Type.simple_dirt d);
}
(************************)
(* CONSTRAINT SOLUTIONS *)
(************************)

let constructed ty =
  begin match ty with
    | Type.Arrow _ -> true
    | Type.Handler _ -> true
    | Type.Apply _ -> true
    | Type.Prim _ -> true
    | Type.Tuple _ -> true
    | _ -> false
  end

let atomic_ty cnstr =
  begin match cnstr with
    | (Type.TyVar a, Type.TyVar b, _) -> 
      {
        ty_param_repl = (function (p, polarity) -> if (polarity == true && p == b) then Type.Union (Type.TyVar a, Type.TyVar b) else Type.TyVar p);
        dirt_param_repl = id_drt;
      }
    | (Type.TyVar a, ty, _) when constructed ty -> 
      {
        ty_param_repl = (function (p, polarity) -> if (polarity == false && p == a) then Type.Intersection (Type.TyVar a, ty) else Type.TyVar p);
        dirt_param_repl = id_drt;
      }
    | (ty, Type.TyVar b, _) when constructed ty -> 
      {
        ty_param_repl = (function (p, polarity) -> if (polarity == true && p == b) then Type.Union (Type.TyVar b, ty) else Type.TyVar p);
        dirt_param_repl = id_drt;
      }
    (* | _ -> false *)
  end

let is_atomic_ty el =
  begin match el with
    | (Type.TyVar a, Type.TyVar b, _) when a != b-> true
    | (Type.TyVar _, ty, _) when constructed ty -> true
    | (ty, Type.TyVar _, _) when constructed ty -> true
    | _ -> false
  end

let atomic_drt cnstr =
  begin match cnstr with
    | (Type.DirtVar a, Type.DirtVar b, _) -> 
      {
        ty_param_repl = id_ty;
        dirt_param_repl = (function (p, polarity) -> if (polarity == true && p == b) then Type.DirtUnion (Type.DirtVar a, Type.DirtVar b) else Type.DirtVar p);
      }
    | (Type.DirtVar a, ty, _) -> 
      {
        ty_param_repl = id_ty;
        dirt_param_repl = (function (p, polarity) -> if (polarity == false && p == a) then Type.DirtIntersection (Type.DirtVar a, ty) else Type.DirtVar p);
      }
    | (ty, Type.DirtVar b, _) -> 
      {
        ty_param_repl = id_ty;
        dirt_param_repl = (function (p, polarity) -> if (polarity == true && p == b) then Type.DirtUnion (Type.DirtVar b, ty) else Type.DirtVar p);
      }
    (* | _ -> false *)
  end

let is_atomic_drt el =
  begin match el with
    | (Type.DirtVar a, Type.DirtVar b, _) when a != b-> true
    | (Type.DirtVar _, Op _, _) -> true
    | (Op _, Type.DirtVar _, _) -> true
    | _ -> false
  end

(* Apply of OldUtils.tyname * args *)
(* RecType of Params.ty_param * ty *)
let decompose_ty_cnstr (ty1, ty2, loc) =
  begin match ty1, ty2 with
    | (ty1, ty2) when ty1 = ty2 -> empty

    | (Type.TyVar a, Type.TyVar b) when a = b -> empty

    | (Type.Tuple tys1, Type.Tuple tys2) when List.length tys1 = List.length tys2 ->
      let cnstr = List.fold_right2 (add_ty_constraint ~loc) tys1 tys2 empty in
      cnstr

    (* A -> B ! a = C -> D ! b translates into: A=C, B=D, a=b *)
    | (Type.Arrow (ty1_in, dirty1_out), Type.Arrow (ty2_in, dirty2_out)) ->
      let cnstr = add_ty_constraint ~loc ty1_in ty2_in empty in
      let cnstr = add_dirty_constraint ~loc dirty1_out dirty2_out cnstr in
      cnstr

    (* A ! a => B ! b = C ! c => D ! d translates into: A=C, B=D, a=c, b=d *)
    | (Type.Handler (dirty1_in, dirty1_out), Type.Handler (dirty2_in, dirty2_out)) ->
      let cnstr = add_dirty_constraint ~loc dirty1_in dirty2_in empty in
      let cnstr = add_dirty_constraint ~loc dirty1_out dirty2_out cnstr in
      cnstr

    | (Type.Union (ty_left, ty_right), ty2) ->
      let cnstr = add_ty_constraint ~loc ty_left ty2 empty in
      let cnstr = add_ty_constraint ~loc ty_right ty2 cnstr in
      cnstr
    
    | (ty1, Type.Intersection (ty_left, ty_right)) ->
      let cnstr = add_ty_constraint ~loc ty1 ty_left empty in
      let cnstr = add_ty_constraint ~loc ty1 ty_right cnstr in
      cnstr

    | (Type.Bottom, _) -> empty
    | (_, Type.Top) -> empty

    (* Primitives *)
    | (Type.Prim Type.BoolTy, Type.Prim Type.BoolTy) -> empty
    | (Type.Prim Type.IntTy, Type.Prim Type.IntTy) -> empty
    | (Type.Prim Type.FloatTy, Type.Prim Type.FloatTy) -> empty
    | (Type.Prim Type.StringTy, Type.Prim Type.StringTy) -> empty
    | (Type.Tuple [], Type.Tuple []) -> empty
    | (Type.Prim Type.UniTy, Type.Prim Type.UniTy) -> empty

    (* Constraints could not be unified *)
    | _ -> Error.typing ~loc "This expression has type %t but it should have type %t." (Type.print_ty ty1) (Type.print_ty ty2)
  end

let decompose_drt_cnstr (drt1, drt2, loc) = 
  begin match drt1, drt2 with
    | (Type.DirtVar a, Type.DirtVar b) when a = b -> empty
    | (Type.Op a, Type.Op b) when a = b -> empty

    | (Type.DirtBottom, _) -> empty
    (* | (_, Type.Top) -> empty *)

    | (Type.DirtUnion (drt_left, drt_right), drt2) ->
    let cnstr = add_dirt_constraint ~loc drt_left drt2 empty in
    let cnstr = add_dirt_constraint ~loc drt_right drt2 cnstr in
    cnstr
  
  | (drt1, Type.DirtIntersection (drt_left, drt_right)) ->
    let cnstr = add_dirt_constraint ~loc drt1 drt_left empty in
    let cnstr = add_dirt_constraint ~loc drt1 drt_right cnstr in
    cnstr
  end

let rec contains x = function
  | [] -> false
  | x' :: lst -> if (x = x') then true else contains x lst

let rec biunify_h ctx ty cnstr history =
  begin match cnstr with
    | {types = []; dirts = []} -> (ctx, ty, cnstr) (* EMPTY *)
    | {types = h :: tail; dirts = d} when contains h history.types ->  biunify_h ctx ty {types = tail; dirts = d} history (* REDUNDANT *)
    | {types = t; dirts = h :: tail} when contains h history.dirts -> biunify_h ctx ty {types = t; dirts = tail} history (* REDUNDANT *)
    | {types = h :: tail; dirts = d} when is_atomic_ty h -> 
      let sbst = atomic_ty h in
      let history = subst_polar sbst {history with types = h :: history.types} in
      let cnstr = subst_polar sbst {types = tail; dirts = d} in
      let ty = replace_ty sbst true ty in
      let ctx = OldUtils.assoc_map (replace_ty sbst false) ctx in
      biunify_h ctx ty cnstr history (* ATOMIC *)
    | {types = t; dirts = h :: tail} when is_atomic_drt h -> 
      let sbst = atomic_drt h in
      let history = subst_polar sbst {history with dirts = h :: history.dirts} in
      let cnstr = subst_polar sbst {types = t; dirts = tail} in
      let ty = replace_ty sbst true ty in
      let ctx = OldUtils.assoc_map (replace_ty sbst false) ctx in
      biunify_h ctx ty cnstr history (* ATOMIC *)
    | {types = h :: tail; dirts = d} -> 
      let history = {history with types = h :: history.types} in
      let cnstr = union (decompose_ty_cnstr h) {types = tail; dirts = d} in
      biunify_h ctx ty cnstr history (* DECOMPOSE *)
    | {types = t; dirts = h :: tail} -> 
      let history = {history with dirts = h :: history.dirts} in
      let cnstr = union (decompose_drt_cnstr h) {types = t; dirts = tail} in
      biunify_h ctx ty cnstr history  (* DECOMPOSE *)
  end

let rec biunify_h_dirty ctx dirty cnstr history =
  begin match cnstr with
    | {types = []; dirts = []} -> (ctx, dirty, cnstr) (* EMPTY *)
    | {types = h :: tail; dirts = d} when contains h history.types ->  biunify_h_dirty ctx dirty {types = tail; dirts = d} history (* REDUNDANT *)
    | {types = t; dirts = h :: tail} when contains h history.dirts -> biunify_h_dirty ctx dirty {types = t; dirts = tail} history (* REDUNDANT *)
    | {types = h :: tail; dirts = d} when is_atomic_ty h -> 
      let sbst = atomic_ty h in
      let history = subst_polar sbst {history with types = h :: history.types} in
      let cnstr = subst_polar sbst {types = tail; dirts = d} in
      let dirty = replace_dirty sbst true dirty in
      let ctx = OldUtils.assoc_map (replace_ty sbst false) ctx in
      biunify_h_dirty ctx dirty cnstr history (* ATOMIC *)
    | {types = t; dirts = h :: tail} when is_atomic_drt h -> 
      let sbst = atomic_drt h in
      let history = subst_polar sbst {history with dirts = h :: history.dirts} in
      let cnstr = subst_polar sbst {types = t; dirts = tail} in
      let dirty = replace_dirty sbst true dirty in
      let ctx = OldUtils.assoc_map (replace_ty sbst false) ctx in
      biunify_h_dirty ctx dirty cnstr history (* ATOMIC *)
    | {types = h :: tail; dirts = d} -> 
      let history = {history with types = h :: history.types} in
      let cnstr = union (decompose_ty_cnstr h) {types = tail; dirts = d} in
      biunify_h_dirty ctx dirty cnstr history (* DECOMPOSE *)
    | {types = t; dirts = h :: tail} -> 
      let history = {history with dirts = h :: history.dirts} in
      let cnstr = union (decompose_drt_cnstr h) {types = t; dirts = tail} in
      biunify_h_dirty ctx dirty cnstr history  (* DECOMPOSE *)
  end

(* START *)
let biunify ctx ty cnstr = biunify_h ctx ty cnstr empty

(* Unify the constraints to find a solution *)
let unify_ty ctx ty cnstr = 
  let ctx, ty, cnstr = biunify ctx ty cnstr in
  (ctx, ty, cnstr)

(* Unify the constraints to find a solution *)
let unify_dirty ctx (ty, drt) cnstr =
  let ctx, (ty, drt), cnstr = biunify_h_dirty ctx (ty, drt) cnstr empty in
  (* let ctx, (ty, drt), cnstr = unify_dirts ctx (ty, drt) cnstr in *)
  (ctx, (ty, drt), cnstr)
