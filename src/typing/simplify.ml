
(* represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) OldUtils.assoc

let rec encode_drt drt polarity automat =
  begin match drt with
    | Type.Op eff ->
      Automata.add_final_transition_drt (Automata.Op (eff, polarity)) automat
    | Type.DirtVar p ->
      Automata.add_final_transition_drt (Automata.DirtVar (p, polarity)) automat
    | Type.DirtBottom -> 
      automat
    | Type.DirtTop -> 
      automat
    | DirtUnion (drt1, drt2) ->
      let automat = encode_drt drt1 polarity automat in
      let automat = encode_drt drt2 polarity automat in
      automat
    | DirtIntersection (drt1, drt2) ->
      let automat = encode_drt drt1 polarity automat in
      let automat = encode_drt drt2 polarity automat in
      automat
  end

let rec encode ty polarity automat =
  begin match ty with
    | Type.Apply (ty_name, args) -> 
      assert false
    | Type.TyVar p -> 
      Automata.add_final_transition (Automata.Alpha (p, polarity)) automat
    | Type.Prim p ->
      Automata.add_final_transition (Automata.Prim (p, polarity)) automat
    | Type.Tuple tys -> 
      assert false
    | Type.Arrow (ty1, (ty2, drt)) ->
      let state = Automata.get_current_state automat in
      let automat = Automata.add_new_transition (Automata.Domain polarity) automat in
      let automat = encode ty1 (not polarity) automat in
      let automat = Automata.set_current_state state automat in
      let automat = Automata.add_new_transition (Automata.Range polarity) automat in
      let automat = encode ty2 polarity automat in
      let automat = Automata.set_current_state state automat in
      let automat = encode_drt drt polarity automat in
      let automat = Automata.add_final_transition (Automata.Function polarity) automat in
      automat
    | Type.Handler ((ty1, drt1), (ty2, drt2)) ->
      let state = Automata.get_current_state automat in
      let automat = Automata.add_new_transition (Automata.Domain polarity) automat in
      let automat = encode ty1 (not polarity) automat in
      let automat = Automata.set_current_state state automat in
      let automat = encode_drt drt1 polarity automat in
      let automat = Automata.add_new_transition (Automata.Range polarity) automat in
      let automat = encode ty2 polarity automat in
      let automat = Automata.set_current_state state automat in
      let automat = encode_drt drt2 polarity automat in
      let automat = Automata.add_final_transition (Automata.Handler polarity) automat in
      automat
    | Type.Bottom -> 
      Automata.undo_last_change automat
    | Type.Top -> 
      Automata.undo_last_change automat
    | Type.Union (ty1, ty2) ->
      let automat = encode ty1 polarity automat in
      let automat = encode ty2 polarity automat in
      automat
    | Type.Intersection (ty1, ty2) ->
      let automat = encode ty1 polarity automat in
      let automat = encode ty2 polarity automat in
      automat
  end

let rec replace_dirt rpls polarity drt =
  begin match drt with
    | Type.Op _ -> drt
    | Type.DirtVar _ -> drt
    | Type.DirtBottom -> Type.DirtBottom
    | Type.DirtUnion (d1, d2) -> Type.DirtUnion ((replace_dirt rpls polarity d1), (replace_dirt rpls polarity d2))
    | Type.DirtIntersection (d1, d2) -> Type.DirtIntersection ((replace_dirt rpls polarity d1), (replace_dirt rpls polarity d2))
    | Type.XContextDirt -> rpls
  end

(** [replace_ty rpls ty] replaces type parameters in [ty] according to [rpls]. *)
let rec replace_ty rpls polarity ty =
  begin match ty with
    | Type.Apply (ty_name, args) -> Type.Apply (ty_name, replace_args rpls polarity args)
    | Type.TyVar _ as ty -> ty
    | Type.Prim _ as ty -> ty
    | Type.Tuple tys -> Type.Tuple (OldUtils.map (replace_ty rpls polarity) tys)
    | Type.Arrow (ty1, drty2) ->
      let ty1 = replace_ty rpls (not polarity) ty1 in
      let drty2 = replace_dirty rpls polarity drty2 in
      Type.Arrow (ty1, drty2)
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
    | Type.XContext -> rpls
  end

and replace_dirty rpls polarity (ty, drt) =
  let ty = replace_ty rpls polarity ty in
  (* let drt = replace_dirt rpls polarity drt in *)
  (ty, drt)

and replace_args rpls polarity (tys, drts) =
  let tys = OldUtils.map (replace_ty rpls polarity) tys in
  (* let drts = OldUtils.map (replace_dirt rpls polarity) drts in *)
  (tys, drts)

let meet (left1, left2) (right1, right2) =
  (Type.Union (left1, right1), Type.Intersection (left2, right2))

let dirtmeet (left1, left2) (right1, right2) =
  (Type.DirtUnion (left1, right1), Type.DirtIntersection (left2, right2))

let composition (left1, left2) (right1, right2) =
  begin match right1, right2 with
    | Type.Bottom, Type.Top -> (Type.Bottom, Type.Top)
    | _ -> (left1, left2) (* Check polarity and change the XContext *)
  end

let dirtcomposition (left1, left2) (right1, right2) =
  begin match right1, right2 with
    | Type.DirtBottom, Type.DirtTop -> (Type.DirtBottom, Type.DirtTop)
    | _ -> (left1, left2) (* Check polarity and change the XContext *)
  end

let decode_alphabet_drt enc = 
  begin match enc with
    | Automata.Op (eff, b) ->
      if b then
        (Type.Op eff, Type.DirtTop)
      else
        (Type.DirtBottom, Type.Op eff)
    | Automata.DirtVar (drt, b) ->
      if b then
        (Type.DirtVar drt, Type.DirtTop)
      else
        (Type.DirtBottom, Type.DirtVar drt)
  end

let decode_alphabet enc =
  begin match enc with
    | Automata.Prim (a, b) ->
      if b then
        (Type.Prim a, Type.Top)
      else
        (Type.Bottom, Type.Prim a)
    | Automata.Function b ->
      if b then
        (Type.Arrow (Type.Top, (Type.Bottom, Type.DirtBottom)), Type.Top)
      else
        (Type.Bottom, Type.Arrow (Type.Bottom, (Type.Top, Type.DirtTop)))
    | Automata.Handler b -> 
      if b then
        (Type.Handler ((Type.Top, Type.DirtTop), (Type.Bottom, Type.DirtBottom)), Type.Top)
      else
        (Type.Bottom, Type.Handler ((Type.Bottom, Type.DirtBottom), (Type.Top, Type.DirtTop)))
    | Automata.Alpha (a, b) ->
      if b then
        (Type.TyVar a, Type.Top)
      else
        (Type.Bottom, Type.TyVar a)
    | Automata.Domain b ->
      if b then 
        (Type.Arrow (Type.XContext, (Type.Bottom, Type.DirtBottom)), Type.Top)
      else
        (Type.Bottom, Type.Arrow (Type.XContext, (Type.Top, Type.DirtTop)))
    | Automata.Range b -> 
      if b then 
        (Type.Arrow (Type.Top, (Type.XContext, Type.XContextDirt)), Type.Top)
      else
        (Type.Bottom, Type.Arrow (Type.Bottom, (Type.XContext, Type.XContextDirt)))
  end

let decode automat = automat

let simplify_ty ctx ty =
  (* Automata.printAuto (encode ty true Automata.empty); *)
  (ctx, ty)

let simplify_dirty ctx dirty = (ctx, dirty)