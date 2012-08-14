type ty_scheme = (Type.ty_param list * Type.dirt_param list * Type.region_param list) * Type.ty
type t = (Common.variable, ty_scheme) Common.assoc

let empty = []

let lookup ctx x =
  match Common.lookup x ctx with
  | Some (ps, t) -> Some (snd (Type.refresh ps t))
  | None -> None

let extend ctx x ty_scheme = (x, ty_scheme) :: ctx

let extend_ty ctx x ty = (x, (([],[],[]), ty)) :: ctx

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty) =
    assert (List.for_all (fun (p, _) -> not (List.mem p (let ps,_,_= ps in ps))) sbst.Type.subst_ty);
    (ps, Type.subst_ty sbst ty)
  in
  Common.assoc_map subst_ty_scheme ctx

(* XXX belongs to Common, compare to diff3 in type.ml *)
let diff3 (xs, ys, zs) (us, vs, ws) =
  (Common.diff xs us, Common.diff ys vs, Common.diff zs ws)

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  (* Code repeats, compare to type.ml, Matija loves to clean up such things. *)
  let (@@@) (xs, ys, zs) (us, vs, ws) = (xs @ us, ys @ vs, zs @ ws) in
  let flatten_map f lst = List.fold_left (@@@) ([], [], []) (List.map f lst) in
  let binding_params (_, (ps, ty)) = diff3 (Type.free_params ty) ps in
  let (xs, ys, zs) = flatten_map binding_params ctx in
    (Common.uniq xs, Common.uniq ys, Common.uniq zs)

let generalize ctx poly ty =
  if poly then
    let ps = diff3 (Type.free_params ty) (free_params ctx) in
    (ps, ty)
  else
    (([],[],[]), ty)
