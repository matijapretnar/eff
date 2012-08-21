type ty_scheme = Type.params * Type.ty * Type.constraints list
type t = (Common.variable, ty_scheme) Common.assoc

let empty = []

let lookup ctx x =
  match Common.lookup x ctx with
  | None -> None
  | Some (ps, ty, cstrs) -> Some (Type.refresh ps ty cstrs)

let extend ctx x ty_scheme = (x, ty_scheme) :: ctx

let extend_ty ctx x ty = (x, (([],[],[]), ty, [])) :: ctx

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty, cstrs) =
   assert (List.for_all (fun (p, _) -> not (List.mem p (let ps,_,_= ps in ps))) sbst.Type.subst_ty);
    (ps, Type.subst_ty sbst ty, Type.subst_constraints sbst cstrs)
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
  let binding_params (_, (ps, ty, cstrs)) = diff3 (Type.free_params ty cstrs) ps in
  let (xs, ys, zs) = flatten_map binding_params ctx in
    (Common.uniq xs, Common.uniq ys, Common.uniq zs)

let generalize ctx poly ty cstrs =
  if poly then
    let ps = diff3 (Type.free_params ty cstrs) (free_params ctx) in
    (ps, ty, cstrs)
  else
    (([],[],[]), ty, cstrs)
