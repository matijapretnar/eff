type ty_scheme = Type.params * Type.ty * Type.constraints list
type t = (int, ty_scheme) Common.assoc

let empty = []

let lookup ctx x =
  match Common.lookup x ctx with
  | None -> None
  | Some (ps, ty, cstrs) -> Some (Type.refresh ps ty cstrs)

let extend ctx x ty_scheme = (x, ty_scheme) :: ctx

let extend_ty ctx x ty = (x, (Trio.empty, ty, [])) :: ctx

let subst_ctx ctx sbst =
  let subst_ty_scheme (ps, ty, cstrs) =
   assert (List.for_all (fun (p, _) -> not (List.mem p (let ps,_,_= ps in ps))) sbst.Type.subst_ty);
    (ps, Type.subst_ty sbst ty, Type.subst_constraints sbst cstrs)
  in
  Common.assoc_map subst_ty_scheme ctx

(** [free_params ctx] returns a list of all free type parameters in [ctx]. *)
let free_params ctx =
  (* Code repeats, compare to type.ml, Matija loves to clean up such things. *)
  let binding_params (_, (ps, ty, cstrs)) = Trio.diff (Type.free_params ty cstrs) ps in
  Trio.uniq (Trio.flatten_map binding_params ctx)

let generalize ctx poly ty cstrs =
  if poly then
    let ps = Trio.diff (Type.free_params ty cstrs) (free_params ctx) in
    (ps, ty, cstrs)
  else
    (Trio.empty, ty, cstrs)
