module TyParam = ConstraintsPoset.Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
end)

type t = TyParam.t

let empty  = TyParam.empty

(** Add an edge to the graph. *)
let add_edge = TyParam.add_edge

let skeletons = TyParam.skeletons

let get_prec = TyParam.get_prec

let map = TyParam.map

let garbage_collect = TyParam.garbage_collect

let remove_skeleton = TyParam.remove_skeleton

let union = TyParam.union
