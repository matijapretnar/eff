module DirtPoset = ConstraintsPoset.Make(struct
  type t = Type.dirt_param
  let compare = Pervasives.compare
end)

type t = DirtPoset.t

let empty  = DirtPoset.empty

(** Add an edge to the graph. *)
let add_edge = DirtPoset.add_edge

let skeletons = DirtPoset.skeletons

let get_prec = DirtPoset.get_prec

let map = DirtPoset.map

let garbage_collect = DirtPoset.garbage_collect

let remove_skeleton = DirtPoset.remove_skeleton

let union = DirtPoset.union
