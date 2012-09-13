module Ty :
  sig
    type elt = Type.ty_param
    type t
  end
module Region :
  sig
    type elt = Type.region
    type t
  end
module Dirt :
  sig
    type elt = Type.dirt
    type t
  end
type t = {
  mutable ty_graph : Ty.t;
  mutable region_graph : Region.t;
  mutable dirt_graph : Dirt.t;
}
val empty : unit -> t
val add_ty_edge : t -> Ty.elt -> Ty.elt -> Common.position -> unit
val add_region_edge :
  t -> Region.elt -> Region.elt -> Common.position -> unit
val add_dirt_edge : t -> Dirt.elt -> Dirt.elt -> Common.position -> unit
val remove_ty :
  t ->
  Ty.elt -> (Ty.elt * Common.position) list * (Ty.elt * Common.position) list
val fold_ty :
  (Ty.elt -> Ty.elt -> Common.position -> 'a -> 'a) -> t -> 'a -> 'a
val fold_region :
  (Region.elt -> Region.elt -> Common.position -> 'a -> 'a) -> t -> 'a -> 'a
val fold_dirt :
  (Dirt.elt -> Dirt.elt -> Common.position -> 'a -> 'a) -> t -> 'a -> 'a
val print : t -> Format.formatter -> unit
val garbage_collect :
  (Ty.elt -> Ty.elt -> Common.position -> bool) ->
  (Dirt.elt -> Dirt.elt -> Common.position -> bool) ->
  (Region.elt -> Region.elt -> Common.position -> bool) -> t -> t
