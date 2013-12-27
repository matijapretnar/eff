module TyParam = ConstraintsPoset.Make(struct
  type t = Type.ty_param
  let compare = Pervasives.compare
end)

type t = TyParam.t

let empty  = TyParam.empty

(** Add an edge to the graph. *)
let add_edge = TyParam.add_edge

let get_prec = TyParam.get_prec

let map = TyParam.map

let garbage_collect = TyParam.garbage_collect

let remove_skeleton = TyParam.remove_skeleton

let union = TyParam.union

let skeletons cnstrs =
  let skeletons = TyParam.skeletons cnstrs in
  let rec missing misses expect = function
  | [] -> misses
  | x :: xs ->
    let (Type.Ty_Param y) = x in
    if y < expect then
      missing misses expect xs
    else if y = expect then
      missing misses (succ expect) xs
    else (* y > expect *)
      missing (expect :: misses) (succ expect) (x :: xs)
  in
  let misses = missing [] 0 (List.sort Pervasives.compare (List.flatten skeletons)) in
  let skeletons = List.map (fun x -> [Type.Ty_Param x]) misses @ skeletons in
  let skeletons = List.sort Pervasives.compare (List.map (List.sort Pervasives.compare) skeletons) in
  skeletons

