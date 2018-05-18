(** Association lists *)
type ('key, 'value) t = ('key * 'value) list

let rec empty = []

(* Finding elements. *)
let rec lookup x = function
  | [] -> None
  | (k, v) :: tl -> if x = k then Some v else lookup x tl

let rec find_if p = function
  | [] -> None
  | hd :: tl -> if p hd then Some hd else find_if p tl

let pop = function
  | [] -> (None, [])
  | hd :: tl -> (Some hd, tl)

(* Changing the list. *)
let update k v assoc = (k, v) :: assoc

let rec replace k v = function
| [] -> []
| (k', v') :: tl -> if k = k' then (k, v) :: tl else (k', v') :: replace k v tl

let rec remove x = function
  | [] -> []
  | (k, v) :: tl -> if x = k then tl else (k, v) :: remove x tl

(* Iters, maps, folds. *)
let rec iter = List.iter

let rec map f = function
  | [] -> []
  | (k, v) :: tl ->
      let v' = f v in
      let tl' = map f tl in
      (k, v') :: tl'

let rec kmap f = function
  | [] -> []
  | hd :: tl ->
      let hd' = f hd in
      let tl' = kmap f tl in
      hd' :: tl'

let rec map_of_list f = function
  | [] -> []
  | x :: tl ->
      let k, v = f x in
      let tl' = map_of_list f tl in
      (k, v) :: tl'

let fold_left = CoreUtils.fold

let fold_right = List.fold_right

let fold_map = CoreUtils.fold_map



(* Other useful stuff. *)
let length assoc = List.length assoc

let rec values_of = function
  | [] -> []
  | (k, v) :: tl -> v :: values_of tl

let rec keys_of = function
  | [] -> []
  | (k, v) :: tl -> k :: keys_of tl

let rev = List.rev

let concat assoc1 assoc2 = assoc1 @ assoc2

(* Type casting *)
let of_list lst = lst

let to_list assoc = assoc
