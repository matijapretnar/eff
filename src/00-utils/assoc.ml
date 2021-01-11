type ('key, 'value) t = ('key * 'value) list
(** Association lists *)

let empty = []

(* Finding elements. *)
let rec lookup x = function
  | [] -> None
  | (k, v) :: tl -> if x = k then Some v else lookup x tl

let rec find_if p = function
  | [] -> None
  | hd :: tl -> if p hd then Some hd else find_if p tl

let pop = function [] -> None | hd :: tl -> Some (hd, tl)

(* Changing the list. *)
let update k v assoc = (k, v) :: assoc

let rec replace k v = function
  | [] -> []
  | (k', v') :: tl ->
      if k = k' then (k, v) :: tl else (k', v') :: replace k v tl

let rec remove x = function
  | [] -> []
  | (k, v) :: tl -> if x = k then tl else (k, v) :: remove x tl

(* Iters, maps, folds. *)
let iter = List.iter

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

let fold_map f st assoc =
  let aux (st, reversed_assoc) (k, v) =
    let st', v' = f st v in
    (st', (k, v') :: reversed_assoc)
  in
  let st', reversed_assoc = fold_left aux (st, []) assoc in
  (st', List.rev reversed_assoc)

let kfold_map f st xs =
  let aux (st, reversed_ys) x =
    let st', y = f st x in
    (st', y :: reversed_ys)
  in
  let st', reversed_ys = fold_left aux (st, []) xs in
  (st', List.rev reversed_ys)

(* Other useful stuff. *)
let length assoc = List.length assoc

let rec values_of = function [] -> [] | (_k, v) :: tl -> v :: values_of tl

let rec keys_of = function [] -> [] | (k, _v) :: tl -> k :: keys_of tl

let rev = List.rev

let concat assoc1 assoc2 = assoc1 @ assoc2

(* Type casting *)
let of_list lst = lst

let to_list assoc = assoc
