(** Association lists *)
type ('key, 'value) t = ('key * 'value) list

let rec lookup x = function
  | [] -> None
  | (k, y) :: tl -> if x = k then Some y else lookup x tl

let rec remove x = function
  | [] -> []
  | (k, v) :: tl -> if x = k then tl else (k, v) :: remove x tl

let update k v assoc = (k, v) :: assoc

let rec map f = function
  | [] -> []
  | (k, v) :: tl ->
      let v' = f v in
      let tl' = map f tl in
      (k, v') :: tl'
