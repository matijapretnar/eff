include Stdlib.List

let fold = Stdlib.List.fold_left

let fold_map f s xs =
  let aux (s, reversed_ys) x =
    let s', y = f s x in
    (s', y :: reversed_ys)
  in
  let s', reversed_ys = fold aux (s, []) xs in
  (s', Stdlib.List.rev reversed_ys)

let rec left_to_right_map f = function
  | [] -> []
  | x :: xs ->
      let y = f x in
      let ys = left_to_right_map f xs in
      y :: ys

let unique_elements lst =
  let rec unique_elements acc = function
    | [] -> Stdlib.List.rev acc
    | x :: xs ->
        if Stdlib.List.mem x acc then unique_elements acc xs
        else unique_elements (x :: acc) xs
  in
  unique_elements [] lst

let no_duplicates lst =
  let rec check seen = function
    | [] -> true
    | x :: xs -> (not (Stdlib.List.mem x seen)) && check (x :: seen) xs
  in
  check [] lst

let list_diff lst1 lst2 =
  Stdlib.List.filter (fun x -> not (Stdlib.List.mem x lst2)) lst1

let concat_map f lst = Stdlib.List.concat (Stdlib.List.map f lst)
