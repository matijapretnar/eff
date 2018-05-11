let fold = List.fold_left

let fold_map f s xs =
  let aux (s, reversed_ys) x =
    let s', y = f s x in
    (s', y :: reversed_ys)
  in
  let s', reversed_ys = fold aux (s, []) xs in
  (s', List.rev reversed_ys)
