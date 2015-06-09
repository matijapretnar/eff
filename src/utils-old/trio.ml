type ('a, 'b, 'c) t = 'a list * 'b list * 'c list
let empty = ([], [], [])
let append (xs, ys, zs) (us, vs, ws) = (xs @ us, ys @ vs, zs @ ws)
let snds (xs, ys, zs) = (List.map snd xs, List.map snd ys, List.map snd zs)
let flatten_map f lst = List.fold_left append empty (List.map f lst)
let diff (xs, ys, zs) (us, vs, ws) = (Common.diff xs us, Common.diff ys vs, Common.diff zs ws)
let uniq (xs, ys, zs) = (Common.uniq xs, Common.uniq ys, Common.uniq zs)
