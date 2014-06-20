(* This file is based on Jean-Christophe Filliatre's implementation of
   Garsia-Wachs algorithm. Some changes have been made to make the file
   compatible with Eff. *)

let map = List.map


(* Identical code from here on *)

type 'a tree =
  | Leaf of 'a
  | Node of 'a tree * 'a tree

let phase1 l =
  let rec extract before = function
    | [t,_] ->
        t
    | [t1,w1; t2,w2] ->
        insert [] (Node (t1, t2), w1 + w2) before
    | (t1, w1) :: ((t2, w2) :: ((_, w3) :: _ as after) as r) ->
        if w1 <= w3 then
            insert after (Node (t1, t2), w1 + w2) before
        else
            extract ((t1, w1) :: before) r
  and insert after ((_,wt) as t) = function
    | [] -> 
        extract [] (t :: after)
    | ((_, wj_1) as tj_1) :: before ->
        if wj_1 >= wt then
            begin match before with
          | [] -> extract [] (tj_1 :: t :: after)
          | tj_2 :: before -> extract before (tj_2 :: tj_1 :: t :: after)
        end
    else
        insert (tj_1 :: after) t before
  in
  extract [] l

let rec mark d = function
  | Leaf (x, dx) -> dx := d
  | Node (l, r) -> mark (d + 1) l; mark (d + 1) r

let rec build d = function
  ((Leaf (x, dx), _) :: r) as l -> 
    if  !dx = d then
      Leaf x, r
  else
      let left,l = build (d+1) l in
      let right,l = build (d+1) l in
      Node (left, right), l

let garsia_wachs l =
  let l = map (fun (x, wx) -> Leaf (x, ref 0), wx) l in
  let t = phase1 l in
  mark 0 t;
  let t, l = build 0 l in
  assert (l = []);
  t
