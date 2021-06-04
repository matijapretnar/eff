(* Triple *)

let triple n s =
  let rec loop1 i acc1 =
    if i < 1 then acc1
    else
      let rec loop2 j acc2 =
        if j < 1 then acc2
        else
          let rec loop3 m acc3 =
            if m < 1 then acc3
            else
              loop3 (m - 1)
                (List.append acc3
                   (if i + j + m == s then [ (i, j, m) ] else []))
          in
          loop2 (j - 1) (List.append acc2 (loop3 (j - 1) []))
      in
      loop1 (i - 1) (List.append acc1 (loop2 (i - 1) []))
  in
  loop1 n []

let handledTriple n s = triple n s

let handleTripleWrap (x, y) = handledTriple x y

(* Queens *)

let null = function [] -> true | x :: xs -> false

let isNothing = function None -> true | Some x -> false

let fromJust = function None -> failwith "fromJust: None" | Some x -> x

let rec filter p = function
  | [] -> []
  | x :: xs -> if p x then x :: filter p xs else filter p xs

let rec forall p = function
  | [] -> true
  | x :: xs -> if p x then forall p xs else false

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available x qs l = filter (fun y -> forall (no_attack (x, y)) qs) l

let handledQueens l n =
  let rec place x qs =
    if x = n + 1 then Some qs
    else
      let rec loop ys =
        if null ys then None
        else
          let solution = place (x + 1) ((x, List.hd ys) :: qs) in
          if isNothing solution then loop (List.tl ys) else solution
      in
      loop (available x qs l)
  in
  place 1 []

let findSolution n =
  let l = ref [] in
  for i = n downto 1 do
    l := i :: !l
  done;
  handledQueens !l n

(* Count *)

(* This is slower than pure version *)
let testCountImpure n =
  let state = ref n in
  let rec count () =
    let i = !state in
    if i = 0 then i
    else
      let _ = state := i - 1 in
      count ()
  in
  count ()

let testCount n =
  let rec count i = if i = 0 then i else count (i - 1) in
  count n

(* Generator *)

(* This is slower than pure version *)
let testGeneratorImpure n =
  let state = ref 0 in
  let rec generateFromTo l u =
    if l > u then ()
    else
      let _ = state := !state + l in
      generateFromTo (l + 1) u
  in
  generateFromTo 1 n;
  !state

let testGenerator n =
  let rec generateFromTo l u s =
    if l > u then s else generateFromTo (l + 1) u (s + l)
  in
  generateFromTo 1 n 0
