type variable = string
type opname = string
type effname = string
type label = string
type field = string

type tyname = string
type param = string

type position =
  | Position of Lexing.position * Lexing.position
  | Nowhere

type 'a pos = 'a * position

type op = effname * opname

type const =
  | Integer of Big_int.big_int
  | String of string
  | Boolean of bool
  | Float of float

let equal_const c1 c2 =
  match c1, c2 with
    | Integer k1, Integer k2 -> Big_int.eq_big_int k1 k2
    | String s1, String s2 -> s1 = s2
    | Boolean b1, Boolean b2 -> b1 = b2
    | Float f1, Float f2 -> f1 = f2
    | _, _ -> false

let less_than_const c1 c2 =
  match c1, c2 with
    | Integer k1, Integer k2 -> Big_int.lt_big_int k1 k2
    | String s1, String s2 -> String.compare s1 s2 < 0
    | Boolean b1, Boolean b2 -> not b1 && b2
    | Float f1, Float f2 -> f1 < f2
    | _, _ -> false

let cons = "$1cons"
let nil = "$0nil"

type ('key, 'value) assoc = ('key * 'value) list

let lookup k env =
  try
    Some (List.assoc k env)
  with
    | Not_found -> None

let find p lst =
  try
    Some (List.find p lst)
  with
    | Not_found -> None

let update k v env =
  (k, v) :: env

(* [injective f lst] returns [true] when [f] is injective on [lst]. *)
let injective f lst =
  let rec check ys = function
    | [] -> true
    | x :: xs -> let y = f x in not (List.mem y ys) && check (y::ys) xs
  in
    check [] lst

let join_pos (_, pos1) (_, pos2) =
  match pos1, pos2 with
  | _, Nowhere | Nowhere, _ -> Nowhere
  | Position (b1, _), Position (_, e2) -> Position (b1, e2)

let rec find_duplicate xs ys =
  match xs with
    | [] -> None
    | x::xs -> if List.mem x ys then Some x else find_duplicate xs ys

(** NB: We use our own [map] to be sure that the order of side-effects is well-defined. *)
let rec map f = function
  | [] -> []
  | x :: xs ->
      let y = f x in
      let ys = map f xs in
      y :: ys

let option_map f = function
  | None -> None
  | Some x -> Some (f x)

let rec remove x = function
  | [] -> []
  | y::lst -> if x = y then remove x lst else y :: (remove x lst)

let rec assoc_map f = function
  | [] -> []
  | (l, x) :: xs ->
      let y = f x in
      let ys = assoc_map f xs in
      (l, y) :: ys

let fresh sort =
  let counter = ref 0 in
  fun () ->
    let f = !counter in
    incr counter;
    if !counter = 0 then failwith ("Too many instances of " ^ sort ^ ".");
    f

let fresh_variable =
  let next_variable = fresh "variable" in
  fun () -> "$gen" ^ string_of_int (next_variable ())

let rec uniq = function
  | [] -> []
  | x::xs ->
    let ys = uniq xs in
      if List.mem x ys then ys else x::ys

let diff lst1 lst2 = List.filter (fun x -> not (List.mem x lst2)) lst1
