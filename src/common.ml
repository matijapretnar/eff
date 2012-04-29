(** Common definitions. *)

(** Types shared by different modules *)
type variable = string (** variable identifiers *)
type opsym = string (** operation symbols *)
type label = string (** variant labels *)
type field = string (** record fields *)

type tyname = string (** type names *)
type typaram = string (** type parameters *)

(** Positions *)
type position =
  | Position of Lexing.position * Lexing.position (** delimited position *)
  | Nowhere (** unknown region *)

(** A type enriched with a position *)
type 'a pos = 'a * position

(** A union of two positions *)
let join_pos (_, pos1) (_, pos2) =
  match pos1, pos2 with
  | _, Nowhere | Nowhere, _ -> Nowhere
  | Position (b1, _), Position (_, e2) -> Position (b1, e2)

(** Primitive constants *)
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

(** Variants for the built-in list type *)
let cons = "$1cons"
let nil = "$0nil"

(** Association lists *)
type ('key, 'value) assoc = ('key * 'value) list

(** Variants of association list operations that map into [option] type instead
    of raising [Not_found] *)
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

(* [find_duplicate xs ys] returns [Some x] if [x] is the first element of [xs]
   that appears [ys]. It returns [None] if there is no such element. *)
let rec find_duplicate xs ys =
  match xs with
    | [] -> None
    | x::xs -> if List.mem x ys then Some x else find_duplicate xs ys

(** NB: We use our own [map] to be sure that the order of side-effects is
    well-defined. *)
let rec map f = function
  | [] -> []
  | x :: xs ->
      let y = f x in
      let ys = map f xs in
      y :: ys

let flatten_map f xs = List.flatten (List.map f xs)

(** [option_map f] maps [None] to [None] and [Some x] to [Some (f x)]. *)
let option_map f = function
  | None -> None
  | Some x -> Some (f x)

(** [repeat x n] creates a list with [x] repeated [n] times. *)
let rec repeat x = function
  | 0 -> []
  | n -> x :: repeat x (n-1)

(** [remove x lst] returns [lst] with all occurrences of [x] removed. *)
let rec remove x = function
  | [] -> []
  | y::lst -> if x = y then remove x lst else y :: (remove x lst)

(** [assoc_map f lst] transforms each [(k, v)] in [lst] into [(k, f v)]. *)
let rec assoc_map f = function
  | [] -> []
  | (l, x) :: xs ->
      let y = f x in
      let ys = assoc_map f xs in
      (l, y) :: ys

(** [fresh sort] creates a function that creates fresh instances with label
    [sort] *)
let fresh sort =
  let counter = ref 0 in
  fun () ->
    let f = !counter in
    incr counter;
    if !counter = 0 then failwith ("Too many instances of " ^ sort ^ ".");
    f

(** [fresh_variable ()] creates a fresh variable ["$gen1"], ["$gen2"], ... on
    each call *)
let fresh_variable =
  let next_variable = fresh "variable" in
  fun () -> "$gen" ^ string_of_int (next_variable ())

(** [uniq lst] returns [lst] with all duplicates removed, keeping the first
    occurence of each element. *)
let uniq lst =
  let rec uniq acc = function
  | [] -> List.rev acc
  | x :: xs -> if List.mem x acc then uniq acc xs else uniq (x :: acc) xs
  in uniq [] lst

(** [diff lst1 lst2] returns [lst1] with all members of [lst2] removed *)
let diff lst1 lst2 = List.filter (fun x -> not (List.mem x lst2)) lst1

(** [subset lst1 lst2] returns [true] if [lst1] is a subset of [lst2]. *)
let subset lst1 lst2 = List.for_all (fun x -> List.mem x lst2) lst1

(** [equal_set lst1 lst2] returns [true] if the lists are equal as sets. *)
let equal_set lst1 lst2 = subset lst1 lst2 && subset lst2 lst1
