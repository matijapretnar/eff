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

type comparison = Less | Equal | Greater | Invalid

let compare_const c1 c2 =
  let cmp x y =
    let r = Pervasives.compare x y in
      if r < 0 then Less
      else if r > 0 then Greater
      else Equal
  in
    match c1 with
      | Integer k ->
        (match c2 with
          | Integer k' -> 
            let r = Big_int.compare_big_int k k' in
              if r < 0 then Less
              else if r > 0 then Greater
              else Equal
          | String _ | Boolean _ | Float _ -> Less)
    | String s ->
      (match c2 with
        | Integer _ -> Greater
        | String s' -> cmp s s'
        | Boolean _ | Float _ -> Less)
    | Boolean b ->
      (match c2 with
        | Integer _ | String _ -> Greater
        | Boolean b' -> cmp b b'
        | Float _ -> Less)
    | Float x ->
      (match c2 with
        | Integer _ | String _ | Boolean _ -> Greater
        | Float x' -> cmp x x')

let equal_const c1 c2 = (compare_const c1 c2 = Equal)

(** Variants for the built-in list type *)
let cons = "$1cons"
let nil = "$0nil"

(** Association lists *)
type ('key, 'value) assoc = ('key * 'value) list

(** Variants of association list operations that map into [option] type instead
    of raising [Not_found] *)
let rec lookup x = function
  | [] -> None
  | (x', y) :: lst -> if x = x' then Some y else lookup x lst

let rec find p = function
  | [] -> None
  | x :: lst -> if p x then Some x else find p lst

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

(** [split n lst] splits [lst] into two parts containing (up to) the first [n]
    elements and the rest. *)
let split n lst =
  let rec split_aux acc lst n = match lst, n with
    | ([], _) | (_, 0) -> (List.rev acc, lst)
    | x :: xs, n -> split_aux (x :: acc) xs (n-1)
  in
  split_aux [] lst n

(** [diff lst1 lst2] returns [lst1] with all members of [lst2] removed *)
let diff lst1 lst2 = List.filter (fun x -> not (List.mem x lst2)) lst1

(** [subset lst1 lst2] returns [true] if [lst1] is a subset of [lst2]. *)
let subset lst1 lst2 = List.for_all (fun x -> List.mem x lst2) lst1

(** [equal_set lst1 lst2] returns [true] if the lists are equal as sets. *)
let equal_set lst1 lst2 = subset lst1 lst2 && subset lst2 lst1
