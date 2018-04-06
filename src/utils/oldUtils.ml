(** OldUtils.definitions. *)

(** Types shared by different modules *)

(** effect symbols *)
type effect = string

(** variant labels *)
type label = string

(** record fields *)
type field = string

(** type names *)
type tyname = string

(** type parameters *)
type typaram = string

(** dirt parameters *)
type dirtparam = int

(** region parameters *)
type regionparam = int

let id x = x

let compose f g x = f (g x)

type comparison = Less | Equal | Greater | Invalid

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


let lookup_default x =
  List.fold_right (fun (x', y) rest -> if x = x' then y else rest)


let rec remove_assoc x = function
  | [] -> []
  | (k, v) :: ys -> if x = k then ys else (k, v) :: remove_assoc x ys


let rec find p = function
  | [] -> None
  | x :: lst -> if p x then Some x else find p lst


let update k v env = (k, v) :: env

(* [injective f lst] returns [true] when [f] is injective on [lst]. *)
let injective f lst =
  let rec check ys = function
    | [] -> true
    | x :: xs ->
        let y = f x in
        not (List.mem y ys) && check (y :: ys) xs
  in
  check [] lst


(* [find_duplicate xs ys] returns [Some x] if [x] is the first element of [xs]
   that appears [ys]. It returns [None] if there is no such element. *)
let rec find_duplicate xs ys =
  match xs with
  | [] -> None
  | x :: xs -> if List.mem x ys then Some x else find_duplicate xs ys


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
let option_map f = function None -> None | Some x -> Some (f x)

let map_default f x = function None -> x | Some y -> f y

(** [repeat x n] creates a list with [x] repeated [n] times. *)
let rec repeat x = function 0 -> [] | n -> x :: repeat x (n - 1)

(** [assoc_map f lst] transforms each [(k, v)] in [lst] into [(k, f v)]. *)
let rec assoc_map f = function
  | [] -> []
  | (l, x) :: xs ->
      let y = f x in
      let ys = assoc_map f xs in
      (l, y) :: ys


(** [uniq lst] returns [lst] with all duplicates removed, keeping the first
    occurence of each element. *)
let uniq lst =
  let rec uniq acc = function
    | [] -> List.rev acc
    | x :: xs -> if List.mem x acc then uniq acc xs else uniq (x :: acc) xs
  in
  uniq [] lst


(** [split n lst] splits [lst] into two parts containing (up to) the first [n]
    elements and the rest. *)
let split n lst =
  let rec split_aux acc lst n =
    match (lst, n) with
    | [], _ | _, 0 -> (List.rev acc, lst)
    | x :: xs, n -> split_aux (x :: acc) xs (n - 1)
  in
  split_aux [] lst n


(** [diff lst1 lst2] returns [lst1] with all members of [lst2] removed *)
let diff lst1 lst2 = List.filter (fun x -> not (List.mem x lst2)) lst1

let to_string print x =
  print x Format.str_formatter ;
  Format.flush_str_formatter ()
