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

type comparison = Less | Equal | Greater | Invalid

(** Variants for the built-in list type *)
let cons = "$1cons"

let nil = "$0nil"


let no_duplicates lst =
  let rec check seen = function
    | [] -> true
    | x :: xs -> not (List.mem x seen) && check (x :: seen) xs
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

(** [repeat x n] creates a list with [x] repeated [n] times. *)
let rec repeat x = function 0 -> [] | n -> x :: repeat x (n - 1)

let rec find p = function
  | [] -> None
  | x :: lst -> if p x then Some x else find p lst

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
