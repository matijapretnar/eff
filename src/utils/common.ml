(** Common definitions. *)

(** Types shared by different modules *)
type opsym = string (** operation symbols *)
type effect = string (** effect symbols *)
type label = string (** variant labels *)
type field = string (** record fields *)

type tyname = string (** type names *)
type typaram = string (** type parameters *)
type dirtparam = int (** dirt parameters *)
type regionparam = int (** region parameters *)

let id x = x
let compose f g x = f (g x)

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

let lookup_default x =
  List.fold_right (fun (x', y) rest -> if x = x' then y else rest)

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

(** [assoc_map f lst] transforms each [(k, v)] in [lst] into [(k, f v)]. *)
let rec assoc_map f = function
  | [] -> []
  | (l, x) :: xs ->
      let y = f x in
      let ys = assoc_map f xs in
      (l, y) :: ys

(** [fresh wrapper] creates a function that creates fresh instances and wraps
    them with the [wrapper] function *)
let fresh wrapper =
  let counter = ref (-1) in
  fun () ->
    incr counter;
    assert (!counter >= 0);
    wrapper !counter

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


let print_const c ppf =
  match c with
  | Integer k -> Format.fprintf ppf "%s" (Big_int.string_of_big_int k)
  | String s -> Format.fprintf ppf "%S" s
  | Boolean b -> Format.fprintf ppf "%B" b
  | Float f -> Format.fprintf ppf "%F" f

let assoc_flatten lst =
  let add (k, v) lst =
  begin match lookup k lst with
  | None -> (k, ref [v]) :: lst
  | Some vs -> vs := v :: !vs; lst
  end
  in
  let lst = List.fold_right add lst [] in
  assoc_map (!) lst
