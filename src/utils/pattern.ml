type 'var t =
    ('var plain_t) Common.pos
and 'var plain_t =
  | Var of 'var
  | As of 'var t * 'var
  | Tuple of ('var t) list
  | Record of (Common.field * 'var t) list
  | Variant of Common.label * ('var t) option
  | Const of Common.const
  | Nonbinding
(* Changing the datatype [plain_t] will break [specialize_vector] in [exhaust.ml] because
   of wildcard matches there. *)

(* [pattern_vars p] returns the list of variables appearing in pattern [p]. *)
let rec pattern_vars (p, _) =
  match p with
    | Var x -> [x]
    | As (p,x) -> x :: pattern_vars p
    | Tuple lst -> List.fold_left (fun vs p -> vs @ pattern_vars p) [] lst
    | Record lst -> List.fold_left (fun vs (_, p) -> vs @ pattern_vars p) [] lst
    | Variant (_, None) -> []
    | Variant (_, Some p) -> pattern_vars p
    | Const _ -> []
    | Nonbinding -> []

(* [linear_pattern p] verifies that [p] is linear and has linear records. *)
let linear_pattern p =
  let rec linear_records (p, _) =
    match p with
      | Var x -> true
      | As (p, _) -> linear_records p
      | Tuple lst -> List.for_all linear_records lst
      | Record lst -> List.for_all (fun (_, p) -> linear_records p) lst
      | Variant (_, None) -> true
      | Variant (_, Some p) -> linear_records p
      | Const _ -> true
      | Nonbinding -> true
  in
    Common.injective (fun x -> x) (pattern_vars p) && linear_records p

let rec map f (p, pos) =
  let p' = match p with
    | Var x -> Var (f x)
    | As (p, x) -> As (map f p, f x)
    | Tuple lst -> Tuple (List.map (map f) lst)
    | Record lst -> Record (Common.assoc_map (map f) lst)
    | Variant (lbl, e) -> Variant (lbl, Common.option_map (map f) e)
    | Const c -> Const c
    | Nonbinding -> Nonbinding
  in
  (p', pos)

(* [linear_record r] verifies that a record or a record pattern has linear field names. *)
let linear_record lst = Common.injective fst lst
