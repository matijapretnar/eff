type t =
    plain_t Common.pos
and plain_t =
  | Var of Common.variable
  | As of t * Common.variable
  | Tuple of t list
  | Record of (Common.field * t) list
  | Variant of Common.label * t option
  | Const of Common.const
  | Nonbinding

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

(* [linear_record r] verifies that a record or a record pattern has linear field names. *)
let linear_record lst = Common.injective fst lst

(* Removes any As pattern wrappers (e.g. [2 as x] -> [2]). *)
let rec simplify p = match p with
  | (As (p', _), _) -> simplify p'
  | _ -> p
