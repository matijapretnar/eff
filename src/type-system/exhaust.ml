open CoreUtils

module Untyped = UntypedSyntax

(* Pattern matching exhaustiveness checking as described by Maranget [1]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred.

   Another assumption made by the code is that all types are inhabited by some
   values. An example where this matters is:

   let f x = (match x with) ; let (y, 42) = (x, 23) in y ;;

   Here we get a warning about non-exhaustive pattern match, but in fact
   since x has the empty type, the code will never execute (there is nothing
   we could pass to f). One solution would be to have the patterns explicitly
   typed, then we could compute whether the type is non-inhabited.

   [1] http://pauillac.inria.fr/~maranget/papers/warn/index.html
*)
(* Types of constructors. *)
type cons =
  | Tuple of int
  | Record of OldUtils.field list
  | Variant of OldUtils.label * bool
  | Const of Const.t
  | Wildcard

(* The number of subpatterns required by a pattern constructor. *)
let arity = function
  | Const _ | Wildcard -> 0
  | Tuple n -> n
  | Record flds -> List.length flds
  | Variant (_, b) -> if b then 1 else 0


(* Removes the top-most [As] pattern wrappers, if present (e.g. [2 as x] -> [2]). *)
let rec remove_as {it= p} =
  match p with Untyped.PAs (p', _) -> remove_as p' | p -> p


(* Reads constructor description from a pattern, discarding any [Untyped.PAs] layers. *)
let rec cons_of_pattern {it= p; at= loc} =
  match p with
  | Untyped.PAs (p, _) -> cons_of_pattern p
  | Untyped.PTuple lst -> Tuple (List.length lst)
  | Untyped.PRecord flds -> (
    match Assoc.pop flds with
    | None -> assert false
    | Some ((lbl, _), _) ->
      match Tctx.find_field lbl with
      | None ->
          Error.typing ~loc "Unbound record field label %s in a pattern" lbl
      | Some (_, _, flds) -> Record (Assoc.keys_of flds) )
  | Untyped.PVariant (lbl, opt) -> Variant (lbl, opt <> None)
  | Untyped.PConst c -> Const c
  | Untyped.PVar _ | Untyped.PNonbinding -> Wildcard


(* Constructs a pattern from a constructor and a list of subpatterns, which must
   contain [arity c] elements. *)
let pattern_of_cons ~loc c lst =
  let plain =
    match c with
    | Tuple n -> Untyped.PTuple lst
    | Record flds -> Untyped.PRecord (Assoc.of_list (List.combine flds lst))
    | Const const -> Untyped.PConst const
    | Variant (lbl, opt) ->
        Untyped.PVariant (lbl, if opt then Some (List.hd lst) else None)
    | Wildcard -> Untyped.PNonbinding
  in
  {it= plain; at= loc}


(* Finds all distinct non-wildcard root pattern constructors in [lst], and at
   least one constructor of their type not present in [lst] if it exists. *)
let find_constructors lst =
  let present =
    List.filter
      (fun c -> c <> Wildcard)
      (List.map cons_of_pattern (OldUtils.uniq lst))
  in
  let missing =
    match present with
    | [] -> [Wildcard]
    | cons :: _ ->
      match cons with
      (* Tuples and records of any type have exactly one constructor. *)
      | Tuple _ | Record _ ->
          []
      (* Try to find an unmatched value in a countable set of constants. *)
      | Const c ->
          let first = function
            | Const.Integer _ -> Const.of_integer 0
            | Const.String _ -> Const.of_string ""
            | Const.Boolean _ -> Const.of_false
            | Const.Float _ -> Const.of_float 0.0
          in
          let next = function
            | Const.Integer v -> Const.of_integer (succ v)
            | Const.String v -> Const.of_string (v ^ "*")
            | Const.Boolean v -> Const.of_boolean (not v)
            | Const.Float v -> Const.of_float (v +. 1.0)
          in
          (* Only booleans are considered finite. *)
          let is_last = function Const.Boolean b -> b | _ -> false in
          let rec find c =
            if is_last c then []
            else if List.exists
                      (function Const c' -> Const.equal c c' | _ -> false)
                      present
            then find (next c)
            else [Const c]
          in
          find (first c)
      (* Check if all tags defined by this variant type are covered. *)
      | Variant (lbl, _) -> (
        match Tctx.find_variant lbl with
        | None -> assert false (* We assume that everything is type-checked *)
        | Some (_, _, tags, _) ->
            let all =
              List.map
                (fun (lbl, opt) -> Variant (lbl, opt <> None))
                (Assoc.to_list tags)
            in
            OldUtils.diff all present )
      (* Only for completeness. *)
      | Wildcard -> []
  in
  (present, missing)


(* Specializes a pattern vector for the pattern constructor [con]. Returns None
   if the first pattern of input vector has an incompatible constructor. *)
let specialize_vector ~loc con = function
  | [] -> None
  | p1 :: lst ->
    match (con, remove_as p1) with
    | Tuple _, Untyped.PTuple l -> Some (l @ lst)
    | Record all, Untyped.PRecord def ->
        let get_pattern defs lbl =
          match Assoc.lookup lbl defs with
          | Some p' -> p'
          | None -> {it= Untyped.PNonbinding; at= loc}
        in
        Some (List.map (get_pattern def) all @ lst)
    | Variant (lbl, _), Untyped.PVariant (lbl', opt) when lbl = lbl' -> (
      match opt with Some p -> Some (p :: lst) | None -> Some lst )
    | Const c, Untyped.PConst c' when Const.equal c c' -> Some lst
    | _, (Untyped.PNonbinding | Untyped.PVar _) ->
        Some
          ( OldUtils.repeat
              {it= Untyped.PNonbinding; at= loc}
              (arity con)
          @ lst )
    | _, _ -> None


(* Specializes a pattern matrix for the pattern constructor [con]. *)
let rec specialize ~loc con = function
  | [] -> []
  | row :: lst ->
    match specialize_vector ~loc con row with
    | Some row' -> row' :: specialize ~loc con lst
    | None -> specialize ~loc con lst


(* Creates a default matrix from the input pattern matrix. *)
let rec default = function
  | [] -> []
  | [] :: lst -> default lst (* Only for completeness. *)
  | (p :: ps) :: lst ->
    match remove_as p with
    | Untyped.PNonbinding | Untyped.PVar _ -> ps :: default lst
    | _ -> default lst


(* Is the pattern vector [q] useful w.r.t. pattern matrix [p]? *)
let rec useful ~loc p q =
  match q with
  (* Base case. *)
  | [] -> p = []
  (* Induction on the number of columns of [p] and [q]. *)
  | q1 :: qs ->
      let c = cons_of_pattern q1 in
      match c with
      (* If the first pattern in [q] is constructed, check the matrix [p]
             specialized for that constructor. *)
      | Tuple _ | Record _ | Variant _ | Const _ -> (
        match specialize_vector ~loc c q with
        | None -> assert false
        | Some q' -> useful ~loc (specialize ~loc c p) q' )
      (* Otherwise, check if pattern constructors in the first column of [p]
             form a complete type signature. If they do, check if [q] is useful
             for any specialization of [p] for that type; if not, only the
             default matrix of [p] must be checked. *)
      | Wildcard ->
          let present, missing = find_constructors (List.map List.hd p) in
          if present <> [] && missing = [] then
            List.exists
              (fun x ->
                match specialize_vector ~loc x q with
                | None -> false
                | Some q' -> useful ~loc (specialize ~loc x p) q' )
              present
          else useful ~loc (default p) qs


(* Specialized version of [useful] that checks if a pattern matrix [p] with [n]
   columns is exhaustive (equivalent to calling [useful] on [p] with a vector
   of [n] wildcard patterns). Returns a list with at least one counterexample if
   [p] is not exhaustive. *)
let rec exhaustive ~loc p = function
  | 0 -> if p = [] then Some [] else None
  | n ->
      let present, missing = find_constructors (List.map List.hd p) in
      if present <> [] && missing = [] then
        let rec find = function
          | [] -> None
          | c :: cs ->
            match exhaustive ~loc (specialize ~loc c p) (arity c + n - 1) with
            | None -> find cs
            | Some lst ->
                let ps, rest = OldUtils.split (arity c) lst in
                Some (pattern_of_cons ~loc c ps :: rest)
        in
        find present
      else
        match exhaustive ~loc (default p) (n - 1) with
        | None -> None
        | Some lst ->
            let c = List.hd missing in
            Some
              ( pattern_of_cons ~loc c
                  (OldUtils.repeat
                     {it= Untyped.PNonbinding; at= loc}
                     (arity c))
              :: lst )


(* Prints a warning if the list of patterns [pats] is not exhaustive or contains
   unused patterns. *)
let check_patterns ~loc pats =
  (* [p] contains the patterns that have already been checked for usefulness. *)
  let rec check p pats =
    match pats with
    | [] -> (
      match exhaustive ~loc p 1 with
      | Some ps ->
          Print.warning ~loc
            "@[This pattern-matching is not exhaustive.@.\n                                    Here is an example of a value that is not matched:@.  @[%t@]"
            (Untyped.print_pattern (List.hd ps))
      | None -> () )
    | pat :: pats ->
        if not (useful ~loc p [pat]) then (
          Print.warning ~loc "This match case is unused." ;
          check p pats )
        else check ([pat] :: p) pats
    (* Order of rows in [p] is not important. *)
  in
  check [] pats


(* A pattern is irrefutable if it cannot fail during pattern matching. *)
let is_irrefutable p = check_patterns ~loc:p.at [p]

(* Check for refutable patterns in let statements and non-exhaustive match
   statements. *)
let check_comp c =
  let rec check c =
    match c.it with
    | Untyped.Value _ -> ()
    | Untyped.Let (lst, c) ->
        List.iter (fun (p, c) -> is_irrefutable p ; check c) lst ;
        check c
    | Untyped.LetRec (lst, c) ->
        List.iter (fun (_, (p, c)) -> is_irrefutable p ; check c) lst
    | Untyped.Match (_, []) ->
        () (* Skip empty match to avoid an unwanted warning. *)
    | Untyped.Match (_, lst) ->
        check_patterns ~loc:c.at (List.map fst lst) ;
        List.iter (fun (_, c) -> check c) lst
    | Untyped.Apply _ -> ()
    | Untyped.Handle (_, c) -> check c
    | Untyped.Check c -> check c
  in
  check c
