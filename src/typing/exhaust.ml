module C = OldUtils
module P = Pattern
module Untyped = CoreSyntax


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
  | Record of C.field list
  | Variant of C.label * bool
  | Const of Const.t
  | Wildcard

(* The number of subpatterns required by a pattern constructor. *)
let arity = function
  | Const _ | Wildcard -> 0
  | Tuple n -> n
  | Record flds -> List.length flds
  | Variant (_, b) -> if b then 1 else 0

(* Removes the top-most [As] pattern wrappers, if present (e.g. [2 as x] -> [2]). *)
let rec remove_as = function
  | Pattern.As ((p', _), _) -> remove_as p'
  | p -> p

(* Reads constructor description from a pattern, discarding any [P.As] layers. *)
let rec cons_of_pattern p =
  match fst p with
    | P.As (p, _) -> cons_of_pattern p
    | P.Tuple lst -> Tuple (List.length lst)
    | P.Record [] -> assert false
    | P.Record ((lbl, _) :: _) ->
        (match Tctx.find_field lbl with
          | None -> Error.typing ~loc:(snd p) "Unbound record field label %s in a pattern" lbl
          | Some (_, _, flds) -> Record (List.map fst flds))
    | P.Variant (lbl, opt) -> Variant (lbl, opt <> None)
    | P.Const c -> Const c
    | P.Var _ | P.Nonbinding -> Wildcard

(* Constructs a pattern from a constructor and a list of subpatterns, which must
   contain [arity c] elements. *)
let pattern_of_cons ~loc c lst =
  let plain = match c with
    | Tuple n -> P.Tuple lst
    | Record flds -> P.Record (List.combine flds lst)
    | Const const -> P.Const const
    | Variant (lbl, opt) -> P.Variant (lbl, if opt then Some (List.hd lst) else None)
    | Wildcard -> P.Nonbinding
  in
  (plain, loc)

(* Finds all distinct non-wildcard root pattern constructors in [lst], and at
   least one constructor of their type not present in [lst] if it exists. *)
let find_constructors lst =
  let present = List.filter (fun c -> c <> Wildcard)
                            (List.map cons_of_pattern (C.uniq lst))
  in
  let missing = match present with
    | [] -> [Wildcard]
    | cons :: _ ->
        begin match cons with
          (* Tuples and records of any type have exactly one constructor. *)
          | Tuple _ | Record _ -> []
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
             let is_last = function
               | Const.Boolean b -> b
               | _ -> false
             in
             let rec find c =
               if (is_last c) then [] else begin
                 if List.exists (function Const c' -> Const.equal c c' | _ -> false) present
                 then find (next c) else [Const c]
               end
             in
             find (first c)
          (* Check if all tags defined by this variant type are covered. *)
          | Variant (lbl, _) ->
              (match Tctx.find_variant lbl with
                | None -> assert false (* We assume that everything is type-checked *)
                | Some (_, _, tags, _) ->
                  let all = List.map (fun (lbl, opt) -> Variant (lbl, opt <> None)) tags
                  in
                    C.diff all present)
          (* Only for completeness. *)
          | Wildcard -> []
        end
  in
  (present, missing)

(* Specializes a pattern vector for the pattern constructor [con]. Returns None
   if the first pattern of input vector has an incompatible constructor. *)
let specialize_vector ~loc con = function
  | [] -> None
  | (p1, _) :: lst ->
      begin match con, remove_as p1 with
        | Tuple _, P.Tuple l -> Some (l @ lst)
        | Record all, P.Record def ->
            let get_pattern defs lbl = match C.lookup lbl defs with
              | Some p' -> p'
              | None -> (P.Nonbinding, loc)
            in
            Some ((List.map (get_pattern def) all) @ lst)
        | Variant (lbl, _), P.Variant (lbl', opt) when lbl = lbl' ->
            begin match opt with
              | Some p -> Some (p :: lst)
              | None -> Some lst
            end
        | Const c, P.Const c' when Const.equal c c' -> Some lst
        | _, (P.Nonbinding | P.Var _) -> Some ((C.repeat (P.Nonbinding, loc) (arity con)) @ lst)
        | _, _ -> None
      end

(* Specializes a pattern matrix for the pattern constructor [con]. *)
let rec specialize ~loc con = function
  | [] -> []
  | row :: lst ->
      begin match specialize_vector ~loc con row with
        | Some row' -> row' :: (specialize ~loc con lst)
        | None -> (specialize ~loc con lst)
      end

(* Creates a default matrix from the input pattern matrix. *)
let rec default = function
  | [] -> []
  | [] :: lst -> default lst (* Only for completeness. *)
  | ((p,_) :: ps) :: lst ->
      begin match remove_as p with
        | (P.Nonbinding | P.Var _) -> ps :: (default lst)
        | _ -> default lst
      end

(* Is the pattern vector [q] useful w.r.t. pattern matrix [p]? *)
let rec useful ~loc p q =
  match q with
    (* Base case. *)
    | [] -> p = []
    (* Induction on the number of columns of [p] and [q]. *)
    | q1 :: qs ->
        let c = cons_of_pattern q1 in
        begin match c with
          (* If the first pattern in [q] is constructed, check the matrix [p]
             specialized for that constructor. *)
          | Tuple _ | Record _ | Variant _ | Const _ ->
              begin match specialize_vector ~loc c q with
                | None -> assert false
                | Some q' -> useful ~loc (specialize ~loc c p) q'
              end
          (* Otherwise, check if pattern constructors in the first column of [p]
             form a complete type signature. If they do, check if [q] is useful
             for any specialization of [p] for that type; if not, only the
             default matrix of [p] must be checked. *)
          | Wildcard ->
              let (present, missing) = find_constructors (List.map List.hd p) in
              if present <> [] && missing = [] then
                List.exists (fun x -> match (specialize_vector ~loc x q) with
                                        | None -> false
                                        | Some q' -> useful ~loc (specialize ~loc x p) q')
                            present
              else
                useful ~loc (default p) qs
        end

(* Specialized version of [useful] that checks if a pattern matrix [p] with [n]
   columns is exhaustive (equivalent to calling [useful] on [p] with a vector
   of [n] wildcard patterns). Returns a list with at least one counterexample if
   [p] is not exhaustive. *)
let rec exhaustive ~loc p = function
  | 0 -> if p = [] then Some [] else None
  | n ->
      let (present, missing) = find_constructors (List.map List.hd p) in
      if present <> [] && missing = [] then
        let rec find = function
          | [] -> None
          | c :: cs ->
              begin match exhaustive ~loc (specialize ~loc c p) ((arity c)+n-1) with
                | None -> find cs
                | Some lst ->
                    let (ps, rest) = C.split (arity c) lst in
                    Some ((pattern_of_cons ~loc c ps) :: rest)
              end
        in
        find present
      else
        match exhaustive ~loc (default p) (n-1) with
          | None -> None
          | Some lst ->
              let c = List.hd missing in
              Some ((pattern_of_cons ~loc c (C.repeat (P.Nonbinding, loc) (arity c))) :: lst)


let rec old_of_new_pattern p =
  let old_p =
    match p.Untyped.term with
    | Untyped.PAs (p, x) -> P.As (old_of_new_pattern p, x)
    | Untyped.PTuple lst -> P.Tuple (List.map old_of_new_pattern lst)
    | Untyped.PRecord lst -> P.Record (OldUtils.assoc_map old_of_new_pattern lst)
    | Untyped.PVariant (lbl, opt) -> P.Variant (lbl, OldUtils.option_map old_of_new_pattern opt)
    | Untyped.PConst c -> P.Const c
    | Untyped.PVar x -> P.Var x
    | Untyped.PNonbinding -> P.Nonbinding
  in
  (old_p, p.Untyped.location)

let rec new_of_old_pattern p =
  let new_p =
    match fst p with
    | P.As (p, x) -> Untyped.PAs (new_of_old_pattern p, x)
    | P.Tuple lst -> Untyped.PTuple (List.map new_of_old_pattern lst)
    | P.Record lst -> Untyped.PRecord (OldUtils.assoc_map new_of_old_pattern lst)
    | P.Variant (lbl, opt) -> Untyped.PVariant (lbl, OldUtils.option_map new_of_old_pattern opt)
    | P.Const c -> Untyped.PConst c
    | P.Var x -> Untyped.PVar x
    | P.Nonbinding -> Untyped.PNonbinding
  in
  {
    Untyped.term = new_p;
    Untyped.location = snd p
  }

(* Prints a warning if the list of patterns [pats] is not exhaustive or contains
   unused patterns. *)
let check_patterns ~loc pats =
  (* [p] contains the patterns that have already been checked for usefulness. *)
  let rec check p pats = match pats with
    | [] ->
        begin match exhaustive ~loc p 1 with
          | Some ps ->
              Print.warning ~loc "@[This pattern-matching is not exhaustive.@.
                                    Here is an example of a value that is not matched:@.  @[%t@]"
              (Untyped.print_pattern (new_of_old_pattern (List.hd ps)));
          | None -> ()
        end
    | (_, loc) as pat :: pats ->
        if not (useful ~loc p [pat]) then
          begin
            Print.warning ~loc "This match case is unused.";
            check p pats
          end
        else
          check ([pat] :: p) pats (* Order of rows in [p] is not important. *)
  in
  check [] pats

(* A pattern is irrefutable if it cannot fail during pattern matching. *)
let is_irrefutable p =
  let p = old_of_new_pattern p in
  check_patterns ~loc:(snd p) [p]

(* Check for refutable patterns in let statements and non-exhaustive match
   statements. *)
let check_comp c =
  let rec check c =
    match c.Untyped.term with
      | Untyped.Value _ -> ()
      | Untyped.Let (lst, c) ->
        List.iter (fun (p, c) -> is_irrefutable p ; check c) lst ;
        check c
      | Untyped.LetRec (lst, c) ->
        List.iter (fun (_, (p, c)) -> is_irrefutable p ; check c) lst ;
      | Untyped.Match (_, []) -> () (* Skip empty match to avoid an unwanted warning. *)
      | Untyped.Match (_, lst) -> 
        check_patterns ~loc:c.Untyped.location (List.map (OldUtils.compose old_of_new_pattern fst) lst) ;
        List.iter (fun (_, c) -> check c) lst
      | Untyped.Apply _ -> ()
      | Untyped.Handle (_, c) -> check c
      | Untyped.Check c -> check c
  in
    check c
