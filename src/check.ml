module C = Common
module P = Pattern

(* Pattern matching exhaustiveness checking as described by Maranget [0]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred.
   [0] http://pauillac.inria.fr/~maranget/papers/warn/index.html *)

(* Pattern constructor description. *)
type cons =
  Tuple of int | Record of C.field list | Variant of C.label * bool | Const of C.const | Wildcard

(* The number of subpatterns required by a pattern constructor. *)
let arity = function
  | Const _ | Wildcard -> 0
  | Tuple n -> n
  | Record flds -> List.length flds
  | Variant (_, b) -> if b then 1 else 0

(* Reads constructor description from a pattern, discarding any P.As layers. *)
let rec cons_of_pattern tctx p =
  match fst p with
    | P.As _ -> cons_of_pattern tctx (P.simplify p)
    | P.Tuple lst -> Tuple (List.length lst)
    | P.Record [] -> assert false
    | P.Record ((lbl, _) :: _) ->
        let (_, _, flds) = Tctx.find_field tctx lbl in
        Record (List.map fst flds)
    | P.Variant (lbl, opt) -> Variant (lbl, opt <> None)
    | P.Const c -> Const c
    | P.Var _ | P.Nonbinding -> Wildcard

(* Constructs a pattern from a constructor and a list of subpatterns, which must
   contain [arity c] elements. *)
let pattern_of_cons c lst =
  let plain = match c with
    | Tuple n -> P.Tuple lst
    | Record flds -> P.Record (List.combine flds lst)
    | Const const -> P.Const const
    | Variant (lbl, opt) -> P.Variant (lbl, if opt then Some (List.hd lst) else None)
    | Wildcard -> P.Nonbinding
  in
  (plain, C.Nowhere)

(* Finds all distinct non-wildcard root pattern constructors in [lst], and at
   least one constructor of their type not present in [lst] if it exists. *)
let find_constructors lst tctx =
  let present = List.filter (fun c -> c <> Wildcard)
                            (List.map (cons_of_pattern tctx) (C.uniq lst))
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
               | C.Integer _ -> C.Integer 0
               | C.String _ -> C.String ""
               | C.Boolean _ -> C.Boolean false
               | C.Float _ -> C.Float 0.0
             in
             let next = function
               | C.Integer v -> C.Integer (succ v)
               | C.String v -> C.String (v ^ "*")
               | C.Boolean v -> C.Boolean (not v)
               | C.Float v -> C.Float (v +. 1.0)
             in
             (* Only booleans are considered finite. *)
             let is_last = function
               | C.Boolean b -> b
               | _ -> false
             in
             let rec find c =
               let c' = Const c in
               if (is_last c) then [] else begin
                 if List.mem c' present then find (next c) else [c']
               end
             in
             find (first c)
          (* Check if all tags defined by this variant type are covered. *)
          | Variant (lbl, _) ->
              let (_, _, tags, _) = Tctx.find_variant tctx lbl in
              let all = (List.map (fun (lbl, opt) -> Variant (lbl, opt <> None)) tags) in
              C.diff all present
          (* Only for completeness. *)
          | Wildcard -> []
        end
  in
  (present, missing)

(* Specializes a pattern vector for the pattern constructor [con]. Returns None
   if the first pattern of input vector has an incompatible constructor. *)
let specialize_vector tctx con = function
  | [] -> None
  | p1 :: lst ->
      let (p1, _) = P.simplify p1 in
      begin match con, p1 with
        | Tuple _, P.Tuple l -> Some (l @ lst)
        | Record all, P.Record def ->
            let get_pattern defs lbl = match C.lookup lbl defs with
              | Some p' -> p'
              | None -> (P.Nonbinding, C.Nowhere)
            in
            Some ((List.map (get_pattern def) all) @ lst)
        | Variant (lbl, _), P.Variant (lbl', opt) when lbl = lbl' ->
            begin match opt with
              | Some p -> Some (p :: lst)
              | None -> Some lst
            end
        | Const c, P.Const c' when c = c' -> Some lst
        | _, (P.Nonbinding | P.Var _) -> Some ((C.repeat (P.Nonbinding, C.Nowhere) (arity con)) @ lst)
        | _ -> None
      end

(* Specializes a pattern matrix for the pattern constructor [con]. *)
let rec specialize tctx con = function
  | [] -> []
  | row :: lst ->
      begin match specialize_vector tctx con row with
        | Some row' -> row' :: (specialize tctx con lst)
        | None -> (specialize tctx con lst)
      end

(* Creates a default matrix from the input pattern matrix. *)
let rec default = function
  | [] -> []
  | [] :: lst -> default lst (* Only for completeness. *)
  | (p :: ps) :: lst ->
      let p = P.simplify p in
      begin match p with
        | ((P.Nonbinding | P.Var _), _) -> ps :: (default lst)
        | _ -> default lst
      end

(* Is the pattern vector [q] useful w.r.t. pattern matrix [p]? *)
let rec useful tctx p q =
  match q with
    (* Base case. *)
    | [] -> p = []
    (* Induction on the number of columns of [p] and [q]. *)
    | q1 :: qs ->
        let c = cons_of_pattern tctx q1 in
        begin match c with
          (* If the first pattern in [q] is constructed, check the matrix [p]
             specialized for that constructor. *)
          | Tuple _ | Record _ | Variant _ | Const _ ->
              begin match specialize_vector tctx c q with
                | None -> assert false
                | Some q' -> useful tctx (specialize tctx c p) q'
              end
          (* Otherwise, check if pattern constructors in the first column of [p]
             form a complete type signature. If they do, check if [q] is useful
             for any specialization of [p] for that type; if not, only the
             default matrix of [p] must be checked. *)
          | Wildcard ->
              let (present, missing) = find_constructors (List.map List.hd p) tctx in
              if present <> [] && missing = [] then
                List.exists (fun x -> match (specialize_vector tctx x q) with
                                        | None -> false
                                        | Some q' -> useful tctx (specialize tctx x p) q')
                            present
              else
                useful tctx (default p) qs
        end

(* Specialized version of [useful] that checks if a pattern matrix [p] with [n]
   columns is exhaustive (equivalent to calling [useful] on [p] with a vector
   of [n] wildcard patterns). Returns a list with at least one counterexample if
   [p] is not exhaustive. *)
let rec exhaustive tctx p = function
  | 0 -> if p = [] then Some [] else None
  | n ->
      let (present, missing) = find_constructors (List.map List.hd p) tctx in
      if present <> [] && missing = [] then
        let rec find = function
          | [] -> None
          | c :: cs ->
              begin match exhaustive tctx (specialize tctx c p) ((arity c)+n-1) with
                | None -> find cs
                | Some lst ->
                    let (ps, rest) = C.split (arity c) lst in
                    Some ((pattern_of_cons c ps) :: rest)
              end
        in
        find present
      else
        match exhaustive tctx (default p) (n-1) with
          | None -> None
          | Some lst ->
              let c = List.hd missing in
              Some ((pattern_of_cons c (C.repeat (P.Nonbinding, C.Nowhere) (arity c))) :: lst)

(* Prints a warning if the list of patterns [pats] is not exhaustive or contains
   unused patterns. *)
let check_patterns ?(pos = C.Nowhere) pats tctx =
  (* [p] contains the patterns that have already been checked for usefulness. *)
  let rec check p pats = match pats with
    | [] ->
        begin match exhaustive tctx p 1 with
          | Some ps ->
              Print.warning ~pos:pos "This pattern-matching is not exhaustive.\n\
                                      Here is an example of a value that is not matched:";
              prerr_endline (Print.to_string "%t" (Print.pattern (List.hd ps)))
          | None -> ()
        end
    | (_, pos) as pat :: pats ->
        if not (useful tctx p [pat]) then
          begin
            Print.warning ~pos:pos "This match case is unused.";
            check p pats
          end
        else
          check ([pat] :: p) pats (* Order of rows in [p] is not important. *)
  in
  check [] pats

(* A pattern is irrefutable if it cannot fail during pattern matching. *)
let is_irrefutable p tctx = check_patterns ~pos:(snd p) [p] tctx
