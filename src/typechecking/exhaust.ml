module C = Common
module P = Pattern

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
  | Const of C.const
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
          | None -> Error.typing ~pos:(snd p) "Unbound record field label %s in a pattern" lbl
          | Some (_, _, flds) -> Record (List.map fst flds))
    | P.Variant (lbl, opt) -> Variant (lbl, opt <> None)
    | P.Const c -> Const c
    | P.Var _ | P.Nonbinding -> Wildcard

(* Constructs a pattern from a constructor and a list of subpatterns, which must
   contain [arity c] elements. *)
let pattern_of_cons ~pos c lst =
  let plain = match c with
    | Tuple n -> P.Tuple lst
    | Record flds -> P.Record (List.combine flds lst)
    | Const const -> P.Const const
    | Variant (lbl, opt) -> P.Variant (lbl, if opt then Some (List.hd lst) else None)
    | Wildcard -> P.Nonbinding
  in
  (plain, pos)

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
               | C.Integer _ -> C.Integer Big_int.zero_big_int
               | C.String _ -> C.String ""
               | C.Boolean _ -> C.Boolean false
               | C.Float _ -> C.Float 0.0
             in
             let next = function
               | C.Integer v -> C.Integer (Big_int.succ_big_int v)
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
               if (is_last c) then [] else begin
                 if List.exists (function Const c' -> C.equal_const c c' | _ -> false) present
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
let specialize_vector ~pos con = function
  | [] -> None
  | (p1, _) :: lst ->
      begin match con, remove_as p1 with
        | Tuple _, P.Tuple l -> Some (l @ lst)
        | Record all, P.Record def ->
            let get_pattern defs lbl = match C.lookup lbl defs with
              | Some p' -> p'
              | None -> (P.Nonbinding, pos)
            in
            Some ((List.map (get_pattern def) all) @ lst)
        | Variant (lbl, _), P.Variant (lbl', opt) when lbl = lbl' ->
            begin match opt with
              | Some p -> Some (p :: lst)
              | None -> Some lst
            end
        | Const c, P.Const c' when Common.equal_const c c' -> Some lst
        | _, (P.Nonbinding | P.Var _) -> Some ((C.repeat (P.Nonbinding, pos) (arity con)) @ lst)
        | _, _ -> None
      end

(* Specializes a pattern matrix for the pattern constructor [con]. *)
let rec specialize ~pos con = function
  | [] -> []
  | row :: lst ->
      begin match specialize_vector ~pos con row with
        | Some row' -> row' :: (specialize ~pos con lst)
        | None -> (specialize ~pos con lst)
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
let rec useful ~pos p q =
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
              begin match specialize_vector ~pos c q with
                | None -> assert false
                | Some q' -> useful ~pos (specialize ~pos c p) q'
              end
          (* Otherwise, check if pattern constructors in the first column of [p]
             form a complete type signature. If they do, check if [q] is useful
             for any specialization of [p] for that type; if not, only the
             default matrix of [p] must be checked. *)
          | Wildcard ->
              let (present, missing) = find_constructors (List.map List.hd p) in
              if present <> [] && missing = [] then
                List.exists (fun x -> match (specialize_vector ~pos x q) with
                                        | None -> false
                                        | Some q' -> useful ~pos (specialize ~pos x p) q')
                            present
              else
                useful ~pos (default p) qs
        end

(* Specialized version of [useful] that checks if a pattern matrix [p] with [n]
   columns is exhaustive (equivalent to calling [useful] on [p] with a vector
   of [n] wildcard patterns). Returns a list with at least one counterexample if
   [p] is not exhaustive. *)
let rec exhaustive ~pos p = function
  | 0 -> if p = [] then Some [] else None
  | n ->
      let (present, missing) = find_constructors (List.map List.hd p) in
      if present <> [] && missing = [] then
        let rec find = function
          | [] -> None
          | c :: cs ->
              begin match exhaustive ~pos (specialize ~pos c p) ((arity c)+n-1) with
                | None -> find cs
                | Some lst ->
                    let (ps, rest) = C.split (arity c) lst in
                    Some ((pattern_of_cons ~pos c ps) :: rest)
              end
        in
        find present
      else
        match exhaustive ~pos (default p) (n-1) with
          | None -> None
          | Some lst ->
              let c = List.hd missing in
              Some ((pattern_of_cons ~pos c (C.repeat (P.Nonbinding, pos) (arity c))) :: lst)

(* Prints a warning if the list of patterns [pats] is not exhaustive or contains
   unused patterns. *)
let check_patterns ~pos pats =
  (* [p] contains the patterns that have already been checked for usefulness. *)
  let rec check p pats = match pats with
    | [] ->
        begin match exhaustive ~pos p 1 with
          | Some ps ->
              Print.warning ~pos "This pattern-matching is not exhaustive.\n\
                                      Here is an example of a value that is not matched:";
(*  *)              prerr_endline (Print.to_string "%t" (Syntax.print_pattern (List.hd ps)))
          | None -> ()
        end
    | (_, pos) as pat :: pats ->
        if not (useful ~pos p [pat]) then
          begin
            Print.warning ~pos "This match case is unused.";
            check p pats
          end
        else
          check ([pat] :: p) pats (* Order of rows in [p] is not important. *)
  in
  check [] pats

(* A pattern is irrefutable if it cannot fail during pattern matching. *)
let is_irrefutable p = check_patterns ~pos:(snd p) [p]

(* Check for refutable patterns in let statements and non-exhaustive match
   statements. *)
let check_comp c =
  let rec check (c, pos) =
    match c with
      | Syntax.Value _ -> ()
      | Syntax.Let (lst, c) ->
        List.iter (fun (p, c) -> is_irrefutable p ; check c) lst ;
        check c
      | Syntax.LetRec (lst, c) ->
        List.iter (fun (_, (p, c)) -> is_irrefutable p ; check c) lst ;
      | Syntax.Match (_, []) -> () (* Skip empty match to avoid an unwanted warning. *)
      | Syntax.Match (_, lst) -> 
        check_patterns ~pos:pos (List.map fst lst) ;
        List.iter (fun (_, c) -> check c) lst
      | Syntax.While (c1, c2) -> check c1 ; check c2
      | Syntax.For (_, _, _, c, _) -> check c
      | Syntax.Apply _ -> ()
      | Syntax.New (_, None) -> ()
      | Syntax.New (_, Some (_, lst)) -> 
        List.iter (fun (_, (p1, p2, c)) -> is_irrefutable p1 ; is_irrefutable p2 ; check c) lst
      | Syntax.Handle (_, c) -> check c
      | Syntax.Check c -> check c
  in
    check c
