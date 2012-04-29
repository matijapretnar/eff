module C = Common
module P = Pattern

(* Pattern matching exhaustiveness checking as described by Maranget [0]. These
   functions assume that patterns are type correct, so they should be run only
   after types are inferred. The functions find_constructors, specialize_vector,
   specialize and default expect a pattern matrix (or vector) with at least one
   column.
   [0] http://pauillac.inria.fr/~maranget/papers/warn/index.html *)

(* Pattern constructors. *)
type cons =
  As | Tuple of int | Record of int | Variant of (C.label * bool) | Const of C.const | Wildcard

let cons_of_pattern p = match fst p with
  | P.As _ -> As
  | P.Tuple lst -> Tuple (List.length lst)
  | P.Record lst -> Record (List.length lst)
  | P.Variant (lbl, opt) -> Variant (lbl, opt <> None)
  | P.Const c -> Const c
  | P.Var _ | P.Nonbinding -> Wildcard

(* Returns the number of subpatterns required by a pattern constructor. *)
let arity = function
  | Const _ | Wildcard -> 0
  | As -> 1
  | Tuple n | Record n -> n
  | Variant (_, b) -> if b then 1 else 0

(* Returns a pair with the list of distinct non-wildcard root pattern
   constructors from the first column of matrix [p] as the first value, and
   the second value true if that list represents a complete type signature. *)
let find_constructors p tctx =
  let filter_column lst =
    C.uniq (List.filter (fun c -> c <> Wildcard) (List.map cons_of_pattern lst))
  in
  let pats = filter_column (List.map List.hd p) in
  let complete =
    match pats with
      (* Every type is assumed to have at least one constructor. *)
      | [] -> false
      (* Tuple, record and as patterns have exactly one constructor. *)
      | [Tuple _ | Record _ | As] -> true
      (* Booleans have exactly two distinct constructors. *)
      | [Const (C.Boolean b1); Const (C.Boolean b2)] -> b1 <> b2
      (* Floats, strings and integers have infinitely many constructors. *)
      | Const (C.Float _ | C.String _ | C.Integer _) :: _ -> false
      (* For variants, check if all labels are covered in [pats]. *)
      | Variant (lbl, _) :: _ ->
          begin match Ctx.find_variant_tags_from_label lbl tctx with
            | Some tags ->
                let pats' = (List.map (fun (lbl, opt) -> Variant (lbl, opt <> None)) tags) in
                C.equal_set pats pats'
            | None -> assert false
          end
      | _ -> false
  in
    (pats, complete)

(* Specializes a pattern vector for the pattern constructor [con]. *)
let specialize_vector con = function
  | [] -> assert false
  | (p1, _) :: lst ->
      begin match con, p1 with
        | As, P.As (p,_) -> Some (p :: lst)
        | Tuple _, P.Tuple l -> Some (l @ lst)
        (* TODO record *)
        | Variant (lbl, _), P.Variant (lbl', opt) when lbl = lbl' ->
            begin match opt with
              | Some p -> Some (p :: lst)
              | None -> Some lst
            end
        | Const c, P.Const c' when C.equal_const c c' -> Some lst
        | _, (P.Nonbinding | P.Var _) -> Some ((C.repeat (P.Nonbinding, C.Nowhere) (arity con)) @ lst)
        | _ -> None
      end

(* Specializes a pattern matrix for the pattern constructor [con]. *)
let rec specialize con = function
  | [] -> []
  | row :: lst ->
      begin match specialize_vector con row with
        | Some row' -> row' :: (specialize con lst)
        | None -> (specialize con lst)
      end

(* Creates a default matrix for input pattern matrix. *)
let rec default = function
  | [] -> []
  | row :: lst ->
      begin match row with
        | ((P.Nonbinding | P.Var _), _) :: ps -> ps :: (default lst)
        | _ -> default lst
      end

(* Is the pattern vector [q] useful w.r.t. pattern matrix [p]? *)
let rec useful p q tctx =
  match q with
    (* base case *)
    | [] -> List.length p = 0
    (* induction on the number of columns of p and q *)
    | q1 :: qs ->
        let c = cons_of_pattern q1 in
        begin match c with
          (* constructed pattern *)
          | As | Tuple _ | Record _ | Variant _ | Const _ ->
              begin match specialize_vector c q with
                | None -> assert false
                | Some q' -> useful (specialize c p) q' tctx
              end
          (* wildcard pattern *)
          | Wildcard ->
              let (cons_lst, complete_sig) = find_constructors p tctx in
              if complete_sig then
                List.exists (fun x -> match (specialize_vector x q) with
                                        | None -> false
                                        | Some q' -> useful (specialize x p) q' tctx)
                            cons_lst
              else
                useful (default p) qs tctx
        end

(* Checks the list of patterns [pats] of same type for exhaustiveness and unused
   patterns. *)
let check_patterns ?(pos = C.Nowhere) pats tctx =
  let rec check p pats =
    match pats with
      | [] ->
          if useful p [(P.Nonbinding, C.Nowhere)] tctx then
            Print.warning ~pos:pos "This pattern-matching is not exhaustive."
          else
            ()
      | (_, pos) as pat :: pats ->
          if not (useful p [pat] tctx) then
            begin
              Print.warning ~pos:pos "This match case is unused.";
              check p pats
            end
          else
            check ([pat] :: p) pats (* reverse order, but still correct result *)
  in
    check [] pats

(* A pattern is irrefutable if it cannot fail during pattern matching. *)
let is_irrefutable p tctx = check_patterns ~pos:(snd p) [p] tctx
