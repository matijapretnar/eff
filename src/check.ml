module C = Common
module P = Pattern

(* Pattern matching exhaustiveness checking as described by Maranget [0].
   [0] http://pauillac.inria.fr/~maranget/papers/warn/index.html *)

(* describes pattern constructor type and its arity if non-zero *)
type cons =
  As | Tuple of int | Record of int | Variant of (C.label * bool) | Const of C.const | Wildcard

let cons_of_pattern p = match fst p with
  | P.As _ -> As
  | P.Tuple lst -> Tuple (List.length lst)
  | P.Record lst -> Record (List.length lst)
  | P.Variant (lbl, opt) -> Variant (lbl, opt != None)
  | P.Const c -> Const c
  | P.Var _ | P.Nonbinding -> Wildcard

(* number of subpatterns required by a pattern constructor *)
let arity = function
  | Const _ | Wildcard -> 0
  | As -> 1
  | Tuple n | Record n -> n
  | Variant (_, b) -> if b then 1 else 0

(* returns a pair with the first value true iff the first column of pattern
   matrix [p] contains the complete type signature, and the list of distinct
   root constructors as the second value *)
let find_constructors p tctx =
  let rec filter column = match column with
    | [] -> []
    | pat :: pats -> begin match cons_of_pattern pat with
        | Wildcard -> filter pats
        | c -> c :: filter pats
      end
  in
  let lst = C.uniq (filter (List.map List.hd p)) in
    if List.length lst = 0 then
      (false, [])
    else
      match List.hd lst with
        (* tuple, record and as patterns have only one constructor *)
        | Tuple _ | Record _ | As -> (true, lst)
        (* floats, strings and integers have infinite constructors *)
        | Const (C.Float _ | C.String _ | C.Integer _) -> (false, lst)
        (* booleans have two distinct constructors *)
        | Const (C.Boolean _) -> (List.length lst = 2, lst)
        (* for variants, check if all labels are covered *)
        | Variant (lbl, _) -> begin match Ctx.find_variant lbl tctx with
            | None -> assert false
            | Some v -> begin match Ctx.find_variant_tags v tctx with
                | None -> assert false
                | Some tags -> (List.length lst = List.length tags, lst)
              end
          end
        | _ -> (false, lst)

(* returns a specialized row from [p_row] for pattern constructor [con] *)
let spec_row con p_row = match p_row with
  | [] -> assert false
  | p1 :: lst ->
      begin match con, fst p1 with
        | As, P.As (p,_) -> Some (p :: lst)
        | Tuple _, P.Tuple l -> Some (l @ lst)
	(* TODO record *)
        | Variant (lbl, _), P.Variant (lbl', opt) when lbl = lbl' ->
            begin match opt with
              | Some p -> Some (p :: lst)
              | None -> Some lst
            end
        | Const c, P.Const c' when C.equal_const c c' -> Some lst
        | _, (P.Nonbinding | P.Var _) ->
            let rec make_wildcard_list n =
              if n = 0 then
                []
              else
                (P.Nonbinding, C.Nowhere) :: make_wildcard_list (n - 1)
            in
            Some ((make_wildcard_list (arity con)) @ lst)
        | _ -> None
      end

(* return rows where the first pattern constructor matches [con] or wildcard *)
let rec specialize con p = match p with
  | [] -> []
  | row :: lst ->
      begin match spec_row con row with
        | Some row' -> row' :: (specialize con lst)
        | None -> (specialize con lst)
      end

(* return rows where the first pattern constructor is a wildcard *)
let rec default p = match p with
  | [] -> []
  | row :: lst ->
      begin match row with
        | ((P.Nonbinding | P.Var _), _) :: ps -> ps :: (default lst)
        | _ -> default lst
      end

(* is pattern vector [q] useful w.r.t. pattern matrix [p]? *)
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
              begin match spec_row c q with
                | None -> assert false
                | Some q' -> useful (specialize c p) q' tctx
              end
          (* wildcard pattern *)
          | Wildcard ->
              let (complete_sig, cons_lst) = find_constructors p tctx in
              if complete_sig then
                List.exists (fun x -> match (spec_row x q) with
                                        | None -> false
                                        | Some q' -> useful (specialize x p) q' tctx)
                            cons_lst
              else
                useful (default p) qs tctx
        end

(* checks the list of patterns [pats] of same type for exhaustiveness and unused
   patterns *)
let check_pats pats tctx =
  let rec check p pats =
    match pats with
      | [] ->
          if useful p [(P.Nonbinding, C.Nowhere)] tctx then
            Print.warning "This pattern-matching is not exhaustive."
          else
            ()
      | (_, pos) as pat :: pats ->
          if not (useful p [pat] tctx) then
            begin
              Print.warning ~pos:pos "This match case is unused.";
              check p pats
            end
          else
            check ([pat] :: p) pats (* wrong order, but still correct result *)
  in
    check [] pats
