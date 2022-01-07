(***********************************
*********** The Parser *************
***********************************)

exception Fail

(********************************
* Handlers
********************************)

(* let parse = handler
    | val y -> (fun s ->
        begin match s with
        | [] -> y
        | _ -> absurd (#Fail ())
        end
    )
    | #Symbol c k ->
        fun s ->
        (begin match s with
            | [] -> k (fun () -> (absurd (#Fail ()))) []
            | (x :: xs) -> if (c = x) then k (fun () -> x) xs else k (fun () -> (absurd (#Fail ()))) s
        end
        )
;;

let allsols = handler
  | val x -> [x]
  | #Decide _ k -> k true @ k false
  | #Fail _ _ -> []
;;
 *)
(********************************
* Parser :: string list to int
********************************)

let createNumber (prev, num) = (prev * 10) + num

let rec parseNum (l, v) =
  match l with
  | [] -> v
  | Some x :: xs -> (
      match x with
      | "0" -> parseNum (xs, createNumber (v, 0))
      | "1" -> parseNum (xs, createNumber (v, 1))
      | "2" -> parseNum (xs, createNumber (v, 2))
      | "3" -> parseNum (xs, createNumber (v, 3))
      | "4" -> parseNum (xs, createNumber (v, 4))
      | "5" -> parseNum (xs, createNumber (v, 5))
      | "6" -> parseNum (xs, createNumber (v, 6))
      | "7" -> parseNum (xs, createNumber (v, 7))
      | "8" -> parseNum (xs, createNumber (v, 8))
      | "9" -> parseNum (xs, createNumber (v, 9)))

let rec toNum l = parseNum (l, 0)

(********************************
* Parser :: FAIL
********************************)

(* | [] -> raise Fail
| y :: ys ->
    begin try place (x + 1) ((x, y) :: qs) with
    | Fail -> choose ys
    end

let digit d =
let nums = ["0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9"] in
let rec checkNums n =
    begin match n with
    | [] -> raise Fail
    | (x :: xs) ->
        begin try get_symbol x d with
        | Fail -> checkNums xs
        end
        let (c, d2) = get_symbol x d in
        begin match (c) with
          | Some qs -> (c, d2)
          | None -> checkNums xs
        end
    end in
checkNums nums
;; *)

(********************************
* Parser :: OPTION
********************************)

let get_symbol c d =
  match d with
  | [] -> (None, [])
  | x :: xs -> if c = x then (Some x, xs) else (None, d)

let digit d =
  let nums = [ "0"; "1"; "2"; "3"; "4"; "5"; "6"; "7"; "8"; "9" ] in
  let rec checkNums n =
    match n with
    | [] -> (None, d)
    | x :: xs -> (
        let c, d2 = get_symbol x d in
        match c with Some qs -> (c, d2) | None -> checkNums xs)
  in
  checkNums nums

let rec many m d = m d

let rec many1 d =
  let x, d2 = digit d in
  match x with
  | None -> ([], d2)
  | _ ->
      let xs, d3 = many many1 d2 in
      ([ x ] @ xs, d3)

let solve n1 n2 p =
  match n1 with
  | [] -> []
  | _ -> (
      match n2 with
      | [] -> []
      | _ -> (
          match p with
          | None -> []
          | Some "+" -> [ toNum n1 + toNum n2 ]
          | Some "*" -> [ toNum n1 * toNum n2 ]))

let choose l = match l with [], _ -> [] | l1, [] -> l1 | l1, _ -> []

let rec expr d =
  let rec term dt =
    let rec factor df =
      let i, df1 = many1 df in
      let res = match i with [] -> [] | _ -> [ (toNum i, df1) ] in
      let p, df2 = get_symbol "(" df in
      match p with
      | None -> res
      | _ -> (
          let e1 = expr df2 in
          match e1 with
          | [] -> res
          | (a, b) :: xs -> (
              let p, df2 = get_symbol ")" b in
              match p with None -> res | _ -> [ (a, df2) ]))
    in
    let r = factor dt in
    let res = match r with [] -> [] | _ -> r in
    let r2 = factor dt in
    match r2 with
    | [] -> res
    | (r2a, r2b) :: xs -> (
        let p, dt1 = get_symbol "*" r2b in
        match p with
        | None -> res
        | _ -> (
            let r3 = term dt1 in
            match r3 with [] -> res | (r3a, r3b) :: xs -> [ (r2a * r3a, r3b) ]))
  in
  let t2 = term d in
  match t2 with
  | [] -> []
  | (a, b) :: xs -> (
      match b with
      | [] -> [ (a, b) ]
      | _ -> (
          let t1 = term d in
          match t1 with
          | [] -> [ (a, b) ]
          | (a1, b1) :: xs -> (
              let p, d1 = get_symbol "+" b1 in
              match p with
              | None -> [ (a, b) ]
              | _ -> (
                  let e1 = expr d1 in
                  match e1 with
                  | [] -> [ (a, b) ]
                  | (a2, b2) :: xs -> [ (a1 + a2, b2) ]))))

(********************************
* Example
********************************)

(* expr ["2"; "+"; "4"; "3"; "*"; "("; "3"; "+"; "3"; ")"];;
expr ["4"; "5"; "+"];; *)
let parseTest () = expr [ "4"; "3"; "*"; "("; "3"; "+"; "3"; ")" ]
