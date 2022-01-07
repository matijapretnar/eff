(* Code provided by: https://dl.acm.org/doi/10.1145/3408975 *)

(* Primes *)

(** Message-passing parallel prime number generation using Sieve of Eratosthenes **)

(* A message is either a [Stop] signal or a [Candidate] prime number *)
type message = Stop | Candidate of int

let isCandidate = function Candidate x -> true | Stop -> false

let fromCandidate = function
  | Candidate x -> x
  | Stop -> failwith "Attempt to unwrap Stop"

let fromJust = function Some x -> x | _ -> failwith "Attempt to unwrap None"

let isNothing = function None -> true | Some x -> false

let string_of_msg = function
  | Stop -> "Stop"
  | Candidate i -> Printf.sprintf "%d" i

type pid = int
(** Process primitives **)

(** A mailbox is indexed by process ids (PIDs), each process has its own message queue **)
module MMailbox = struct
  module Make (Ord : Map.OrderedType) = struct
    include Map.Make (Ord)

    let empty = empty

    let lookup key mb = try Some (find key mb) with Not_found -> None

    let pop key mb =
      ( (match lookup key mb with
        | Some msg_q ->
            if Queue.is_empty msg_q then None else Some (Queue.pop msg_q)
        | None -> None),
        mb )

    let push key msg mb =
      match lookup key mb with
      | Some msg_q ->
          Queue.push msg msg_q;
          mb
      | None ->
          let msg_q = Queue.create () in
          Queue.push msg msg_q;
          add key msg_q mb
  end
end

module Mailbox = MMailbox.Make (struct
  type t = pid

  let compare = compare
end)

let mailbox = ref Mailbox.empty

let lookup pid =
  let msg, mb = Mailbox.pop pid !mailbox in
  mailbox := mb;
  msg

let pid = ref 0

let run_q = Queue.create ()

let enqueue k = Queue.push k run_q

let dequeue () =
  if Queue.is_empty run_q then fun x k -> k x
    (* Oh oh we need to apply pure here! *)
  else Queue.pop run_q

let handledSieve_generated x0 =
  let x1 = !pid in
  let x2 =
    enqueue (fun x2 k3 ->
        (((let rec f4 x5 k6 k7 =
             if x5 == x0 then (k6 ()) k7
             else
               ((((fun x8 y9 k10 k11 ->
                    let x12 =
                      mailbox :=
                        Mailbox.push (fst (x8, y9)) (snd (x8, y9)) !mailbox
                    in
                    let x13 = enqueue (fun x13 k14 -> (k10 x13) k14) in
                    let x14 = dequeue () in
                    (x14 ()) k11)
                    (1 + x1))
                   (Candidate x5)) (fun a8 k9 -> ((f4 (x5 + 1)) k6) k9))
                 k7
           in
           f4)
            2) (fun a4 k5 ->
             ((((fun x6 y7 k8 k9 ->
                  let x10 =
                    mailbox :=
                      Mailbox.push (fst (x6, y7)) (snd (x6, y7)) !mailbox
                  in
                  let x11 = enqueue (fun x11 k12 -> (k8 x11) k12) in
                  let x12 = dequeue () in
                  (x12 ()) k9)
                  (1 + x1))
                 Stop) (fun a6 k7 ->
                  let x8 = dequeue () in
                  (x8 ()) (fun a9 -> k7 a9)))
               k5))
          k3)
  in
  let x3 = pid := 1 + x1 in
  (((fun x4 k5 k6 ->
      (((let rec f7 x8 k9 k10 =
           (((let rec f11 x12 k13 k14 =
                let x15 = lookup x12 in
                if isNothing x15 then
                  let x16 = enqueue (fun x16 k17 -> ((f11 x12) k13) k17) in
                  let x17 = dequeue () in
                  (x17 ()) k14
                else (k13 (fromJust x15)) k14
              in
              f11)
               x8) (fun a11 k12 ->
                if isCandidate a11 then
                  let x13 = ref None in
                  (((let rec f14 x15 k16 k17 =
                       (((let rec f18 x19 k20 k21 =
                            let x22 = lookup x19 in
                            if isNothing x22 then
                              let x23 =
                                enqueue (fun x23 k24 -> ((f18 x19) k20) k24)
                              in
                              let x24 = dequeue () in
                              (x24 ()) k21
                            else (k20 (fromJust x22)) k21
                          in
                          f18)
                           x8) (fun a18 k19 ->
                            if isCandidate a18 then
                              if fromCandidate a18 mod fromCandidate a11 <> 0
                              then
                                if isNothing !x13 then
                                  let x20 = !pid in
                                  let x21 =
                                    enqueue (fun x21 k22 ->
                                        let x23 = x13 := Some (1 + x20) in
                                        ((((fun x24 y25 k26 k27 ->
                                             let x28 =
                                               mailbox :=
                                                 Mailbox.push
                                                   (fst (x24, y25))
                                                   (snd (x24, y25))
                                                   !mailbox
                                             in
                                             let x29 =
                                               enqueue (fun x29 k30 ->
                                                   (k26 x29) k30)
                                             in
                                             let x30 = dequeue () in
                                             (x30 ()) k27)
                                             (1 + x20))
                                            a18) (fun a24 k25 ->
                                             ((f14 ()) k16) k25))
                                          k22)
                                  in
                                  let x22 = pid := 1 + x20 in
                                  ((f7 !pid) (fun a23 k24 ->
                                       let x25 = dequeue () in
                                       (x25 ()) k24))
                                    k19
                                else
                                  let x20 = !x13 in
                                  ((((fun x21 y22 k23 k24 ->
                                       let x25 =
                                         mailbox :=
                                           Mailbox.push
                                             (fst (x21, y22))
                                             (snd (x21, y22))
                                             !mailbox
                                       in
                                       let x26 =
                                         enqueue (fun x26 k27 -> (k23 x26) k27)
                                       in
                                       let x27 = dequeue () in
                                       (x27 ()) k24)
                                       (fromJust x20))
                                      a18) (fun a21 k22 -> ((f14 ()) k16) k22))
                                    k19
                              else ((f14 ()) k16) k19
                            else if isNothing !x13 then (k16 ()) k19
                            else
                              let x20 = !x13 in
                              ((((fun x21 y22 k23 k24 ->
                                   let x25 =
                                     mailbox :=
                                       Mailbox.push
                                         (fst (x21, y22))
                                         (snd (x21, y22))
                                         !mailbox
                                   in
                                   let x26 =
                                     enqueue (fun x26 k27 -> (k23 x26) k27)
                                   in
                                   let x27 = dequeue () in
                                   (x27 ()) k24)
                                   (fromJust x20))
                                  Stop)
                                 k16)
                                k19))
                         k17
                     in
                     f14)
                      ())
                     k9)
                    k12
                else (k9 ()) k12))
             k10
         in
         f7)
          x4)
         k5)
        k6)
      !pid) (fun a4 k5 ->
       let x6 = dequeue () in
       (x6 ()) k5)) (fun a4 -> a4)

(* Chameneos *)

open Printf

module Color = struct
  type t = Blue | Red | Yellow

  let complement t t' =
    match (t, t') with
    | Blue, Blue -> Blue
    | Blue, Red -> Yellow
    | Blue, Yellow -> Red
    | Red, Blue -> Yellow
    | Red, Red -> Red
    | Red, Yellow -> Blue
    | Yellow, Blue -> Red
    | Yellow, Red -> Blue
    | Yellow, Yellow -> Yellow

  let to_string = function Blue -> "blue" | Red -> "red" | Yellow -> "yellow"

  let all = [ Blue; Red; Yellow ]
end

let spell_int i =
  let spell_char = function
    | '0' -> "zero"
    | '1' -> "one"
    | '2' -> "two"
    | '3' -> "three"
    | '4' -> "four"
    | '5' -> "five"
    | '6' -> "six"
    | '7' -> "seven"
    | '8' -> "eight"
    | '9' -> "nine"
    | x -> failwith "unexpected char"
  in
  let s = string_of_int i in
  String.iter (fun c -> printf " %s" (spell_char c)) s

let print_complements () =
  ListLabels.iter Color.all ~f:(fun c1 ->
      ListLabels.iter Color.all ~f:(fun c2 ->
          printf "%s + %s -> %s\n" (Color.to_string c1) (Color.to_string c2)
            (Color.to_string (Color.complement c1 c2))));
  printf "\n"

type 'a cont = 'a -> unit

let run_q = Queue.create ()

let enqueue k = Queue.push k run_q

let rec dequeue () =
  if Queue.is_empty run_q then fun x -> x else Queue.pop run_q

(** The state of mvar is either [Full v q] filled with value [v] and a queue
    [q] of threads waiting to fill the mvar, or [Empty q], with a queue [q] of
    threads waiting to empty the mvar. *)
type 'a mv_state =
  | Full of 'a * ('a * unit cont) Queue.t
  | Empty of 'a cont Queue.t

let isEmpty = function Empty _ -> true | Full _ -> false

let emptyQueue = function Empty q -> q | Full _ -> failwith "emptyQueue: Full"

let fullQueue = function
  | Full (_, q) -> q
  | Empty _ -> failwith "fullQueue: Empty"

let fullValue = function
  | Full (a, _) -> a
  | Empty _ -> failwith "fullValue: Empty"

type 'a mvar = 'a mv_state ref

let create_empty () = ref (Empty (Queue.create ()))

let create v = ref (Full (v, Queue.create ()))

let rec tabulate' acc f = function
  | 0 -> acc
  | n -> tabulate' (f () :: acc) f (n - 1)

let tabulate f n = ListLabels.rev @@ tabulate' [] f n

type chameneos = Color.t ref

type mp = Nobody of int | Somebody of int * chameneos * chameneos mvar

let isNobody = function Nobody _ -> true | Somebody _ -> false

let nobodyCount = function
  | Nobody n -> n
  | Somebody _ -> failwith "nobodyCount: Somebody"

let somebodyCount = function
  | Somebody (n, _, _) -> n
  | Nobody _ -> failwith "somebodyCount: Nobody"

let somebodyChameneos = function
  | Somebody (_, ch, _) -> ch
  | Nobody _ -> failwith "somebodyChameneos: Nobody"

let somebodyWaker = function
  | Somebody (_, _, w) -> w
  | Nobody _ -> failwith "somebodyWaker: Nobody"

let waker = create_empty ()

let inc ch x i = if x == ch then i + 1 else i

let complement ch ch' =
  let c'' = Color.complement !ch !ch' in
  ch := c'';
  ch' := c''

let colors =
  [
    Color.Blue;
    Color.Red;
    Color.Yellow;
    Color.Red;
    Color.Yellow;
    Color.Blue;
    Color.Red;
    Color.Yellow;
    Color.Red;
    Color.Blue;
  ]

let fins = tabulate create_empty (List.length colors)

let chams = List.map (fun c -> ref c) colors

let print_ns ns =
  ListLabels.iter
    ~f:(fun (n, b) ->
      print_int n;
      spell_int b;
      printf "\n")
    ns

let null = function [] -> true | x :: xs -> false

let handledWork_generated x0 =
  ((fun x1 k2 ->
     let x3 = create (Nobody x1) in
     ((((let rec f4 x5 y6 z7 k8 =
           if null y6 then k8 ()
           else
             ((x5 (List.hd y6)) (List.hd z7)) (fun a9 ->
                 (((f4 x5) (List.tl y6)) (List.tl z7)) k8)
         in
         f4) (fun x4 y5 k6 ->
            let x7 = enqueue (fun x7 -> k6 ()) in
            ((fun x8 k9 ->
               ((((fun x10 y11 z12 k13 ->
                    (((let rec f14 x15 y16 k17 =
                         ((fun x18 k19 ->
                            let x20 = !x18 in
                            if isEmpty x20 then
                              let x21 =
                                (fun x21 -> Queue.push x21 (emptyQueue x20))
                                  (fun x21 -> k19 x21)
                              in
                              let x22 = dequeue () in
                              x22 ()
                            else if Queue.is_empty (fullQueue x20) then
                              let x21 = x18 := Empty (Queue.create ()) in
                              k19 (fullValue x20)
                            else
                              let x21 = Queue.pop (fullQueue x20) in
                              let x22 = x18 := Full (fst x21, fullQueue x20) in
                              let x23 =
                                enqueue (fun x23 ->
                                    (fst (snd x21, ())) (snd (snd x21, ())))
                              in
                              k19 (fullValue x20))
                            x10) (fun a18 ->
                             if isNobody a18 then
                               if nobodyCount a18 == 0 then
                                 (((fun x19 y20 k21 ->
                                     let x22 = !y20 in
                                     if isEmpty x22 then
                                       if Queue.is_empty (emptyQueue x22) then
                                         let x23 =
                                           y20 := Full (x19, Queue.create ())
                                         in
                                         k21 x23
                                       else
                                         let x23 = Queue.pop (emptyQueue x22) in
                                         let x24 =
                                           enqueue (fun x24 ->
                                               (fst (x23, x19)) (snd (x23, x19)))
                                         in
                                         k21 ()
                                     else
                                       let x23 =
                                         (fun x23 ->
                                           Queue.push (x19, x23) (fullQueue x22))
                                           (fun x23 -> k21 x23)
                                       in
                                       let x24 = dequeue () in
                                       x24 ())
                                     a18)
                                    x10) (fun a19 ->
                                     (((fun x20 y21 k22 ->
                                         let x23 = !y21 in
                                         if isEmpty x23 then
                                           if Queue.is_empty (emptyQueue x23)
                                           then
                                             let x24 =
                                               y21 := Full (x20, Queue.create ())
                                             in
                                             k22 x24
                                           else
                                             let x24 =
                                               Queue.pop (emptyQueue x23)
                                             in
                                             let x25 =
                                               enqueue (fun x25 ->
                                                   (fst (x24, x20))
                                                     (snd (x24, x20)))
                                             in
                                             k22 ()
                                         else
                                           let x24 =
                                             (fun x24 ->
                                               Queue.push (x20, x24)
                                                 (fullQueue x23)) (fun x24 ->
                                                 k22 x24)
                                           in
                                           let x25 = dequeue () in
                                           x25 ())
                                         (x15, y16))
                                        y11)
                                       k17)
                               else
                                 (((fun x19 y20 k21 ->
                                     let x22 = !y20 in
                                     if isEmpty x22 then
                                       if Queue.is_empty (emptyQueue x22) then
                                         let x23 =
                                           y20 := Full (x19, Queue.create ())
                                         in
                                         k21 x23
                                       else
                                         let x23 = Queue.pop (emptyQueue x22) in
                                         let x24 =
                                           enqueue (fun x24 ->
                                               (fst (x23, x19)) (snd (x23, x19)))
                                         in
                                         k21 ()
                                     else
                                       let x23 =
                                         (fun x23 ->
                                           Queue.push (x19, x23) (fullQueue x22))
                                           (fun x23 -> k21 x23)
                                       in
                                       let x24 = dequeue () in
                                       x24 ())
                                     (Somebody (nobodyCount a18, z12, waker)))
                                    x10) (fun a19 ->
                                     ((fun x20 k21 ->
                                        let x22 = !x20 in
                                        if isEmpty x22 then
                                          let x23 =
                                            (fun x23 ->
                                              Queue.push x23 (emptyQueue x22))
                                              (fun x23 -> k21 x23)
                                          in
                                          let x24 = dequeue () in
                                          x24 ()
                                        else if Queue.is_empty (fullQueue x22)
                                        then
                                          let x23 =
                                            x20 := Empty (Queue.create ())
                                          in
                                          k21 (fullValue x22)
                                        else
                                          let x23 = Queue.pop (fullQueue x22) in
                                          let x24 =
                                            x20 := Full (fst x23, fullQueue x22)
                                          in
                                          let x25 =
                                            enqueue (fun x25 ->
                                                (fst (snd x23, ()))
                                                  (snd (snd x23, ())))
                                          in
                                          k21 (fullValue x22))
                                        waker) (fun a20 ->
                                         ((f14 (x15 + 1)) (inc z12 a20 y16)) k17))
                             else
                               (((fun x19 y20 k21 ->
                                   let x22 = !y20 in
                                   if isEmpty x22 then
                                     if Queue.is_empty (emptyQueue x22) then
                                       let x23 =
                                         y20 := Full (x19, Queue.create ())
                                       in
                                       k21 x23
                                     else
                                       let x23 = Queue.pop (emptyQueue x22) in
                                       let x24 =
                                         enqueue (fun x24 ->
                                             (fst (x23, x19)) (snd (x23, x19)))
                                       in
                                       k21 ()
                                   else
                                     let x23 =
                                       (fun x23 ->
                                         Queue.push (x19, x23) (fullQueue x22))
                                         (fun x23 -> k21 x23)
                                     in
                                     let x24 = dequeue () in
                                     x24 ())
                                   (Nobody (somebodyCount a18 - 1)))
                                  x10) (fun a19 ->
                                   let x20 =
                                     complement z12 (somebodyChameneos a18)
                                   in
                                   (((fun x21 y22 k23 ->
                                       let x24 = !y22 in
                                       if isEmpty x24 then
                                         if Queue.is_empty (emptyQueue x24) then
                                           let x25 =
                                             y22 := Full (x21, Queue.create ())
                                           in
                                           k23 x25
                                         else
                                           let x25 =
                                             Queue.pop (emptyQueue x24)
                                           in
                                           let x26 =
                                             enqueue (fun x26 ->
                                                 (fst (x25, x21))
                                                   (snd (x25, x21)))
                                           in
                                           k23 ()
                                       else
                                         let x25 =
                                           (fun x25 ->
                                             Queue.push (x21, x25)
                                               (fullQueue x24)) (fun x25 ->
                                               k23 x25)
                                         in
                                         let x26 = dequeue () in
                                         x26 ())
                                       z12)
                                      (somebodyWaker a18)) (fun a21 ->
                                       ((f14 (x15 + 1))
                                          (inc z12 (somebodyChameneos a18) y16))
                                         k17)))
                       in
                       f14)
                        0)
                       0)
                      k13)
                    x3)
                   x4)
                  y5)
                 k9)
               ()) (fun a8 ->
                let x9 = dequeue () in
                x9 ())))
         fins)
        chams) (fun a4 ->
         (((let rec f5 x6 y7 k8 =
              if null y7 then k8 []
              else
                (x6 (List.hd y7)) (fun a9 ->
                    ((f5 x6) (List.tl y7)) (fun a10 -> k8 (a9 :: a10)))
            in
            f5) (fun x5 k6 ->
               let x7 = !x5 in
               if isEmpty x7 then
                 let x8 =
                   (fun x8 -> Queue.push x8 (emptyQueue x7)) (fun x8 -> k6 x8)
                 in
                 let x9 = dequeue () in
                 x9 ()
               else if Queue.is_empty (fullQueue x7) then
                 let x8 = x5 := Empty (Queue.create ()) in
                 k6 (fullValue x7)
               else
                 let x8 = Queue.pop (fullQueue x7) in
                 let x9 = x5 := Full (fst x8, fullQueue x7) in
                 let x10 =
                   enqueue (fun x10 -> (fst (snd x8, ())) (snd (snd x8, ())))
                 in
                 k6 (fullValue x7)))
            fins)
           k2))
     x0) (fun a1 ->
      let x2 = print_ns a1 in
      let x3 = dequeue () in
      let x4 = x3 () in
      x4)

(* Triple *)

let handledTriple_generated x0 y1 =
  ((((fun x2 y3 k4 k5 ->
       (((let rec f6 x7 k8 k9 =
            if x7 < 1 then k9 []
            else
              let x10 = (k8 x7) k9 in
              let x11 = ((f6 (x7 - 1)) k8) k9 in
              List.append x10 x11
          in
          f6)
           x2) (fun a6 k7 ->
            (((let rec f8 x9 k10 k11 =
                 if x9 < 1 then k11 []
                 else
                   let x12 = (k10 x9) k11 in
                   let x13 = ((f8 (x9 - 1)) k10) k11 in
                   List.append x12 x13
               in
               f8)
                (a6 - 1)) (fun a8 k9 ->
                 (((let rec f10 x11 k12 k13 =
                      if x11 < 1 then k13 []
                      else
                        let x14 = (k12 x11) k13 in
                        let x15 = ((f10 (x11 - 1)) k12) k13 in
                        List.append x14 x15
                    in
                    f10)
                     (a8 - 1)) (fun a10 k11 ->
                      if a6 + a8 + a10 == y3 then (k4 (a6, a8, a10)) k11
                      else k11 []))
                   k9))
              k7))
         k5)
       x0)
      y1) (fun a2 k3 -> k3 [ a2 ])) (fun a2 -> a2)

let handleTripleWrap (x, y) = handledTriple_generated x y

(* let _ = handledTriple_generated 100 15 *)

(* Queens *)

let null = function [] -> true | x :: xs -> false

let isNothing = function None -> true | Some x -> false

let fromJust = function None -> failwith "fromJust: None" | Some x -> x

let rec filter p = function
  | [] -> []
  | x :: xs -> if p x then x :: filter p xs else filter p xs

let rec forall p = function
  | [] -> true
  | x :: xs -> if p x then forall p xs else false

let no_attack (x, y) (x', y') =
  x <> x' && y <> y' && abs (x - x') <> abs (y - y')

let available x qs l = filter (fun y -> forall (no_attack (x, y)) qs) l

let handledQueens_generated x0 y1 =
  (((let rec f2 x3 y4 k5 =
       if x3 == y1 + 1 then k5 (Some y4)
       else
         (let rec f6 x7 =
            if null x7 then None
            else
              let x8 = ((f2 (x3 + 1)) ((x3, List.hd x7) :: y4)) k5 in
              if isNothing x8 then f6 (List.tl x7) else Some (fromJust x8)
          in
          f6)
           (available x3 y4 x0)
     in
     f2)
      1)
     []) (fun a2 -> a2)

let findSolution_generated n =
  let l = ref [] in
  for i = n downto 1 do
    l := i :: !l
  done;
  handledQueens_generated !l n

(* Count *)
let handledCount_generated x0 =
  let x1 =
    ((let rec f1 x2 k3 x4 =
        let x5 =
          if x4 == 0 then k3 x4
          else fun x5 ->
            let x6 = (f1 ()) k3 in
            x6 (x4 - 1)
        in
        x5 x4
      in
      f1)
       ()) (fun a1 x2 -> x2)
  in
  x1 x0

(* Generator *)

let handledGenerator_generated x0 =
  let x1 =
    ((((let rec f2 x3 y4 k5 k6 =
          if x3 > y4 then (k5 ()) k6
          else fun x7 ->
            let x8 x9 =
              let x10 = (((f2 (x3 + 1)) y4) k5) k6 in
              x10 (x7 + x3)
            in
            x8 x7
        in
        f2)
         1)
        x0) (fun a2 k3 -> k3 a2)) (fun a2 x3 -> x3)
  in
  x1 0
