let rec loop0 n a =
    if n = 0 then a
    else loop0 (n - 1) (a+1)

let rec loop1 n a =
    if n = 0 then ()
    else loop1 (n-1) (a+1)

let rec loop2 n a =
    if n = 0 then (a, ())
    else loop2 (n-1) (a+1)

let rec loop3 n a =
    if n = 0 then a
    else loop3 (n-1) a

let rec loopState n a =
    if n = 0 then a
    else loopState (n-1) (a+1)


let loop_w_handler0 n = loop0 n 0
(* let res0 = loop_w_handler0 10;; *)

let loop_w_handler1 n = loop1 n 0
(* let res1 = loop_w_handler1 10;; *)

let loop_w_handler2 n = loop2 n 0
(* let res2 = loop_w_handler2 10;; *)

let loop_w_handler3 n = loop3 n 0
(* let res2 = loop_w_handler3 10;; *)

let loop_w_handler4 n = loopState n 0
(* let res3 = loop_w_handler4 10;; *)
