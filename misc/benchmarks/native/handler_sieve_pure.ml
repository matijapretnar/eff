(* [primes] holds the primes found so far, the latest first, which is the
   order in which the nested handlers test them. *)
let rec run i n primes a =
  if i >= n then a
  else if List.for_all (fun p -> i mod p <> 0) primes then
    run (i + 1) n (i :: primes) (a + i)
  else run (i + 1) n primes a

let () = Printf.printf "%d\n" (run 2 (int_of_string Sys.argv.(1)) [] 0)
