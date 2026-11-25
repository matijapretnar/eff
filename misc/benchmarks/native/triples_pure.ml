let hash a b c = ((53 * a) + (2809 * b) + (148877 * c)) mod 1000000007

let run n s =
  let rec loop_i i a =
    if i < 1 then a
    else
      let rec loop_j j a =
        if j < 1 then a
        else
          let rec loop_k k a =
            if k < 1 then a
            else
              let a =
                if i + j + k = s then (a + hash i j k) mod 1000000007 else a
              in
              loop_k (k - 1) a
          in
          loop_j (j - 1) (loop_k (j - 1) a)
      in
      loop_i (i - 1) (loop_j (i - 1) a)
  in
  loop_i n 0

let () =
  let n = int_of_string Sys.argv.(1) in
  Printf.printf "%d\n" (run n n)
