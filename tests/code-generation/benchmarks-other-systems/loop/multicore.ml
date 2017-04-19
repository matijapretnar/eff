effect Fail : (unit -> bool)

let rec loop_latent n =
 if n = 0 then
     perform Fail ()
 else if n < 0 then
     perform Fail ()
 else
     loop_latent (n - 1)

let test_latent n =
 loop_latent n;;

match (test_latent 10000) with
    | x -> x
    | effect Fail k ->
        continue k (fun () -> true);;
