effect Fail : (unit -> int)

let rec loop_latent n =
 if n = 0 then
     perform Fail ()
 else if n < 0 then
     perform Fail ()
 else
     loop_latent (n - 1)

let test_latent n =
 loop_latent n;;

let test_once () =
    match (test_latent 10000) with
        | x -> x
        | effect Fail k ->
            continue k (fun () -> 0);;

let rec test_many n =
    if n = 0 then
        ()
    else
        let a = test_once () in
        test_many (n - 1 + a);;

test_many 10000000
