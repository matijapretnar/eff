let run n =
  let s = ref n in
  let rec countdown () =
    let i = !s in
    if i = 0 then i
    else (
      s := i - 1;
      countdown ())
  in
  countdown ()

let () = Printf.printf "%d\n" (run (int_of_string Sys.argv.(1)))
