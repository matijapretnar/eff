let names = [ "loop"; "queens"; "interp"; "range" ]

let default_args = "--no-stdlib --compile-plain-ocaml"

let modes =
  [
    ("--pure", "OptPure");
    ("--pure --no-opt", "NoOptPure");
    ("", "OptImpure");
    ("--no-opt", "NoOptImpure");
  ]

let benchmark_case_stanza in_filename args out_filename =
  Printf.printf "(rule\n";
  Printf.printf " (deps\n";
  Printf.printf " %%{bin:eff}\n";
  Printf.printf "  (source_tree .))\n";
  Printf.printf "   (target \"%s.out\")\n" out_filename;
  Printf.printf "    (action\n";
  Printf.printf "     (with-outputs-to \"%%{target}\"\n";
  Printf.printf "      (with-accepted-exit-codes\n";
  (* Just for now, ignore exit codes *)
  Printf.printf "       (or 0 1 2)\n";
  Printf.printf "       (run eff %s %s \"./%s\")))))\n\n" default_args args
    in_filename

let benchmark_case_alias_stanza out_filename =
  Printf.printf "(rule\n";
  Printf.printf " (alias generate_benchmarks)\n";
  Printf.printf "  (action\n";
  Printf.printf "   (diff \"%s.ml\" \"%s.out\")))\n\n" out_filename out_filename

let main () =
  List.iter
    (fun in_file_name ->
      List.iter
        (fun (args, name) ->
          let out_filename = in_file_name ^ "/" ^ in_file_name ^ name in
          benchmark_case_stanza
            (in_file_name ^ "/" ^ in_file_name ^ ".eff")
            args out_filename;
          benchmark_case_alias_stanza out_filename)
        modes)
    names

let () = main ()
