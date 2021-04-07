let names =
  [ "loop"; "queens"; "interp"; "range"; "tree"; "capability_benchmarks" ]

let invalid = [] (*  ("loop", "NoOptImpure") ] *)

let default_args = "--no-stdlib --compile-plain-ocaml"

let modes = [ ("", "Opt") ]

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

let format_stanza out_filename =
  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s.out\")\n" out_filename;
  Printf.printf "  (target \"%s.formatted\")\n" out_filename;
  Printf.printf "   (action\n";
  Printf.printf "    (with-outputs-to \"%s.formatted\"\n" out_filename;
  Printf.printf "     (with-accepted-exit-codes (or 0 1 2)\n";
  Printf.printf "      (run ocamlformat %s.out)))))\n\n" out_filename

let benchmark_case_alias_stanza out_filename out_filename_full =
  Printf.printf "(rule\n";
  Printf.printf " (deps %s.formatted)\n" out_filename;
  Printf.printf "  (alias generate_benchmarks)\n";
  Printf.printf "   (action\n";
  Printf.printf "    (diff \"%s.ml\" \"%s.formatted\")))\n\n" out_filename_full
    out_filename

let main () =
  List.iter
    (fun in_file_name ->
      List.iter
        (fun (args, name) ->
          if not (List.mem (in_file_name, name) invalid) then (
            let out_filename = in_file_name ^ name in
            let target_filename = in_file_name ^ name in
            benchmark_case_stanza (in_file_name ^ ".eff") args target_filename;

            format_stanza target_filename;
            benchmark_case_alias_stanza target_filename out_filename))
        modes)
    names

let () = main ()
