(* Generates dune rules for each [.eff] file *)
(* Taken from https://github.com/mirage/alcotest/blob/master/test/e2e/gen_dune_rules.ml *)

let src_suffix = ".eff"

let test_script = "regression_test"

let skip = []

let global_stanza _files =
  Printf.printf "(executables\n";
  Printf.printf " (names %s)\n" test_script;
  Printf.printf " (libraries eff_core)\n";
  Printf.printf " (modules %s)\n" test_script;
  Printf.printf ")\n";
  Printf.printf "\n"

let test_case_rule_stanza (_bare, full_name) =
  Printf.printf "(rule\n";
  Printf.printf " (deps\n";
  Printf.printf "  (source_tree .))\n";
  Printf.printf "   (target %s.out)\n" full_name;
  Printf.printf "    (action\n";
  Printf.printf "     (with-outputs-to %%{target}\n";
  Printf.printf "      (with-accepted-exit-codes\n";
  Printf.printf "       0\n";
  Printf.printf "       (run %%{dep:%s.exe} ./%s)))))\n\n" test_script full_name

let test_case_alias_stanza (_bare, full_name) =
  Printf.printf "(rule\n";
  Printf.printf " (alias runtest)\n";
  Printf.printf "  (action\n";
  Printf.printf "   (diff %s.ref %s.out)))\n\n" full_name full_name

let main () =
  Sys.readdir "." |> Array.to_list |> List.sort String.compare
  |> List.filter_map (fun full_name ->
         Option.map
           (fun bare -> (bare, full_name))
           (Filename.chop_suffix_opt ~suffix:src_suffix full_name))
  |> List.filter (fun (_, full_name) -> List.mem full_name skip |> not)
  |> function
  | [] -> () (* no tests to execute *)
  | tests ->
      global_stanza tests;
      List.iter
        (fun test ->
          test_case_rule_stanza test;
          test_case_alias_stanza test)
        tests

let () = main ()
