(* Generates dune rules for each [.eff] file *)
(* Taken from https://github.com/mirage/alcotest/blob/master/test/e2e/gen_dune_rules.ml *)

let src_suffix = ".eff"

let test_script = "regression_test"

type config = { allowed_exit_code : int; args : string }

let parse_config =
  let l = Array.length Sys.argv in
  let allowed_exit_code = if l >= 2 then int_of_string Sys.argv.(1) else 0 in
  let args = if l >= 3 then Sys.argv.(2) ^ " " else "" in
  { allowed_exit_code; args }

let skip = []

let generate_empty_ref = true

(* Placeholder for future use *)
let global_stanza _files = ()

let test_case_rule_stanza config (_bare, full_name) =
  Printf.printf "(rule\n";
  Printf.printf " (deps\n";
  Printf.printf " %%{bin:eff}\n";
  Printf.printf "  (source_tree .))\n";
  Printf.printf "   (target \"%s.out\")\n" full_name;
  Printf.printf "    (action\n";
  Printf.printf "     (with-outputs-to \"%%{target}\"\n";
  Printf.printf "      (with-accepted-exit-codes\n";
  (* Just for now, ignore exit codes *)
  Printf.printf "       (or %d 0 1 2)\n" config.allowed_exit_code;
  Printf.printf "       (run eff %s\"./%s\")))))\n\n" config.args full_name

let test_case_alias_stanza (_bare, full_name) =
  Printf.printf "(rule\n";
  Printf.printf " (alias runtest)\n";
  Printf.printf "  (action\n";
  Printf.printf "   (diff \"%s.ref\" \"%s.out\")))\n\n" full_name full_name

let main () =
  let config = parse_config in
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
          test_case_rule_stanza config test;
          test_case_alias_stanza test)
        tests

let () = main ()
