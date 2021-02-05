(* Generates dune rules for each [.eff] file *)
(* Taken from https://github.com/mirage/alcotest/blob/master/test/e2e/gen_dune_rules.ml *)

let src_suffix = ".eff"

let test_script = "regression_test"

type config = {
  allowed_exit_code : int;
  args : string;
  apply_ocamlformat : bool;
  generate_ocaml_compile_rule : bool;
}

let parse_config =
  let l = Array.length Sys.argv in
  let allowed_exit_code = if l >= 2 then int_of_string Sys.argv.(1) else 0 in
  let args = if l >= 3 then Sys.argv.(2) ^ " " else "" in
  let apply_ocamlformat =
    if l >= 4 then 1 = int_of_string Sys.argv.(3) else false
  in
  let generate_ocaml_compile_rule =
    if l >= 5 then 1 = int_of_string Sys.argv.(4) else false
  in
  { allowed_exit_code; args; apply_ocamlformat; generate_ocaml_compile_rule }

let skip = []

let generate_empty_ref = true

let global_stanza _files config =
  if config.generate_ocaml_compile_rule then (
    Printf.printf "(rule\n";
    Printf.printf " (deps\n";
    Printf.printf "  \"../../ocamlHeader/ocamlHeader.ml\")\n";
    Printf.printf "   (target ocaml_header.tmp)\n";
    Printf.printf "    (action\n";
    Printf.printf "     (with-outputs-to \"%%{target}\"\n";
    Printf.printf "      (with-accepted-exit-codes\n";
    Printf.printf "       0\n";
    Printf.printf
      "       (run cat \"../../ocamlHeader/ocamlHeader.ml\")))))\n\n")

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

let format_stanza out_filename =
  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s.out\")\n" out_filename;
  Printf.printf " (target \"%s.formatted\")\n" out_filename;
  Printf.printf "  (action\n";
  Printf.printf "   (with-outputs-to \"%s.formatted\"\n" out_filename;
  Printf.printf "    (with-accepted-exit-codes (or 0 1 2)\n";
  Printf.printf "     (run ocamlformat %s.out)))))\n\n" out_filename;

  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s.formatted\")\n" out_filename;
  Printf.printf "  (alias runtest)\n";
  Printf.printf "   (action\n";
  Printf.printf "    (diff \"%s.ref.formatted\" \"%s.formatted\")))\n\n"
    out_filename out_filename

let ocaml_compile_rule full_name out_filename =
  (* Combined file*)
  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s\" ocaml_header.tmp)\n" out_filename;
  Printf.printf " (target \"%s.ocaml_with_header\")\n" out_filename;
  Printf.printf "  (action\n";
  Printf.printf "   (with-outputs-to \"%%{target}\"\n";
  Printf.printf
    "    (pipe-outputs (run echo \";;\") (run cat ocaml_header.tmp - %s)))))\n\n"
    out_filename;

  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s.ocaml_with_header\")\n" out_filename;
  Printf.printf " (target \"%s.ocaml_output\")\n" out_filename;
  Printf.printf "  (action\n";
  Printf.printf "   (with-outputs-to \"%s.ocaml_output\"\n" out_filename;
  Printf.printf "    (with-accepted-exit-codes (or 0 1 2)\n";
  Printf.printf "     (run ocaml \"%s.ocaml_with_header\")))))\n\n" out_filename;

  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s.ocaml_output\")\n" out_filename;
  Printf.printf "  (alias runtest)\n";
  Printf.printf "   (action\n";
  Printf.printf "    (diff \"%s.ref.ocaml_output\" \"%s.ocaml_output\")))\n\n"
    full_name out_filename

let test_case_alias_stanza config (_bare, full_name) =
  let out_file_name = full_name ^ ".out" in
  if config.apply_ocamlformat then format_stanza full_name;
  if config.generate_ocaml_compile_rule then
    ocaml_compile_rule full_name out_file_name;
  Printf.printf "(rule\n";
  Printf.printf " (deps \"%s\")\n" out_file_name;
  Printf.printf "  (alias runtest)\n";
  Printf.printf "   (action\n";
  Printf.printf "    (diff \"%s.ref\" \"%s\")))\n\n" full_name out_file_name

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
      global_stanza tests config;
      List.iter
        (fun test ->
          test_case_rule_stanza config test;
          test_case_alias_stanza config test)
        tests

let () = main ()
