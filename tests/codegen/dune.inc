(rule
 (deps
  "../../ocamlHeader/ocamlHeader.ml")
   (target ocaml_header.tmp)
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run cat "../../ocamlHeader/ocamlHeader.ml")))))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "application_red.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./application_red.eff")))))

(rule
 (deps "application_red.eff.out")
 (target "application_red.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat application_red.eff.out)))))

(rule
 (deps "application_red.eff.out.formatted" ocaml_header.tmp)
 (target "application_red.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - application_red.eff.out.formatted)))))

(rule
 (deps "application_red.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "application_red.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "application_red.eff.out.formatted")
  (alias runtest)
   (action
    (diff "application_red.eff.ref" "application_red.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "break-split.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./break-split.eff")))))

(rule
 (deps "break-split.eff.out")
 (target "break-split.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat break-split.eff.out)))))

(rule
 (deps "break-split.eff.out.formatted" ocaml_header.tmp)
 (target "break-split.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - break-split.eff.out.formatted)))))

(rule
 (deps "break-split.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "break-split.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "break-split.eff.out.formatted")
  (alias runtest)
   (action
    (diff "break-split.eff.ref" "break-split.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "constant_folding_match.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./constant_folding_match.eff")))))

(rule
 (deps "constant_folding_match.eff.out")
 (target "constant_folding_match.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat constant_folding_match.eff.out)))))

(rule
 (deps "constant_folding_match.eff.out.formatted" ocaml_header.tmp)
 (target "constant_folding_match.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - constant_folding_match.eff.out.formatted)))))

(rule
 (deps "constant_folding_match.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "constant_folding_match.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "constant_folding_match.eff.out.formatted")
  (alias runtest)
   (action
    (diff "constant_folding_match.eff.ref" "constant_folding_match.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "handle_match.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./handle_match.eff")))))

(rule
 (deps "handle_match.eff.out")
 (target "handle_match.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat handle_match.eff.out)))))

(rule
 (deps "handle_match.eff.out.formatted" ocaml_header.tmp)
 (target "handle_match.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - handle_match.eff.out.formatted)))))

(rule
 (deps "handle_match.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "handle_match.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "handle_match.eff.out.formatted")
  (alias runtest)
   (action
    (diff "handle_match.eff.ref" "handle_match.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "handle_rec.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./handle_rec.eff")))))

(rule
 (deps "handle_rec.eff.out")
 (target "handle_rec.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat handle_rec.eff.out)))))

(rule
 (deps "handle_rec.eff.out.formatted" ocaml_header.tmp)
 (target "handle_rec.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - handle_rec.eff.out.formatted)))))

(rule
 (deps "handle_rec.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "handle_rec.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "handle_rec.eff.out.formatted")
  (alias runtest)
   (action
    (diff "handle_rec.eff.ref" "handle_rec.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "handler_beta_reduction.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./handler_beta_reduction.eff")))))

(rule
 (deps "handler_beta_reduction.eff.out")
 (target "handler_beta_reduction.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat handler_beta_reduction.eff.out)))))

(rule
 (deps "handler_beta_reduction.eff.out.formatted" ocaml_header.tmp)
 (target "handler_beta_reduction.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - handler_beta_reduction.eff.out.formatted)))))

(rule
 (deps "handler_beta_reduction.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "handler_beta_reduction.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "handler_beta_reduction.eff.out.formatted")
  (alias runtest)
   (action
    (diff "handler_beta_reduction.eff.ref" "handler_beta_reduction.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "ifthenelse.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./ifthenelse.eff")))))

(rule
 (deps "ifthenelse.eff.out")
 (target "ifthenelse.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat ifthenelse.eff.out)))))

(rule
 (deps "ifthenelse.eff.out.formatted" ocaml_header.tmp)
 (target "ifthenelse.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - ifthenelse.eff.out.formatted)))))

(rule
 (deps "ifthenelse.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "ifthenelse.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "ifthenelse.eff.out.formatted")
  (alias runtest)
   (action
    (diff "ifthenelse.eff.ref" "ifthenelse.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "is_relatively_pure.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./is_relatively_pure.eff")))))

(rule
 (deps "is_relatively_pure.eff.out")
 (target "is_relatively_pure.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat is_relatively_pure.eff.out)))))

(rule
 (deps "is_relatively_pure.eff.out.formatted" ocaml_header.tmp)
 (target "is_relatively_pure.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - is_relatively_pure.eff.out.formatted)))))

(rule
 (deps "is_relatively_pure.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "is_relatively_pure.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "is_relatively_pure.eff.out.formatted")
  (alias runtest)
   (action
    (diff "is_relatively_pure.eff.ref" "is_relatively_pure.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "let_list_to_bind.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./let_list_to_bind.eff")))))

(rule
 (deps "let_list_to_bind.eff.out")
 (target "let_list_to_bind.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat let_list_to_bind.eff.out)))))

(rule
 (deps "let_list_to_bind.eff.out.formatted" ocaml_header.tmp)
 (target "let_list_to_bind.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - let_list_to_bind.eff.out.formatted)))))

(rule
 (deps "let_list_to_bind.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "let_list_to_bind.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "let_list_to_bind.eff.out.formatted")
  (alias runtest)
   (action
    (diff "let_list_to_bind.eff.ref" "let_list_to_bind.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "match_red.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./match_red.eff")))))

(rule
 (deps "match_red.eff.out")
 (target "match_red.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat match_red.eff.out)))))

(rule
 (deps "match_red.eff.out.formatted" ocaml_header.tmp)
 (target "match_red.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - match_red.eff.out.formatted)))))

(rule
 (deps "match_red.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "match_red.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "match_red.eff.out.formatted")
  (alias runtest)
   (action
    (diff "match_red.eff.ref" "match_red.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "nested_handlers.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./nested_handlers.eff")))))

(rule
 (deps "nested_handlers.eff.out")
 (target "nested_handlers.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat nested_handlers.eff.out)))))

(rule
 (deps "nested_handlers.eff.out.formatted" ocaml_header.tmp)
 (target "nested_handlers.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - nested_handlers.eff.out.formatted)))))

(rule
 (deps "nested_handlers.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "nested_handlers.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "nested_handlers.eff.out.formatted")
  (alias runtest)
   (action
    (diff "nested_handlers.eff.ref" "nested_handlers.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "norec.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./norec.eff")))))

(rule
 (deps "norec.eff.out")
 (target "norec.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat norec.eff.out)))))

(rule
 (deps "norec.eff.out.formatted" ocaml_header.tmp)
 (target "norec.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - norec.eff.out.formatted)))))

(rule
 (deps "norec.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "norec.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "norec.eff.out.formatted")
  (alias runtest)
   (action
    (diff "norec.eff.ref" "norec.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "not-found.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./not-found.eff")))))

(rule
 (deps "not-found.eff.out")
 (target "not-found.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat not-found.eff.out)))))

(rule
 (deps "not-found.eff.out.formatted" ocaml_header.tmp)
 (target "not-found.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - not-found.eff.out.formatted)))))

(rule
 (deps "not-found.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "not-found.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "not-found.eff.out.formatted")
  (alias runtest)
   (action
    (diff "not-found.eff.ref" "not-found.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "one_input.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./one_input.eff")))))

(rule
 (deps "one_input.eff.out")
 (target "one_input.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat one_input.eff.out)))))

(rule
 (deps "one_input.eff.out.formatted" ocaml_header.tmp)
 (target "one_input.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - one_input.eff.out.formatted)))))

(rule
 (deps "one_input.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "one_input.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "one_input.eff.out.formatted")
  (alias runtest)
   (action
    (diff "one_input.eff.ref" "one_input.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "optimize_pattern_match.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./optimize_pattern_match.eff")))))

(rule
 (deps "optimize_pattern_match.eff.out")
 (target "optimize_pattern_match.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat optimize_pattern_match.eff.out)))))

(rule
 (deps "optimize_pattern_match.eff.out.formatted" ocaml_header.tmp)
 (target "optimize_pattern_match.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - optimize_pattern_match.eff.out.formatted)))))

(rule
 (deps "optimize_pattern_match.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "optimize_pattern_match.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "optimize_pattern_match.eff.out.formatted")
  (alias runtest)
   (action
    (diff "optimize_pattern_match.eff.ref" "optimize_pattern_match.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "optimize_short_circuit.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./optimize_short_circuit.eff")))))

(rule
 (deps "optimize_short_circuit.eff.out")
 (target "optimize_short_circuit.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat optimize_short_circuit.eff.out)))))

(rule
 (deps "optimize_short_circuit.eff.out.formatted" ocaml_header.tmp)
 (target "optimize_short_circuit.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - optimize_short_circuit.eff.out.formatted)))))

(rule
 (deps "optimize_short_circuit.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "optimize_short_circuit.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "optimize_short_circuit.eff.out.formatted")
  (alias runtest)
   (action
    (diff "optimize_short_circuit.eff.ref" "optimize_short_circuit.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "original.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./original.eff")))))

(rule
 (deps "original.eff.out")
 (target "original.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat original.eff.out)))))

(rule
 (deps "original.eff.out.formatted" ocaml_header.tmp)
 (target "original.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - original.eff.out.formatted)))))

(rule
 (deps "original.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "original.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "original.eff.out.formatted")
  (alias runtest)
   (action
    (diff "original.eff.ref" "original.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "other-effect.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./other-effect.eff")))))

(rule
 (deps "other-effect.eff.out")
 (target "other-effect.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat other-effect.eff.out)))))

(rule
 (deps "other-effect.eff.out.formatted" ocaml_header.tmp)
 (target "other-effect.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - other-effect.eff.out.formatted)))))

(rule
 (deps "other-effect.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "other-effect.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "other-effect.eff.out.formatted")
  (alias runtest)
   (action
    (diff "other-effect.eff.ref" "other-effect.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "pm-1_fails.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./pm-1_fails.eff")))))

(rule
 (deps "pm-1_fails.eff.out")
 (target "pm-1_fails.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat pm-1_fails.eff.out)))))

(rule
 (deps "pm-1_fails.eff.out.formatted" ocaml_header.tmp)
 (target "pm-1_fails.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - pm-1_fails.eff.out.formatted)))))

(rule
 (deps "pm-1_fails.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "pm-1_fails.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "pm-1_fails.eff.out.formatted")
  (alias runtest)
   (action
    (diff "pm-1_fails.eff.ref" "pm-1_fails.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "pm-2_passes.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./pm-2_passes.eff")))))

(rule
 (deps "pm-2_passes.eff.out")
 (target "pm-2_passes.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat pm-2_passes.eff.out)))))

(rule
 (deps "pm-2_passes.eff.out.formatted" ocaml_header.tmp)
 (target "pm-2_passes.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - pm-2_passes.eff.out.formatted)))))

(rule
 (deps "pm-2_passes.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "pm-2_passes.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "pm-2_passes.eff.out.formatted")
  (alias runtest)
   (action
    (diff "pm-2_passes.eff.ref" "pm-2_passes.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "pm-3_passes.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./pm-3_passes.eff")))))

(rule
 (deps "pm-3_passes.eff.out")
 (target "pm-3_passes.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat pm-3_passes.eff.out)))))

(rule
 (deps "pm-3_passes.eff.out.formatted" ocaml_header.tmp)
 (target "pm-3_passes.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - pm-3_passes.eff.out.formatted)))))

(rule
 (deps "pm-3_passes.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "pm-3_passes.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "pm-3_passes.eff.out.formatted")
  (alias runtest)
   (action
    (diff "pm-3_passes.eff.ref" "pm-3_passes.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rec1.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./rec1.eff")))))

(rule
 (deps "rec1.eff.out")
 (target "rec1.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat rec1.eff.out)))))

(rule
 (deps "rec1.eff.out.formatted" ocaml_header.tmp)
 (target "rec1.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - rec1.eff.out.formatted)))))

(rule
 (deps "rec1.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "rec1.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "rec1.eff.out.formatted")
  (alias runtest)
   (action
    (diff "rec1.eff.ref" "rec1.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rec2.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./rec2.eff")))))

(rule
 (deps "rec2.eff.out")
 (target "rec2.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat rec2.eff.out)))))

(rule
 (deps "rec2.eff.out.formatted" ocaml_header.tmp)
 (target "rec2.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - rec2.eff.out.formatted)))))

(rule
 (deps "rec2.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "rec2.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "rec2.eff.out.formatted")
  (alias runtest)
   (action
    (diff "rec2.eff.ref" "rec2.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "redefine_local.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./redefine_local.eff")))))

(rule
 (deps "redefine_local.eff.out")
 (target "redefine_local.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat redefine_local.eff.out)))))

(rule
 (deps "redefine_local.eff.out.formatted" ocaml_header.tmp)
 (target "redefine_local.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - redefine_local.eff.out.formatted)))))

(rule
 (deps "redefine_local.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "redefine_local.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "redefine_local.eff.out.formatted")
  (alias runtest)
   (action
    (diff "redefine_local.eff.ref" "redefine_local.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "substitution.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./substitution.eff")))))

(rule
 (deps "substitution.eff.out")
 (target "substitution.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat substitution.eff.out)))))

(rule
 (deps "substitution.eff.out.formatted" ocaml_header.tmp)
 (target "substitution.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - substitution.eff.out.formatted)))))

(rule
 (deps "substitution.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "substitution.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "substitution.eff.out.formatted")
  (alias runtest)
   (action
    (diff "substitution.eff.ref" "substitution.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test-handle_effect_skip.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test-handle_effect_skip.eff")))))

(rule
 (deps "test-handle_effect_skip.eff.out")
 (target "test-handle_effect_skip.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test-handle_effect_skip.eff.out)))))

(rule
 (deps "test-handle_effect_skip.eff.out.formatted" ocaml_header.tmp)
 (target "test-handle_effect_skip.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test-handle_effect_skip.eff.out.formatted)))))

(rule
 (deps "test-handle_effect_skip.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test-handle_effect_skip.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test-handle_effect_skip.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test-handle_effect_skip.eff.ref" "test-handle_effect_skip.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test1.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test1.eff")))))

(rule
 (deps "test1.eff.out")
 (target "test1.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test1.eff.out)))))

(rule
 (deps "test1.eff.out.formatted" ocaml_header.tmp)
 (target "test1.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test1.eff.out.formatted)))))

(rule
 (deps "test1.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test1.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test1.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test1.eff.ref" "test1.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test10.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test10.eff")))))

(rule
 (deps "test10.eff.out")
 (target "test10.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test10.eff.out)))))

(rule
 (deps "test10.eff.out.formatted" ocaml_header.tmp)
 (target "test10.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test10.eff.out.formatted)))))

(rule
 (deps "test10.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test10.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test10.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test10.eff.ref" "test10.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test11.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test11.eff")))))

(rule
 (deps "test11.eff.out")
 (target "test11.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test11.eff.out)))))

(rule
 (deps "test11.eff.out.formatted" ocaml_header.tmp)
 (target "test11.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test11.eff.out.formatted)))))

(rule
 (deps "test11.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test11.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test11.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test11.eff.ref" "test11.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test12.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test12.eff")))))

(rule
 (deps "test12.eff.out")
 (target "test12.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test12.eff.out)))))

(rule
 (deps "test12.eff.out.formatted" ocaml_header.tmp)
 (target "test12.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test12.eff.out.formatted)))))

(rule
 (deps "test12.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test12.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test12.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test12.eff.ref" "test12.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test13.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test13.eff")))))

(rule
 (deps "test13.eff.out")
 (target "test13.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test13.eff.out)))))

(rule
 (deps "test13.eff.out.formatted" ocaml_header.tmp)
 (target "test13.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test13.eff.out.formatted)))))

(rule
 (deps "test13.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test13.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test13.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test13.eff.ref" "test13.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test14.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test14.eff")))))

(rule
 (deps "test14.eff.out")
 (target "test14.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test14.eff.out)))))

(rule
 (deps "test14.eff.out.formatted" ocaml_header.tmp)
 (target "test14.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test14.eff.out.formatted)))))

(rule
 (deps "test14.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test14.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test14.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test14.eff.ref" "test14.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test15.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test15.eff")))))

(rule
 (deps "test15.eff.out")
 (target "test15.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test15.eff.out)))))

(rule
 (deps "test15.eff.out.formatted" ocaml_header.tmp)
 (target "test15.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test15.eff.out.formatted)))))

(rule
 (deps "test15.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test15.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test15.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test15.eff.ref" "test15.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test16.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test16.eff")))))

(rule
 (deps "test16.eff.out")
 (target "test16.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test16.eff.out)))))

(rule
 (deps "test16.eff.out.formatted" ocaml_header.tmp)
 (target "test16.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test16.eff.out.formatted)))))

(rule
 (deps "test16.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test16.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test16.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test16.eff.ref" "test16.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test17.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test17.eff")))))

(rule
 (deps "test17.eff.out")
 (target "test17.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test17.eff.out)))))

(rule
 (deps "test17.eff.out.formatted" ocaml_header.tmp)
 (target "test17.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test17.eff.out.formatted)))))

(rule
 (deps "test17.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test17.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test17.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test17.eff.ref" "test17.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test18.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test18.eff")))))

(rule
 (deps "test18.eff.out")
 (target "test18.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test18.eff.out)))))

(rule
 (deps "test18.eff.out.formatted" ocaml_header.tmp)
 (target "test18.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test18.eff.out.formatted)))))

(rule
 (deps "test18.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test18.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test18.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test18.eff.ref" "test18.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test19.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test19.eff")))))

(rule
 (deps "test19.eff.out")
 (target "test19.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test19.eff.out)))))

(rule
 (deps "test19.eff.out.formatted" ocaml_header.tmp)
 (target "test19.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test19.eff.out.formatted)))))

(rule
 (deps "test19.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test19.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test19.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test19.eff.ref" "test19.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test2.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test2.eff")))))

(rule
 (deps "test2.eff.out")
 (target "test2.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test2.eff.out)))))

(rule
 (deps "test2.eff.out.formatted" ocaml_header.tmp)
 (target "test2.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test2.eff.out.formatted)))))

(rule
 (deps "test2.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test2.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test2.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test2.eff.ref" "test2.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test20.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test20.eff")))))

(rule
 (deps "test20.eff.out")
 (target "test20.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test20.eff.out)))))

(rule
 (deps "test20.eff.out.formatted" ocaml_header.tmp)
 (target "test20.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test20.eff.out.formatted)))))

(rule
 (deps "test20.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test20.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test20.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test20.eff.ref" "test20.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test21.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test21.eff")))))

(rule
 (deps "test21.eff.out")
 (target "test21.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test21.eff.out)))))

(rule
 (deps "test21.eff.out.formatted" ocaml_header.tmp)
 (target "test21.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test21.eff.out.formatted)))))

(rule
 (deps "test21.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test21.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test21.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test21.eff.ref" "test21.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test3.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test3.eff")))))

(rule
 (deps "test3.eff.out")
 (target "test3.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test3.eff.out)))))

(rule
 (deps "test3.eff.out.formatted" ocaml_header.tmp)
 (target "test3.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test3.eff.out.formatted)))))

(rule
 (deps "test3.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test3.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test3.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test3.eff.ref" "test3.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test4.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test4.eff")))))

(rule
 (deps "test4.eff.out")
 (target "test4.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test4.eff.out)))))

(rule
 (deps "test4.eff.out.formatted" ocaml_header.tmp)
 (target "test4.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test4.eff.out.formatted)))))

(rule
 (deps "test4.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test4.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test4.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test4.eff.ref" "test4.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test5.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test5.eff")))))

(rule
 (deps "test5.eff.out")
 (target "test5.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test5.eff.out)))))

(rule
 (deps "test5.eff.out.formatted" ocaml_header.tmp)
 (target "test5.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test5.eff.out.formatted)))))

(rule
 (deps "test5.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test5.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test5.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test5.eff.ref" "test5.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test6.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test6.eff")))))

(rule
 (deps "test6.eff.out")
 (target "test6.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test6.eff.out)))))

(rule
 (deps "test6.eff.out.formatted" ocaml_header.tmp)
 (target "test6.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test6.eff.out.formatted)))))

(rule
 (deps "test6.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test6.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test6.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test6.eff.ref" "test6.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test7.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test7.eff")))))

(rule
 (deps "test7.eff.out")
 (target "test7.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test7.eff.out)))))

(rule
 (deps "test7.eff.out.formatted" ocaml_header.tmp)
 (target "test7.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test7.eff.out.formatted)))))

(rule
 (deps "test7.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test7.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test7.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test7.eff.ref" "test7.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test8.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test8.eff")))))

(rule
 (deps "test8.eff.out")
 (target "test8.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test8.eff.out)))))

(rule
 (deps "test8.eff.out.formatted" ocaml_header.tmp)
 (target "test8.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test8.eff.out.formatted)))))

(rule
 (deps "test8.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test8.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test8.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test8.eff.ref" "test8.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test9.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./test9.eff")))))

(rule
 (deps "test9.eff.out")
 (target "test9.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test9.eff.out)))))

(rule
 (deps "test9.eff.out.formatted" ocaml_header.tmp)
 (target "test9.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test9.eff.out.formatted)))))

(rule
 (deps "test9.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test9.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "test9.eff.out.formatted")
  (alias runtest)
   (action
    (diff "test9.eff.ref" "test9.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "top-letrec_fails.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./top-letrec_fails.eff")))))

(rule
 (deps "top-letrec_fails.eff.out")
 (target "top-letrec_fails.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat top-letrec_fails.eff.out)))))

(rule
 (deps "top-letrec_fails.eff.out.formatted" ocaml_header.tmp)
 (target "top-letrec_fails.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - top-letrec_fails.eff.out.formatted)))))

(rule
 (deps "top-letrec_fails.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "top-letrec_fails.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "top-letrec_fails.eff.out.formatted")
  (alias runtest)
   (action
    (diff "top-letrec_fails.eff.ref" "top-letrec_fails.eff.out.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "two_inputs.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-header "./two_inputs.eff")))))

(rule
 (deps "two_inputs.eff.out")
 (target "two_inputs.eff.out.formatted")
  (action
   (with-outputs-to "%{target}"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat two_inputs.eff.out)))))

(rule
 (deps "two_inputs.eff.out.formatted" ocaml_header.tmp)
 (target "two_inputs.eff.out.formatted.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - two_inputs.eff.out.formatted)))))

(rule
 (deps "two_inputs.eff.out.formatted.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "two_inputs.eff.out.formatted.ocaml_with_header"))))

(rule
 (deps "two_inputs.eff.out.formatted")
  (alias runtest)
   (action
    (diff "two_inputs.eff.ref" "two_inputs.eff.out.formatted")))

