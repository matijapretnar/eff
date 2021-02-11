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
 (target "application_red.eff.formatted")
  (action
   (with-outputs-to "application_red.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat application_red.eff.out)))))

(rule
 (deps "application_red.eff.formatted")
  (alias runtest)
   (action
    (diff "application_red.eff.ref.formatted" "application_red.eff.formatted")))

(rule
 (deps "application_red.eff.out" ocaml_header.tmp)
 (target "application_red.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - application_red.eff.out)))))

(rule
 (deps "application_red.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "application_red.eff.out.ocaml_with_header"))))

(rule
 (deps "application_red.eff.out")
  (alias runtest)
   (action
    (diff "application_red.eff.ref" "application_red.eff.out")))

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
 (target "break-split.eff.formatted")
  (action
   (with-outputs-to "break-split.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat break-split.eff.out)))))

(rule
 (deps "break-split.eff.formatted")
  (alias runtest)
   (action
    (diff "break-split.eff.ref.formatted" "break-split.eff.formatted")))

(rule
 (deps "break-split.eff.out" ocaml_header.tmp)
 (target "break-split.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - break-split.eff.out)))))

(rule
 (deps "break-split.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "break-split.eff.out.ocaml_with_header"))))

(rule
 (deps "break-split.eff.out")
  (alias runtest)
   (action
    (diff "break-split.eff.ref" "break-split.eff.out")))

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
 (target "handle_match.eff.formatted")
  (action
   (with-outputs-to "handle_match.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat handle_match.eff.out)))))

(rule
 (deps "handle_match.eff.formatted")
  (alias runtest)
   (action
    (diff "handle_match.eff.ref.formatted" "handle_match.eff.formatted")))

(rule
 (deps "handle_match.eff.out" ocaml_header.tmp)
 (target "handle_match.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - handle_match.eff.out)))))

(rule
 (deps "handle_match.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "handle_match.eff.out.ocaml_with_header"))))

(rule
 (deps "handle_match.eff.out")
  (alias runtest)
   (action
    (diff "handle_match.eff.ref" "handle_match.eff.out")))

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
 (target "handle_rec.eff.formatted")
  (action
   (with-outputs-to "handle_rec.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat handle_rec.eff.out)))))

(rule
 (deps "handle_rec.eff.formatted")
  (alias runtest)
   (action
    (diff "handle_rec.eff.ref.formatted" "handle_rec.eff.formatted")))

(rule
 (deps "handle_rec.eff.out" ocaml_header.tmp)
 (target "handle_rec.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - handle_rec.eff.out)))))

(rule
 (deps "handle_rec.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "handle_rec.eff.out.ocaml_with_header"))))

(rule
 (deps "handle_rec.eff.out")
  (alias runtest)
   (action
    (diff "handle_rec.eff.ref" "handle_rec.eff.out")))

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
 (target "handler_beta_reduction.eff.formatted")
  (action
   (with-outputs-to "handler_beta_reduction.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat handler_beta_reduction.eff.out)))))

(rule
 (deps "handler_beta_reduction.eff.formatted")
  (alias runtest)
   (action
    (diff "handler_beta_reduction.eff.ref.formatted" "handler_beta_reduction.eff.formatted")))

(rule
 (deps "handler_beta_reduction.eff.out" ocaml_header.tmp)
 (target "handler_beta_reduction.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - handler_beta_reduction.eff.out)))))

(rule
 (deps "handler_beta_reduction.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "handler_beta_reduction.eff.out.ocaml_with_header"))))

(rule
 (deps "handler_beta_reduction.eff.out")
  (alias runtest)
   (action
    (diff "handler_beta_reduction.eff.ref" "handler_beta_reduction.eff.out")))

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
 (target "ifthenelse.eff.formatted")
  (action
   (with-outputs-to "ifthenelse.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat ifthenelse.eff.out)))))

(rule
 (deps "ifthenelse.eff.formatted")
  (alias runtest)
   (action
    (diff "ifthenelse.eff.ref.formatted" "ifthenelse.eff.formatted")))

(rule
 (deps "ifthenelse.eff.out" ocaml_header.tmp)
 (target "ifthenelse.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - ifthenelse.eff.out)))))

(rule
 (deps "ifthenelse.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "ifthenelse.eff.out.ocaml_with_header"))))

(rule
 (deps "ifthenelse.eff.out")
  (alias runtest)
   (action
    (diff "ifthenelse.eff.ref" "ifthenelse.eff.out")))

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
 (target "is_relatively_pure.eff.formatted")
  (action
   (with-outputs-to "is_relatively_pure.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat is_relatively_pure.eff.out)))))

(rule
 (deps "is_relatively_pure.eff.formatted")
  (alias runtest)
   (action
    (diff "is_relatively_pure.eff.ref.formatted" "is_relatively_pure.eff.formatted")))

(rule
 (deps "is_relatively_pure.eff.out" ocaml_header.tmp)
 (target "is_relatively_pure.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - is_relatively_pure.eff.out)))))

(rule
 (deps "is_relatively_pure.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "is_relatively_pure.eff.out.ocaml_with_header"))))

(rule
 (deps "is_relatively_pure.eff.out")
  (alias runtest)
   (action
    (diff "is_relatively_pure.eff.ref" "is_relatively_pure.eff.out")))

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
 (target "let_list_to_bind.eff.formatted")
  (action
   (with-outputs-to "let_list_to_bind.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat let_list_to_bind.eff.out)))))

(rule
 (deps "let_list_to_bind.eff.formatted")
  (alias runtest)
   (action
    (diff "let_list_to_bind.eff.ref.formatted" "let_list_to_bind.eff.formatted")))

(rule
 (deps "let_list_to_bind.eff.out" ocaml_header.tmp)
 (target "let_list_to_bind.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - let_list_to_bind.eff.out)))))

(rule
 (deps "let_list_to_bind.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "let_list_to_bind.eff.out.ocaml_with_header"))))

(rule
 (deps "let_list_to_bind.eff.out")
  (alias runtest)
   (action
    (diff "let_list_to_bind.eff.ref" "let_list_to_bind.eff.out")))

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
 (target "match_red.eff.formatted")
  (action
   (with-outputs-to "match_red.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat match_red.eff.out)))))

(rule
 (deps "match_red.eff.formatted")
  (alias runtest)
   (action
    (diff "match_red.eff.ref.formatted" "match_red.eff.formatted")))

(rule
 (deps "match_red.eff.out" ocaml_header.tmp)
 (target "match_red.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - match_red.eff.out)))))

(rule
 (deps "match_red.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "match_red.eff.out.ocaml_with_header"))))

(rule
 (deps "match_red.eff.out")
  (alias runtest)
   (action
    (diff "match_red.eff.ref" "match_red.eff.out")))

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
 (target "norec.eff.formatted")
  (action
   (with-outputs-to "norec.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat norec.eff.out)))))

(rule
 (deps "norec.eff.formatted")
  (alias runtest)
   (action
    (diff "norec.eff.ref.formatted" "norec.eff.formatted")))

(rule
 (deps "norec.eff.out" ocaml_header.tmp)
 (target "norec.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - norec.eff.out)))))

(rule
 (deps "norec.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "norec.eff.out.ocaml_with_header"))))

(rule
 (deps "norec.eff.out")
  (alias runtest)
   (action
    (diff "norec.eff.ref" "norec.eff.out")))

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
 (target "not-found.eff.formatted")
  (action
   (with-outputs-to "not-found.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat not-found.eff.out)))))

(rule
 (deps "not-found.eff.formatted")
  (alias runtest)
   (action
    (diff "not-found.eff.ref.formatted" "not-found.eff.formatted")))

(rule
 (deps "not-found.eff.out" ocaml_header.tmp)
 (target "not-found.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - not-found.eff.out)))))

(rule
 (deps "not-found.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "not-found.eff.out.ocaml_with_header"))))

(rule
 (deps "not-found.eff.out")
  (alias runtest)
   (action
    (diff "not-found.eff.ref" "not-found.eff.out")))

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
 (target "one_input.eff.formatted")
  (action
   (with-outputs-to "one_input.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat one_input.eff.out)))))

(rule
 (deps "one_input.eff.formatted")
  (alias runtest)
   (action
    (diff "one_input.eff.ref.formatted" "one_input.eff.formatted")))

(rule
 (deps "one_input.eff.out" ocaml_header.tmp)
 (target "one_input.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - one_input.eff.out)))))

(rule
 (deps "one_input.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "one_input.eff.out.ocaml_with_header"))))

(rule
 (deps "one_input.eff.out")
  (alias runtest)
   (action
    (diff "one_input.eff.ref" "one_input.eff.out")))

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
 (target "original.eff.formatted")
  (action
   (with-outputs-to "original.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat original.eff.out)))))

(rule
 (deps "original.eff.formatted")
  (alias runtest)
   (action
    (diff "original.eff.ref.formatted" "original.eff.formatted")))

(rule
 (deps "original.eff.out" ocaml_header.tmp)
 (target "original.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - original.eff.out)))))

(rule
 (deps "original.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "original.eff.out.ocaml_with_header"))))

(rule
 (deps "original.eff.out")
  (alias runtest)
   (action
    (diff "original.eff.ref" "original.eff.out")))

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
 (target "other-effect.eff.formatted")
  (action
   (with-outputs-to "other-effect.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat other-effect.eff.out)))))

(rule
 (deps "other-effect.eff.formatted")
  (alias runtest)
   (action
    (diff "other-effect.eff.ref.formatted" "other-effect.eff.formatted")))

(rule
 (deps "other-effect.eff.out" ocaml_header.tmp)
 (target "other-effect.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - other-effect.eff.out)))))

(rule
 (deps "other-effect.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "other-effect.eff.out.ocaml_with_header"))))

(rule
 (deps "other-effect.eff.out")
  (alias runtest)
   (action
    (diff "other-effect.eff.ref" "other-effect.eff.out")))

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
 (target "pm-1_fails.eff.formatted")
  (action
   (with-outputs-to "pm-1_fails.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat pm-1_fails.eff.out)))))

(rule
 (deps "pm-1_fails.eff.formatted")
  (alias runtest)
   (action
    (diff "pm-1_fails.eff.ref.formatted" "pm-1_fails.eff.formatted")))

(rule
 (deps "pm-1_fails.eff.out" ocaml_header.tmp)
 (target "pm-1_fails.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - pm-1_fails.eff.out)))))

(rule
 (deps "pm-1_fails.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "pm-1_fails.eff.out.ocaml_with_header"))))

(rule
 (deps "pm-1_fails.eff.out")
  (alias runtest)
   (action
    (diff "pm-1_fails.eff.ref" "pm-1_fails.eff.out")))

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
 (target "pm-2_passes.eff.formatted")
  (action
   (with-outputs-to "pm-2_passes.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat pm-2_passes.eff.out)))))

(rule
 (deps "pm-2_passes.eff.formatted")
  (alias runtest)
   (action
    (diff "pm-2_passes.eff.ref.formatted" "pm-2_passes.eff.formatted")))

(rule
 (deps "pm-2_passes.eff.out" ocaml_header.tmp)
 (target "pm-2_passes.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - pm-2_passes.eff.out)))))

(rule
 (deps "pm-2_passes.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "pm-2_passes.eff.out.ocaml_with_header"))))

(rule
 (deps "pm-2_passes.eff.out")
  (alias runtest)
   (action
    (diff "pm-2_passes.eff.ref" "pm-2_passes.eff.out")))

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
 (target "pm-3_passes.eff.formatted")
  (action
   (with-outputs-to "pm-3_passes.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat pm-3_passes.eff.out)))))

(rule
 (deps "pm-3_passes.eff.formatted")
  (alias runtest)
   (action
    (diff "pm-3_passes.eff.ref.formatted" "pm-3_passes.eff.formatted")))

(rule
 (deps "pm-3_passes.eff.out" ocaml_header.tmp)
 (target "pm-3_passes.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - pm-3_passes.eff.out)))))

(rule
 (deps "pm-3_passes.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "pm-3_passes.eff.out.ocaml_with_header"))))

(rule
 (deps "pm-3_passes.eff.out")
  (alias runtest)
   (action
    (diff "pm-3_passes.eff.ref" "pm-3_passes.eff.out")))

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
 (target "rec1.eff.formatted")
  (action
   (with-outputs-to "rec1.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat rec1.eff.out)))))

(rule
 (deps "rec1.eff.formatted")
  (alias runtest)
   (action
    (diff "rec1.eff.ref.formatted" "rec1.eff.formatted")))

(rule
 (deps "rec1.eff.out" ocaml_header.tmp)
 (target "rec1.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - rec1.eff.out)))))

(rule
 (deps "rec1.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "rec1.eff.out.ocaml_with_header"))))

(rule
 (deps "rec1.eff.out")
  (alias runtest)
   (action
    (diff "rec1.eff.ref" "rec1.eff.out")))

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
 (target "rec2.eff.formatted")
  (action
   (with-outputs-to "rec2.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat rec2.eff.out)))))

(rule
 (deps "rec2.eff.formatted")
  (alias runtest)
   (action
    (diff "rec2.eff.ref.formatted" "rec2.eff.formatted")))

(rule
 (deps "rec2.eff.out" ocaml_header.tmp)
 (target "rec2.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - rec2.eff.out)))))

(rule
 (deps "rec2.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "rec2.eff.out.ocaml_with_header"))))

(rule
 (deps "rec2.eff.out")
  (alias runtest)
   (action
    (diff "rec2.eff.ref" "rec2.eff.out")))

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
 (target "substitution.eff.formatted")
  (action
   (with-outputs-to "substitution.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat substitution.eff.out)))))

(rule
 (deps "substitution.eff.formatted")
  (alias runtest)
   (action
    (diff "substitution.eff.ref.formatted" "substitution.eff.formatted")))

(rule
 (deps "substitution.eff.out" ocaml_header.tmp)
 (target "substitution.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - substitution.eff.out)))))

(rule
 (deps "substitution.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "substitution.eff.out.ocaml_with_header"))))

(rule
 (deps "substitution.eff.out")
  (alias runtest)
   (action
    (diff "substitution.eff.ref" "substitution.eff.out")))

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
 (target "test-handle_effect_skip.eff.formatted")
  (action
   (with-outputs-to "test-handle_effect_skip.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test-handle_effect_skip.eff.out)))))

(rule
 (deps "test-handle_effect_skip.eff.formatted")
  (alias runtest)
   (action
    (diff "test-handle_effect_skip.eff.ref.formatted" "test-handle_effect_skip.eff.formatted")))

(rule
 (deps "test-handle_effect_skip.eff.out" ocaml_header.tmp)
 (target "test-handle_effect_skip.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test-handle_effect_skip.eff.out)))))

(rule
 (deps "test-handle_effect_skip.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test-handle_effect_skip.eff.out.ocaml_with_header"))))

(rule
 (deps "test-handle_effect_skip.eff.out")
  (alias runtest)
   (action
    (diff "test-handle_effect_skip.eff.ref" "test-handle_effect_skip.eff.out")))

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
 (target "test1.eff.formatted")
  (action
   (with-outputs-to "test1.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test1.eff.out)))))

(rule
 (deps "test1.eff.formatted")
  (alias runtest)
   (action
    (diff "test1.eff.ref.formatted" "test1.eff.formatted")))

(rule
 (deps "test1.eff.out" ocaml_header.tmp)
 (target "test1.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test1.eff.out)))))

(rule
 (deps "test1.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test1.eff.out.ocaml_with_header"))))

(rule
 (deps "test1.eff.out")
  (alias runtest)
   (action
    (diff "test1.eff.ref" "test1.eff.out")))

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
 (target "test10.eff.formatted")
  (action
   (with-outputs-to "test10.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test10.eff.out)))))

(rule
 (deps "test10.eff.formatted")
  (alias runtest)
   (action
    (diff "test10.eff.ref.formatted" "test10.eff.formatted")))

(rule
 (deps "test10.eff.out" ocaml_header.tmp)
 (target "test10.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test10.eff.out)))))

(rule
 (deps "test10.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test10.eff.out.ocaml_with_header"))))

(rule
 (deps "test10.eff.out")
  (alias runtest)
   (action
    (diff "test10.eff.ref" "test10.eff.out")))

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
 (target "test11.eff.formatted")
  (action
   (with-outputs-to "test11.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test11.eff.out)))))

(rule
 (deps "test11.eff.formatted")
  (alias runtest)
   (action
    (diff "test11.eff.ref.formatted" "test11.eff.formatted")))

(rule
 (deps "test11.eff.out" ocaml_header.tmp)
 (target "test11.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test11.eff.out)))))

(rule
 (deps "test11.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test11.eff.out.ocaml_with_header"))))

(rule
 (deps "test11.eff.out")
  (alias runtest)
   (action
    (diff "test11.eff.ref" "test11.eff.out")))

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
 (target "test12.eff.formatted")
  (action
   (with-outputs-to "test12.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test12.eff.out)))))

(rule
 (deps "test12.eff.formatted")
  (alias runtest)
   (action
    (diff "test12.eff.ref.formatted" "test12.eff.formatted")))

(rule
 (deps "test12.eff.out" ocaml_header.tmp)
 (target "test12.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test12.eff.out)))))

(rule
 (deps "test12.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test12.eff.out.ocaml_with_header"))))

(rule
 (deps "test12.eff.out")
  (alias runtest)
   (action
    (diff "test12.eff.ref" "test12.eff.out")))

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
 (target "test13.eff.formatted")
  (action
   (with-outputs-to "test13.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test13.eff.out)))))

(rule
 (deps "test13.eff.formatted")
  (alias runtest)
   (action
    (diff "test13.eff.ref.formatted" "test13.eff.formatted")))

(rule
 (deps "test13.eff.out" ocaml_header.tmp)
 (target "test13.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test13.eff.out)))))

(rule
 (deps "test13.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test13.eff.out.ocaml_with_header"))))

(rule
 (deps "test13.eff.out")
  (alias runtest)
   (action
    (diff "test13.eff.ref" "test13.eff.out")))

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
 (target "test14.eff.formatted")
  (action
   (with-outputs-to "test14.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test14.eff.out)))))

(rule
 (deps "test14.eff.formatted")
  (alias runtest)
   (action
    (diff "test14.eff.ref.formatted" "test14.eff.formatted")))

(rule
 (deps "test14.eff.out" ocaml_header.tmp)
 (target "test14.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test14.eff.out)))))

(rule
 (deps "test14.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test14.eff.out.ocaml_with_header"))))

(rule
 (deps "test14.eff.out")
  (alias runtest)
   (action
    (diff "test14.eff.ref" "test14.eff.out")))

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
 (target "test15.eff.formatted")
  (action
   (with-outputs-to "test15.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test15.eff.out)))))

(rule
 (deps "test15.eff.formatted")
  (alias runtest)
   (action
    (diff "test15.eff.ref.formatted" "test15.eff.formatted")))

(rule
 (deps "test15.eff.out" ocaml_header.tmp)
 (target "test15.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test15.eff.out)))))

(rule
 (deps "test15.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test15.eff.out.ocaml_with_header"))))

(rule
 (deps "test15.eff.out")
  (alias runtest)
   (action
    (diff "test15.eff.ref" "test15.eff.out")))

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
 (target "test16.eff.formatted")
  (action
   (with-outputs-to "test16.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test16.eff.out)))))

(rule
 (deps "test16.eff.formatted")
  (alias runtest)
   (action
    (diff "test16.eff.ref.formatted" "test16.eff.formatted")))

(rule
 (deps "test16.eff.out" ocaml_header.tmp)
 (target "test16.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test16.eff.out)))))

(rule
 (deps "test16.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test16.eff.out.ocaml_with_header"))))

(rule
 (deps "test16.eff.out")
  (alias runtest)
   (action
    (diff "test16.eff.ref" "test16.eff.out")))

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
 (target "test17.eff.formatted")
  (action
   (with-outputs-to "test17.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test17.eff.out)))))

(rule
 (deps "test17.eff.formatted")
  (alias runtest)
   (action
    (diff "test17.eff.ref.formatted" "test17.eff.formatted")))

(rule
 (deps "test17.eff.out" ocaml_header.tmp)
 (target "test17.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test17.eff.out)))))

(rule
 (deps "test17.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test17.eff.out.ocaml_with_header"))))

(rule
 (deps "test17.eff.out")
  (alias runtest)
   (action
    (diff "test17.eff.ref" "test17.eff.out")))

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
 (target "test18.eff.formatted")
  (action
   (with-outputs-to "test18.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test18.eff.out)))))

(rule
 (deps "test18.eff.formatted")
  (alias runtest)
   (action
    (diff "test18.eff.ref.formatted" "test18.eff.formatted")))

(rule
 (deps "test18.eff.out" ocaml_header.tmp)
 (target "test18.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test18.eff.out)))))

(rule
 (deps "test18.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test18.eff.out.ocaml_with_header"))))

(rule
 (deps "test18.eff.out")
  (alias runtest)
   (action
    (diff "test18.eff.ref" "test18.eff.out")))

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
 (target "test19.eff.formatted")
  (action
   (with-outputs-to "test19.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test19.eff.out)))))

(rule
 (deps "test19.eff.formatted")
  (alias runtest)
   (action
    (diff "test19.eff.ref.formatted" "test19.eff.formatted")))

(rule
 (deps "test19.eff.out" ocaml_header.tmp)
 (target "test19.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test19.eff.out)))))

(rule
 (deps "test19.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test19.eff.out.ocaml_with_header"))))

(rule
 (deps "test19.eff.out")
  (alias runtest)
   (action
    (diff "test19.eff.ref" "test19.eff.out")))

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
 (target "test2.eff.formatted")
  (action
   (with-outputs-to "test2.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test2.eff.out)))))

(rule
 (deps "test2.eff.formatted")
  (alias runtest)
   (action
    (diff "test2.eff.ref.formatted" "test2.eff.formatted")))

(rule
 (deps "test2.eff.out" ocaml_header.tmp)
 (target "test2.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test2.eff.out)))))

(rule
 (deps "test2.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test2.eff.out.ocaml_with_header"))))

(rule
 (deps "test2.eff.out")
  (alias runtest)
   (action
    (diff "test2.eff.ref" "test2.eff.out")))

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
 (target "test20.eff.formatted")
  (action
   (with-outputs-to "test20.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test20.eff.out)))))

(rule
 (deps "test20.eff.formatted")
  (alias runtest)
   (action
    (diff "test20.eff.ref.formatted" "test20.eff.formatted")))

(rule
 (deps "test20.eff.out" ocaml_header.tmp)
 (target "test20.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test20.eff.out)))))

(rule
 (deps "test20.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test20.eff.out.ocaml_with_header"))))

(rule
 (deps "test20.eff.out")
  (alias runtest)
   (action
    (diff "test20.eff.ref" "test20.eff.out")))

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
 (target "test3.eff.formatted")
  (action
   (with-outputs-to "test3.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test3.eff.out)))))

(rule
 (deps "test3.eff.formatted")
  (alias runtest)
   (action
    (diff "test3.eff.ref.formatted" "test3.eff.formatted")))

(rule
 (deps "test3.eff.out" ocaml_header.tmp)
 (target "test3.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test3.eff.out)))))

(rule
 (deps "test3.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test3.eff.out.ocaml_with_header"))))

(rule
 (deps "test3.eff.out")
  (alias runtest)
   (action
    (diff "test3.eff.ref" "test3.eff.out")))

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
 (target "test4.eff.formatted")
  (action
   (with-outputs-to "test4.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test4.eff.out)))))

(rule
 (deps "test4.eff.formatted")
  (alias runtest)
   (action
    (diff "test4.eff.ref.formatted" "test4.eff.formatted")))

(rule
 (deps "test4.eff.out" ocaml_header.tmp)
 (target "test4.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test4.eff.out)))))

(rule
 (deps "test4.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test4.eff.out.ocaml_with_header"))))

(rule
 (deps "test4.eff.out")
  (alias runtest)
   (action
    (diff "test4.eff.ref" "test4.eff.out")))

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
 (target "test5.eff.formatted")
  (action
   (with-outputs-to "test5.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test5.eff.out)))))

(rule
 (deps "test5.eff.formatted")
  (alias runtest)
   (action
    (diff "test5.eff.ref.formatted" "test5.eff.formatted")))

(rule
 (deps "test5.eff.out" ocaml_header.tmp)
 (target "test5.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test5.eff.out)))))

(rule
 (deps "test5.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test5.eff.out.ocaml_with_header"))))

(rule
 (deps "test5.eff.out")
  (alias runtest)
   (action
    (diff "test5.eff.ref" "test5.eff.out")))

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
 (target "test6.eff.formatted")
  (action
   (with-outputs-to "test6.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test6.eff.out)))))

(rule
 (deps "test6.eff.formatted")
  (alias runtest)
   (action
    (diff "test6.eff.ref.formatted" "test6.eff.formatted")))

(rule
 (deps "test6.eff.out" ocaml_header.tmp)
 (target "test6.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test6.eff.out)))))

(rule
 (deps "test6.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test6.eff.out.ocaml_with_header"))))

(rule
 (deps "test6.eff.out")
  (alias runtest)
   (action
    (diff "test6.eff.ref" "test6.eff.out")))

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
 (target "test7.eff.formatted")
  (action
   (with-outputs-to "test7.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test7.eff.out)))))

(rule
 (deps "test7.eff.formatted")
  (alias runtest)
   (action
    (diff "test7.eff.ref.formatted" "test7.eff.formatted")))

(rule
 (deps "test7.eff.out" ocaml_header.tmp)
 (target "test7.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test7.eff.out)))))

(rule
 (deps "test7.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test7.eff.out.ocaml_with_header"))))

(rule
 (deps "test7.eff.out")
  (alias runtest)
   (action
    (diff "test7.eff.ref" "test7.eff.out")))

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
 (target "test8.eff.formatted")
  (action
   (with-outputs-to "test8.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test8.eff.out)))))

(rule
 (deps "test8.eff.formatted")
  (alias runtest)
   (action
    (diff "test8.eff.ref.formatted" "test8.eff.formatted")))

(rule
 (deps "test8.eff.out" ocaml_header.tmp)
 (target "test8.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test8.eff.out)))))

(rule
 (deps "test8.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test8.eff.out.ocaml_with_header"))))

(rule
 (deps "test8.eff.out")
  (alias runtest)
   (action
    (diff "test8.eff.ref" "test8.eff.out")))

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
 (target "test9.eff.formatted")
  (action
   (with-outputs-to "test9.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat test9.eff.out)))))

(rule
 (deps "test9.eff.formatted")
  (alias runtest)
   (action
    (diff "test9.eff.ref.formatted" "test9.eff.formatted")))

(rule
 (deps "test9.eff.out" ocaml_header.tmp)
 (target "test9.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - test9.eff.out)))))

(rule
 (deps "test9.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "test9.eff.out.ocaml_with_header"))))

(rule
 (deps "test9.eff.out")
  (alias runtest)
   (action
    (diff "test9.eff.ref" "test9.eff.out")))

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
 (target "top-letrec_fails.eff.formatted")
  (action
   (with-outputs-to "top-letrec_fails.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat top-letrec_fails.eff.out)))))

(rule
 (deps "top-letrec_fails.eff.formatted")
  (alias runtest)
   (action
    (diff "top-letrec_fails.eff.ref.formatted" "top-letrec_fails.eff.formatted")))

(rule
 (deps "top-letrec_fails.eff.out" ocaml_header.tmp)
 (target "top-letrec_fails.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - top-letrec_fails.eff.out)))))

(rule
 (deps "top-letrec_fails.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "top-letrec_fails.eff.out.ocaml_with_header"))))

(rule
 (deps "top-letrec_fails.eff.out")
  (alias runtest)
   (action
    (diff "top-letrec_fails.eff.ref" "top-letrec_fails.eff.out")))

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
 (target "two_inputs.eff.formatted")
  (action
   (with-outputs-to "two_inputs.eff.formatted"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocamlformat two_inputs.eff.out)))))

(rule
 (deps "two_inputs.eff.formatted")
  (alias runtest)
   (action
    (diff "two_inputs.eff.ref.formatted" "two_inputs.eff.formatted")))

(rule
 (deps "two_inputs.eff.out" ocaml_header.tmp)
 (target "two_inputs.eff.out.ocaml_with_header")
  (action
   (with-outputs-to "%{target}"
    (pipe-outputs (run echo ";;") (run cat ocaml_header.tmp - two_inputs.eff.out)))))

(rule
 (deps "two_inputs.eff.out.ocaml_with_header")
 (alias runtest)
 (action
  (with-accepted-exit-codes 0
   (run ocaml "two_inputs.eff.out.ocaml_with_header"))))

(rule
 (deps "two_inputs.eff.out")
  (alias runtest)
   (action
    (diff "two_inputs.eff.ref" "two_inputs.eff.out")))

