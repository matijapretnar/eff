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
 (deps "application_red.eff.out")
 (target "application_red.eff.out.ocaml_output")
  (action
   (with-outputs-to "application_red.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml application_red.eff.out)))))

(rule
 (deps "application_red.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "application_red.eff.ref.ocaml_output" "application_red.eff.out.ocaml_output")))

(rule
 (deps "application_red.eff.out")
  (alias runtest)
   (action
    (diff "application_red.eff.ref" "application_red.eff.out")))

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
 (deps "handle_match.eff.out")
 (target "handle_match.eff.out.ocaml_output")
  (action
   (with-outputs-to "handle_match.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml handle_match.eff.out)))))

(rule
 (deps "handle_match.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "handle_match.eff.ref.ocaml_output" "handle_match.eff.out.ocaml_output")))

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
 (deps "handle_rec.eff.out")
 (target "handle_rec.eff.out.ocaml_output")
  (action
   (with-outputs-to "handle_rec.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml handle_rec.eff.out)))))

(rule
 (deps "handle_rec.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "handle_rec.eff.ref.ocaml_output" "handle_rec.eff.out.ocaml_output")))

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
 (deps "handler_beta_reduction.eff.out")
 (target "handler_beta_reduction.eff.out.ocaml_output")
  (action
   (with-outputs-to "handler_beta_reduction.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml handler_beta_reduction.eff.out)))))

(rule
 (deps "handler_beta_reduction.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "handler_beta_reduction.eff.ref.ocaml_output" "handler_beta_reduction.eff.out.ocaml_output")))

(rule
 (deps "handler_beta_reduction.eff.out")
  (alias runtest)
   (action
    (diff "handler_beta_reduction.eff.ref" "handler_beta_reduction.eff.out")))

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
 (deps "is_relatively_pure.eff.out")
 (target "is_relatively_pure.eff.out.ocaml_output")
  (action
   (with-outputs-to "is_relatively_pure.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml is_relatively_pure.eff.out)))))

(rule
 (deps "is_relatively_pure.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "is_relatively_pure.eff.ref.ocaml_output" "is_relatively_pure.eff.out.ocaml_output")))

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
 (deps "let_list_to_bind.eff.out")
 (target "let_list_to_bind.eff.out.ocaml_output")
  (action
   (with-outputs-to "let_list_to_bind.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml let_list_to_bind.eff.out)))))

(rule
 (deps "let_list_to_bind.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "let_list_to_bind.eff.ref.ocaml_output" "let_list_to_bind.eff.out.ocaml_output")))

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
 (deps "match_red.eff.out")
 (target "match_red.eff.out.ocaml_output")
  (action
   (with-outputs-to "match_red.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml match_red.eff.out)))))

(rule
 (deps "match_red.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "match_red.eff.ref.ocaml_output" "match_red.eff.out.ocaml_output")))

(rule
 (deps "match_red.eff.out")
  (alias runtest)
   (action
    (diff "match_red.eff.ref" "match_red.eff.out")))

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
 (deps "not-found.eff.out")
 (target "not-found.eff.out.ocaml_output")
  (action
   (with-outputs-to "not-found.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml not-found.eff.out)))))

(rule
 (deps "not-found.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "not-found.eff.ref.ocaml_output" "not-found.eff.out.ocaml_output")))

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
 (deps "one_input.eff.out")
 (target "one_input.eff.out.ocaml_output")
  (action
   (with-outputs-to "one_input.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml one_input.eff.out)))))

(rule
 (deps "one_input.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "one_input.eff.ref.ocaml_output" "one_input.eff.out.ocaml_output")))

(rule
 (deps "one_input.eff.out")
  (alias runtest)
   (action
    (diff "one_input.eff.ref" "one_input.eff.out")))

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
 (deps "substitution.eff.out")
 (target "substitution.eff.out.ocaml_output")
  (action
   (with-outputs-to "substitution.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml substitution.eff.out)))))

(rule
 (deps "substitution.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "substitution.eff.ref.ocaml_output" "substitution.eff.out.ocaml_output")))

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
 (deps "test-handle_effect_skip.eff.out")
 (target "test-handle_effect_skip.eff.out.ocaml_output")
  (action
   (with-outputs-to "test-handle_effect_skip.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml test-handle_effect_skip.eff.out)))))

(rule
 (deps "test-handle_effect_skip.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "test-handle_effect_skip.eff.ref.ocaml_output" "test-handle_effect_skip.eff.out.ocaml_output")))

(rule
 (deps "test-handle_effect_skip.eff.out")
  (alias runtest)
   (action
    (diff "test-handle_effect_skip.eff.ref" "test-handle_effect_skip.eff.out")))

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
 (deps "two_inputs.eff.out")
 (target "two_inputs.eff.out.ocaml_output")
  (action
   (with-outputs-to "two_inputs.eff.out.ocaml_output"
    (with-accepted-exit-codes (or 0 1 2)
     (run ocaml two_inputs.eff.out)))))

(rule
 (deps "two_inputs.eff.out.ocaml_output")
  (alias runtest)
   (action
    (diff "two_inputs.eff.ref.ocaml_output" "two_inputs.eff.out.ocaml_output")))

(rule
 (deps "two_inputs.eff.out")
  (alias runtest)
   (action
    (diff "two_inputs.eff.ref" "two_inputs.eff.out")))

