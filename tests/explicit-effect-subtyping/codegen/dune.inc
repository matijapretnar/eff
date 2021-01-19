(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "application_red.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./application_red.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./handle_match.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./handle_rec.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./handler_beta_reduction.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./is_relatively_pure.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./let_list_to_bind.eff")))))

(rule
 (alias runtest)
  (action
   (diff "let_list_to_bind.eff.ref" "let_list_to_bind.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loop_example.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./loop_example.eff")))))

(rule
 (alias runtest)
  (action
   (diff "loop_example.eff.ref" "loop_example.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "match_red.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./match_red.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./not-found.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./one_input.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./substitution.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./test-handle_effect_skip.eff")))))

(rule
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
       (run eff --no-stdlib --no-header --compile-plain-ocaml "./two_inputs.eff")))))

(rule
 (alias runtest)
  (action
   (diff "two_inputs.eff.ref" "two_inputs.eff.out")))

