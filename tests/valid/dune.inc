(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "lexer.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./lexer.eff")))))

(rule
 (alias runtest)
  (action
   (diff "lexer.eff.ref" "lexer.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "orelse_andalso.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./orelse_andalso.eff")))))

(rule
 (alias runtest)
  (action
   (diff "orelse_andalso.eff.ref" "orelse_andalso.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "patterns.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./patterns.eff")))))

(rule
 (alias runtest)
  (action
   (diff "patterns.eff.ref" "patterns.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "polymorphism.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./polymorphism.eff")))))

(rule
 (alias runtest)
  (action
   (diff "polymorphism.eff.ref" "polymorphism.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "semisemi.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./semisemi.eff")))))

(rule
 (alias runtest)
  (action
   (diff "semisemi.eff.ref" "semisemi.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "state.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./state.eff")))))

(rule
 (alias runtest)
  (action
   (diff "state.eff.ref" "state.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test_equality.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./test_equality.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test_equality.eff.ref" "test_equality.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test_less_than.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./test_less_than.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test_less_than.eff.ref" "test_less_than.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test_stdlib.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./test_stdlib.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test_stdlib.eff.ref" "test_stdlib.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "tydef.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./tydef.eff")))))

(rule
 (alias runtest)
  (action
   (diff "tydef.eff.ref" "tydef.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "type_annotations.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./type_annotations.eff")))))

(rule
 (alias runtest)
  (action
   (diff "type_annotations.eff.ref" "type_annotations.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "typing.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       0
       (run eff "./typing.eff")))))

(rule
 (alias runtest)
  (action
   (diff "typing.eff.ref" "typing.eff.out")))

