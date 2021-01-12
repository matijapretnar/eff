(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test3.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       2
       (run eff --compile-plain-ocaml "./test3.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test3.eff.ref" "test3.eff.out")))
