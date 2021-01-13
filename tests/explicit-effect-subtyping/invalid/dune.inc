(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test3.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 2 0 1 2)
       (run eff --explicit-effects "./test3.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test3.eff.ref" "test3.eff.out")))

