(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test1.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --explicit-effects "./test1.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test10.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test11.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test12.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test13.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test14.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test15.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test16.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test17.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test18.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test19.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test2.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test2.eff.ref" "test2.eff.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "test4.eff.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 0 1 2)
       (run eff --no-stdlib --explicit-effects "./test4.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test5.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test6.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test7.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test8.eff")))))

(rule
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
       (run eff --no-stdlib --explicit-effects "./test9.eff")))))

(rule
 (alias runtest)
  (action
   (diff "test9.eff.ref" "test9.eff.out")))

