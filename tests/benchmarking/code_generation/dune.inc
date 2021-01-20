(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopNoOptImpure.ml" "loopNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opts "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopNoOptPure.ml" "loopNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopOptImpure.ml" "loopOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopOptPure.ml" "loopOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensNoOptImpure.ml" "queensNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opts "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensNoOptPure.ml" "queensNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensOptImpure.ml" "queensOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensOptPure.ml" "queensOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpNoOptImpure.ml" "interpNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opts "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpNoOptPure.ml" "interpNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpOptImpure.ml" "interpOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpOptPure.ml" "interpOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeNoOptImpure.ml" "rangeNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opts "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeNoOptPure.ml" "rangeNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeOptImpure.ml" "rangeOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeOptPure.ml" "rangeOptPure.out")))

