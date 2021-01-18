(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loop/loopOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopOptPure.ml" "loop/loopOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loop/loopNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opt "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopNoOptPure.ml" "loop/loopNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loop/loopOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopOptImpure.ml" "loop/loopOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loop/loopNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opt "./loop/loop.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "loop/loopNoOptImpure.ml" "loop/loopNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queens/queensOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensOptPure.ml" "queens/queensOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queens/queensNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opt "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensNoOptPure.ml" "queens/queensNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queens/queensOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensOptImpure.ml" "queens/queensOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queens/queensNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opt "./queens/queens.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "queens/queensNoOptImpure.ml" "queens/queensNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interp/interpOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpOptPure.ml" "interp/interpOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interp/interpNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opt "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpNoOptPure.ml" "interp/interpNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interp/interpOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpOptImpure.ml" "interp/interpOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interp/interpNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opt "./interp/interp.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "interp/interpNoOptImpure.ml" "interp/interpNoOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "range/rangeOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeOptPure.ml" "range/rangeOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "range/rangeNoOptPure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --pure --no-opt "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeNoOptPure.ml" "range/rangeNoOptPure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "range/rangeOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeOptImpure.ml" "range/rangeOptImpure.out")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "range/rangeNoOptImpure.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opt "./range/range.eff")))))

(rule
 (alias generate_benchmarks)
  (action
   (diff "range/rangeNoOptImpure.ml" "range/rangeNoOptImpure.out")))

