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
 (deps "loopNoOptImpure.out")
  (target "loopNoOptImpure.formatted")
   (action
    (with-outputs-to "loopNoOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoOptImpure.out)))))

(rule
 (deps loopNoOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "loop/loopNoOptImpure.ml" "loopNoOptImpure.formatted")))

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
 (deps "loopNoOptPure.out")
  (target "loopNoOptPure.formatted")
   (action
    (with-outputs-to "loopNoOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoOptPure.out)))))

(rule
 (deps loopNoOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "loop/loopNoOptPure.ml" "loopNoOptPure.formatted")))

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
 (deps "loopOptImpure.out")
  (target "loopOptImpure.formatted")
   (action
    (with-outputs-to "loopOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopOptImpure.out)))))

(rule
 (deps loopOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "loop/loopOptImpure.ml" "loopOptImpure.formatted")))

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
 (deps "loopOptPure.out")
  (target "loopOptPure.formatted")
   (action
    (with-outputs-to "loopOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopOptPure.out)))))

(rule
 (deps loopOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "loop/loopOptPure.ml" "loopOptPure.formatted")))

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
 (deps "queensNoOptImpure.out")
  (target "queensNoOptImpure.formatted")
   (action
    (with-outputs-to "queensNoOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoOptImpure.out)))))

(rule
 (deps queensNoOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "queens/queensNoOptImpure.ml" "queensNoOptImpure.formatted")))

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
 (deps "queensNoOptPure.out")
  (target "queensNoOptPure.formatted")
   (action
    (with-outputs-to "queensNoOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoOptPure.out)))))

(rule
 (deps queensNoOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "queens/queensNoOptPure.ml" "queensNoOptPure.formatted")))

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
 (deps "queensOptImpure.out")
  (target "queensOptImpure.formatted")
   (action
    (with-outputs-to "queensOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensOptImpure.out)))))

(rule
 (deps queensOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "queens/queensOptImpure.ml" "queensOptImpure.formatted")))

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
 (deps "queensOptPure.out")
  (target "queensOptPure.formatted")
   (action
    (with-outputs-to "queensOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensOptPure.out)))))

(rule
 (deps queensOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "queens/queensOptPure.ml" "queensOptPure.formatted")))

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
 (deps "interpNoOptImpure.out")
  (target "interpNoOptImpure.formatted")
   (action
    (with-outputs-to "interpNoOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoOptImpure.out)))))

(rule
 (deps interpNoOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "interp/interpNoOptImpure.ml" "interpNoOptImpure.formatted")))

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
 (deps "interpNoOptPure.out")
  (target "interpNoOptPure.formatted")
   (action
    (with-outputs-to "interpNoOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoOptPure.out)))))

(rule
 (deps interpNoOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "interp/interpNoOptPure.ml" "interpNoOptPure.formatted")))

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
 (deps "interpOptImpure.out")
  (target "interpOptImpure.formatted")
   (action
    (with-outputs-to "interpOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpOptImpure.out)))))

(rule
 (deps interpOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "interp/interpOptImpure.ml" "interpOptImpure.formatted")))

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
 (deps "interpOptPure.out")
  (target "interpOptPure.formatted")
   (action
    (with-outputs-to "interpOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpOptPure.out)))))

(rule
 (deps interpOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "interp/interpOptPure.ml" "interpOptPure.formatted")))

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
 (deps "rangeNoOptImpure.out")
  (target "rangeNoOptImpure.formatted")
   (action
    (with-outputs-to "rangeNoOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoOptImpure.out)))))

(rule
 (deps rangeNoOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "range/rangeNoOptImpure.ml" "rangeNoOptImpure.formatted")))

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
 (deps "rangeNoOptPure.out")
  (target "rangeNoOptPure.formatted")
   (action
    (with-outputs-to "rangeNoOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoOptPure.out)))))

(rule
 (deps rangeNoOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "range/rangeNoOptPure.ml" "rangeNoOptPure.formatted")))

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
 (deps "rangeOptImpure.out")
  (target "rangeOptImpure.formatted")
   (action
    (with-outputs-to "rangeOptImpure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeOptImpure.out)))))

(rule
 (deps rangeOptImpure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "range/rangeOptImpure.ml" "rangeOptImpure.formatted")))

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
 (deps "rangeOptPure.out")
  (target "rangeOptPure.formatted")
   (action
    (with-outputs-to "rangeOptPure.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeOptPure.out)))))

(rule
 (deps rangeOptPure.formatted)
  (alias generate_benchmarks)
   (action
    (diff "range/rangeOptPure.ml" "rangeOptPure.formatted")))

