(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopNoOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./loop/loop.eff")))))

(rule
 (deps "loopNoOpt.out")
  (target "loopNoOpt.formatted")
   (action
    (with-outputs-to "loopNoOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoOpt.out)))))

(rule
 (deps loopNoOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "loop/loopNoOpt.ml" "loopNoOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./loop/loop.eff")))))

(rule
 (deps "loopOpt.out")
  (target "loopOpt.formatted")
   (action
    (with-outputs-to "loopOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopOpt.out)))))

(rule
 (deps loopOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "loop/loopOpt.ml" "loopOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensNoOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./queens/queens.eff")))))

(rule
 (deps "queensNoOpt.out")
  (target "queensNoOpt.formatted")
   (action
    (with-outputs-to "queensNoOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoOpt.out)))))

(rule
 (deps queensNoOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "queens/queensNoOpt.ml" "queensNoOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./queens/queens.eff")))))

(rule
 (deps "queensOpt.out")
  (target "queensOpt.formatted")
   (action
    (with-outputs-to "queensOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensOpt.out)))))

(rule
 (deps queensOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "queens/queensOpt.ml" "queensOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpNoOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./interp/interp.eff")))))

(rule
 (deps "interpNoOpt.out")
  (target "interpNoOpt.formatted")
   (action
    (with-outputs-to "interpNoOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoOpt.out)))))

(rule
 (deps interpNoOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "interp/interpNoOpt.ml" "interpNoOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./interp/interp.eff")))))

(rule
 (deps "interpOpt.out")
  (target "interpOpt.formatted")
   (action
    (with-outputs-to "interpOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpOpt.out)))))

(rule
 (deps interpOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "interp/interpOpt.ml" "interpOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeNoOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml --no-opts "./range/range.eff")))))

(rule
 (deps "rangeNoOpt.out")
  (target "rangeNoOpt.formatted")
   (action
    (with-outputs-to "rangeNoOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoOpt.out)))))

(rule
 (deps rangeNoOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "range/rangeNoOpt.ml" "rangeNoOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./range/range.eff")))))

(rule
 (deps "rangeOpt.out")
  (target "rangeOpt.formatted")
   (action
    (with-outputs-to "rangeOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeOpt.out)))))

(rule
 (deps rangeOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "range/rangeOpt.ml" "rangeOpt.formatted")))

