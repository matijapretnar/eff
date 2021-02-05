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

