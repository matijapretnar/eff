(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "loopOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./loop.eff")))))

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
    (diff "loopOpt.ml" "loopOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "queensOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./queens.eff")))))

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
    (diff "queensOpt.ml" "queensOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "interpOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./interp.eff")))))

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
    (diff "interpOpt.ml" "interpOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "rangeOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./range.eff")))))

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
    (diff "rangeOpt.ml" "rangeOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "treeOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./tree.eff")))))

(rule
 (deps "treeOpt.out")
  (target "treeOpt.formatted")
   (action
    (with-outputs-to "treeOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeOpt.out)))))

(rule
 (deps treeOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "treeOpt.ml" "treeOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (source_tree .))
   (target "capability_benchmarksOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  "./capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksOpt.out")
  (target "capability_benchmarksOpt.formatted")
   (action
    (with-outputs-to "capability_benchmarksOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksOpt.out)))))

(rule
 (deps capability_benchmarksOpt.formatted)
  (alias generate_benchmarks)
   (action
    (diff "capability_benchmarksOpt.ml" "capability_benchmarksOpt.formatted")))

