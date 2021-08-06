(rule
 (deps
 %{bin:eff}
  (file "../loop.eff")
  (source_tree .))
   (target "loopFullOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml   "../loop.eff")))))

(rule
 (deps "loopFullOpt.out")
  (target "loopFullOpt.formatted")
   (action
    (with-outputs-to "loopFullOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopFullOpt.out)))))

(rule
 (deps "loopFullOpt.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "loopFullOpt.ml" "loopFullOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../loop.eff")
  (source_tree .))
   (target "loopNoFunSpec.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1022 "../loop.eff")))))

(rule
 (deps "loopNoFunSpec.out")
  (target "loopNoFunSpec.formatted")
   (action
    (with-outputs-to "loopNoFunSpec.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoFunSpec.out)))))

(rule
 (deps "loopNoFunSpec.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "loopNoFunSpec.ml" "loopNoFunSpec.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../loop.eff")
  (source_tree .))
   (target "loopNoCoerElim.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1021 "../loop.eff")))))

(rule
 (deps "loopNoCoerElim.out")
  (target "loopNoCoerElim.formatted")
   (action
    (with-outputs-to "loopNoCoerElim.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoCoerElim.out)))))

(rule
 (deps "loopNoCoerElim.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "loopNoCoerElim.ml" "loopNoCoerElim.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../loop.eff")
  (source_tree .))
   (target "loopNoCoerPush.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1019 "../loop.eff")))))

(rule
 (deps "loopNoCoerPush.out")
  (target "loopNoCoerPush.formatted")
   (action
    (with-outputs-to "loopNoCoerPush.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoCoerPush.out)))))

(rule
 (deps "loopNoCoerPush.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "loopNoCoerPush.ml" "loopNoCoerPush.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../loop.eff")
  (source_tree .))
   (target "loopNoHandReduc.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1015 "../loop.eff")))))

(rule
 (deps "loopNoHandReduc.out")
  (target "loopNoHandReduc.formatted")
   (action
    (with-outputs-to "loopNoHandReduc.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoHandReduc.out)))))

(rule
 (deps "loopNoHandReduc.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "loopNoHandReduc.ml" "loopNoHandReduc.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../loop.eff")
  (source_tree .))
   (target "loopNoPureTrans.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1007 "../loop.eff")))))

(rule
 (deps "loopNoPureTrans.out")
  (target "loopNoPureTrans.formatted")
   (action
    (with-outputs-to "loopNoPureTrans.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat loopNoPureTrans.out)))))

(rule
 (deps "loopNoPureTrans.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "loopNoPureTrans.ml" "loopNoPureTrans.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../queens.eff")
  (source_tree .))
   (target "queensFullOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml   "../queens.eff")))))

(rule
 (deps "queensFullOpt.out")
  (target "queensFullOpt.formatted")
   (action
    (with-outputs-to "queensFullOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensFullOpt.out)))))

(rule
 (deps "queensFullOpt.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "queensFullOpt.ml" "queensFullOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../queens.eff")
  (source_tree .))
   (target "queensNoFunSpec.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1022 "../queens.eff")))))

(rule
 (deps "queensNoFunSpec.out")
  (target "queensNoFunSpec.formatted")
   (action
    (with-outputs-to "queensNoFunSpec.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoFunSpec.out)))))

(rule
 (deps "queensNoFunSpec.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "queensNoFunSpec.ml" "queensNoFunSpec.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../queens.eff")
  (source_tree .))
   (target "queensNoCoerElim.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1021 "../queens.eff")))))

(rule
 (deps "queensNoCoerElim.out")
  (target "queensNoCoerElim.formatted")
   (action
    (with-outputs-to "queensNoCoerElim.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoCoerElim.out)))))

(rule
 (deps "queensNoCoerElim.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "queensNoCoerElim.ml" "queensNoCoerElim.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../queens.eff")
  (source_tree .))
   (target "queensNoCoerPush.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1019 "../queens.eff")))))

(rule
 (deps "queensNoCoerPush.out")
  (target "queensNoCoerPush.formatted")
   (action
    (with-outputs-to "queensNoCoerPush.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoCoerPush.out)))))

(rule
 (deps "queensNoCoerPush.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "queensNoCoerPush.ml" "queensNoCoerPush.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../queens.eff")
  (source_tree .))
   (target "queensNoHandReduc.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1015 "../queens.eff")))))

(rule
 (deps "queensNoHandReduc.out")
  (target "queensNoHandReduc.formatted")
   (action
    (with-outputs-to "queensNoHandReduc.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoHandReduc.out)))))

(rule
 (deps "queensNoHandReduc.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "queensNoHandReduc.ml" "queensNoHandReduc.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../queens.eff")
  (source_tree .))
   (target "queensNoPureTrans.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1007 "../queens.eff")))))

(rule
 (deps "queensNoPureTrans.out")
  (target "queensNoPureTrans.formatted")
   (action
    (with-outputs-to "queensNoPureTrans.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat queensNoPureTrans.out)))))

(rule
 (deps "queensNoPureTrans.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "queensNoPureTrans.ml" "queensNoPureTrans.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../interp.eff")
  (source_tree .))
   (target "interpFullOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml   "../interp.eff")))))

(rule
 (deps "interpFullOpt.out")
  (target "interpFullOpt.formatted")
   (action
    (with-outputs-to "interpFullOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpFullOpt.out)))))

(rule
 (deps "interpFullOpt.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "interpFullOpt.ml" "interpFullOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../interp.eff")
  (source_tree .))
   (target "interpNoFunSpec.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1022 "../interp.eff")))))

(rule
 (deps "interpNoFunSpec.out")
  (target "interpNoFunSpec.formatted")
   (action
    (with-outputs-to "interpNoFunSpec.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoFunSpec.out)))))

(rule
 (deps "interpNoFunSpec.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "interpNoFunSpec.ml" "interpNoFunSpec.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../interp.eff")
  (source_tree .))
   (target "interpNoCoerElim.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1021 "../interp.eff")))))

(rule
 (deps "interpNoCoerElim.out")
  (target "interpNoCoerElim.formatted")
   (action
    (with-outputs-to "interpNoCoerElim.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoCoerElim.out)))))

(rule
 (deps "interpNoCoerElim.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "interpNoCoerElim.ml" "interpNoCoerElim.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../interp.eff")
  (source_tree .))
   (target "interpNoCoerPush.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1019 "../interp.eff")))))

(rule
 (deps "interpNoCoerPush.out")
  (target "interpNoCoerPush.formatted")
   (action
    (with-outputs-to "interpNoCoerPush.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoCoerPush.out)))))

(rule
 (deps "interpNoCoerPush.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "interpNoCoerPush.ml" "interpNoCoerPush.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../interp.eff")
  (source_tree .))
   (target "interpNoHandReduc.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1015 "../interp.eff")))))

(rule
 (deps "interpNoHandReduc.out")
  (target "interpNoHandReduc.formatted")
   (action
    (with-outputs-to "interpNoHandReduc.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoHandReduc.out)))))

(rule
 (deps "interpNoHandReduc.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "interpNoHandReduc.ml" "interpNoHandReduc.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../interp.eff")
  (source_tree .))
   (target "interpNoPureTrans.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1007 "../interp.eff")))))

(rule
 (deps "interpNoPureTrans.out")
  (target "interpNoPureTrans.formatted")
   (action
    (with-outputs-to "interpNoPureTrans.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat interpNoPureTrans.out)))))

(rule
 (deps "interpNoPureTrans.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "interpNoPureTrans.ml" "interpNoPureTrans.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../range.eff")
  (source_tree .))
   (target "rangeFullOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml   "../range.eff")))))

(rule
 (deps "rangeFullOpt.out")
  (target "rangeFullOpt.formatted")
   (action
    (with-outputs-to "rangeFullOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeFullOpt.out)))))

(rule
 (deps "rangeFullOpt.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "rangeFullOpt.ml" "rangeFullOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../range.eff")
  (source_tree .))
   (target "rangeNoFunSpec.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1022 "../range.eff")))))

(rule
 (deps "rangeNoFunSpec.out")
  (target "rangeNoFunSpec.formatted")
   (action
    (with-outputs-to "rangeNoFunSpec.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoFunSpec.out)))))

(rule
 (deps "rangeNoFunSpec.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "rangeNoFunSpec.ml" "rangeNoFunSpec.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../range.eff")
  (source_tree .))
   (target "rangeNoCoerElim.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1021 "../range.eff")))))

(rule
 (deps "rangeNoCoerElim.out")
  (target "rangeNoCoerElim.formatted")
   (action
    (with-outputs-to "rangeNoCoerElim.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoCoerElim.out)))))

(rule
 (deps "rangeNoCoerElim.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "rangeNoCoerElim.ml" "rangeNoCoerElim.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../range.eff")
  (source_tree .))
   (target "rangeNoCoerPush.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1019 "../range.eff")))))

(rule
 (deps "rangeNoCoerPush.out")
  (target "rangeNoCoerPush.formatted")
   (action
    (with-outputs-to "rangeNoCoerPush.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoCoerPush.out)))))

(rule
 (deps "rangeNoCoerPush.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "rangeNoCoerPush.ml" "rangeNoCoerPush.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../range.eff")
  (source_tree .))
   (target "rangeNoHandReduc.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1015 "../range.eff")))))

(rule
 (deps "rangeNoHandReduc.out")
  (target "rangeNoHandReduc.formatted")
   (action
    (with-outputs-to "rangeNoHandReduc.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoHandReduc.out)))))

(rule
 (deps "rangeNoHandReduc.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "rangeNoHandReduc.ml" "rangeNoHandReduc.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../range.eff")
  (source_tree .))
   (target "rangeNoPureTrans.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1007 "../range.eff")))))

(rule
 (deps "rangeNoPureTrans.out")
  (target "rangeNoPureTrans.formatted")
   (action
    (with-outputs-to "rangeNoPureTrans.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat rangeNoPureTrans.out)))))

(rule
 (deps "rangeNoPureTrans.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "rangeNoPureTrans.ml" "rangeNoPureTrans.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../tree.eff")
  (source_tree .))
   (target "treeFullOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml   "../tree.eff")))))

(rule
 (deps "treeFullOpt.out")
  (target "treeFullOpt.formatted")
   (action
    (with-outputs-to "treeFullOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeFullOpt.out)))))

(rule
 (deps "treeFullOpt.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "treeFullOpt.ml" "treeFullOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../tree.eff")
  (source_tree .))
   (target "treeNoFunSpec.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1022 "../tree.eff")))))

(rule
 (deps "treeNoFunSpec.out")
  (target "treeNoFunSpec.formatted")
   (action
    (with-outputs-to "treeNoFunSpec.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeNoFunSpec.out)))))

(rule
 (deps "treeNoFunSpec.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "treeNoFunSpec.ml" "treeNoFunSpec.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../tree.eff")
  (source_tree .))
   (target "treeNoCoerElim.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1021 "../tree.eff")))))

(rule
 (deps "treeNoCoerElim.out")
  (target "treeNoCoerElim.formatted")
   (action
    (with-outputs-to "treeNoCoerElim.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeNoCoerElim.out)))))

(rule
 (deps "treeNoCoerElim.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "treeNoCoerElim.ml" "treeNoCoerElim.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../tree.eff")
  (source_tree .))
   (target "treeNoCoerPush.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1019 "../tree.eff")))))

(rule
 (deps "treeNoCoerPush.out")
  (target "treeNoCoerPush.formatted")
   (action
    (with-outputs-to "treeNoCoerPush.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeNoCoerPush.out)))))

(rule
 (deps "treeNoCoerPush.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "treeNoCoerPush.ml" "treeNoCoerPush.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../tree.eff")
  (source_tree .))
   (target "treeNoHandReduc.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1015 "../tree.eff")))))

(rule
 (deps "treeNoHandReduc.out")
  (target "treeNoHandReduc.formatted")
   (action
    (with-outputs-to "treeNoHandReduc.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeNoHandReduc.out)))))

(rule
 (deps "treeNoHandReduc.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "treeNoHandReduc.ml" "treeNoHandReduc.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../tree.eff")
  (source_tree .))
   (target "treeNoPureTrans.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1007 "../tree.eff")))))

(rule
 (deps "treeNoPureTrans.out")
  (target "treeNoPureTrans.formatted")
   (action
    (with-outputs-to "treeNoPureTrans.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat treeNoPureTrans.out)))))

(rule
 (deps "treeNoPureTrans.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "treeNoPureTrans.ml" "treeNoPureTrans.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../capability_benchmarks.eff")
  (source_tree .))
   (target "capability_benchmarksFullOpt.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml   "../capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksFullOpt.out")
  (target "capability_benchmarksFullOpt.formatted")
   (action
    (with-outputs-to "capability_benchmarksFullOpt.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksFullOpt.out)))))

(rule
 (deps "capability_benchmarksFullOpt.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "capability_benchmarksFullOpt.ml" "capability_benchmarksFullOpt.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../capability_benchmarks.eff")
  (source_tree .))
   (target "capability_benchmarksNoFunSpec.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1022 "../capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksNoFunSpec.out")
  (target "capability_benchmarksNoFunSpec.formatted")
   (action
    (with-outputs-to "capability_benchmarksNoFunSpec.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksNoFunSpec.out)))))

(rule
 (deps "capability_benchmarksNoFunSpec.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "capability_benchmarksNoFunSpec.ml" "capability_benchmarksNoFunSpec.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../capability_benchmarks.eff")
  (source_tree .))
   (target "capability_benchmarksNoCoerElim.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1021 "../capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksNoCoerElim.out")
  (target "capability_benchmarksNoCoerElim.formatted")
   (action
    (with-outputs-to "capability_benchmarksNoCoerElim.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksNoCoerElim.out)))))

(rule
 (deps "capability_benchmarksNoCoerElim.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "capability_benchmarksNoCoerElim.ml" "capability_benchmarksNoCoerElim.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../capability_benchmarks.eff")
  (source_tree .))
   (target "capability_benchmarksNoCoerPush.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1019 "../capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksNoCoerPush.out")
  (target "capability_benchmarksNoCoerPush.formatted")
   (action
    (with-outputs-to "capability_benchmarksNoCoerPush.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksNoCoerPush.out)))))

(rule
 (deps "capability_benchmarksNoCoerPush.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "capability_benchmarksNoCoerPush.ml" "capability_benchmarksNoCoerPush.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../capability_benchmarks.eff")
  (source_tree .))
   (target "capability_benchmarksNoHandReduc.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1015 "../capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksNoHandReduc.out")
  (target "capability_benchmarksNoHandReduc.formatted")
   (action
    (with-outputs-to "capability_benchmarksNoHandReduc.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksNoHandReduc.out)))))

(rule
 (deps "capability_benchmarksNoHandReduc.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "capability_benchmarksNoHandReduc.ml" "capability_benchmarksNoHandReduc.formatted")))

(rule
 (deps
 %{bin:eff}
  (file "../capability_benchmarks.eff")
  (source_tree .))
   (target "capability_benchmarksNoPureTrans.out")
    (action
     (with-outputs-to "%{target}"
      (with-accepted-exit-codes
       (or 0 1 2)
       (run eff --no-stdlib --compile-plain-ocaml  --optimizations 1007 "../capability_benchmarks.eff")))))

(rule
 (deps "capability_benchmarksNoPureTrans.out")
  (target "capability_benchmarksNoPureTrans.formatted")
   (action
    (with-outputs-to "capability_benchmarksNoPureTrans.formatted"
     (with-accepted-exit-codes (or 0 1 2)
      (run ocamlformat capability_benchmarksNoPureTrans.out)))))

(rule
 (deps "capability_benchmarksNoPureTrans.formatted")
  (alias generate_partial_benchmarks)
   (action
    (diff "capability_benchmarksNoPureTrans.ml" "capability_benchmarksNoPureTrans.formatted")))

