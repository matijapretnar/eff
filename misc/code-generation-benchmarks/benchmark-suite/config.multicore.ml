open NativeMulticore
open Benchmark_config

let add_benchmark b benchmark_set =
  { benchmark_set with benchmarks = benchmark_set.benchmarks @ [ b ] }

let test_suite =
  let base_suite = default_test_suite in
  let interpreter_benchmark =
    add_benchmark
      ("multicore", InterpMulticore.bigTest)
      base_suite.interpreter_benchmark
  in
  let interpreter_state_benchmark =
    add_benchmark
      ("multicore", InterpMulticore.testState)
      base_suite.interpreter_state_benchmark
  in

  let range_benchmarks =
    base_suite.range_benchmarks
    |> add_benchmark ("multicore", fun n -> ignore (RangeMulticore.test n))
    |> add_benchmark
         ( "multicore-custom-list-type",
           fun n -> ignore (RangeMulticoreCustomList.test n) )
  in
  let loop_benchmarks =
    base_suite.loop_benchmarks
    |> add_benchmark ("multicore", LoopMulticore.test_pure)
  in
  let loop_latent_benchmarks =
    base_suite.loop_latent_benchmarks
    |> add_benchmark ("multicore", LoopMulticore.loop_latent)
  in
  let loop_incr_benchmark =
    base_suite.loop_incr_benchmark
    |> add_benchmark ("multicore", LoopMulticore.test_incr)
  in
  let loop_incr'_benchmark =
    base_suite.loop_incr'_benchmark
    |> add_benchmark ("multicore", LoopMulticore.test_incr')
  in
  let loop_state_benchmark =
    base_suite.loop_state_benchmark
    |> add_benchmark ("multicore", LoopMulticore.test_state)
  in
  let queens_one_benchmark =
    base_suite.queens_one_benchmark
    |> add_benchmark
         ( "multicore-translated",
           fun n -> ignore (QueensMulticoreTranslated.queens_one_option n) )
  in
  let queens_one_benchmark =
    base_suite.queens_one_benchmark
    |> add_benchmark
         ( "multicore-translated",
           fun n -> ignore (QueensMulticoreTranslated.queens_one_cps n) )
  in
  let queens_all_benchmark =
    base_suite.queens_all_benchmark
    (* |> add_benchmark
         ("multicore", fun n -> ignore (QueensMulticore.queens_all n)) *)
    |> add_benchmark
         ( "multicore-translated",
           fun n -> ignore (QueensMulticoreTranslated.queens_all n) )
  in
  let tree_benchmark =
    base_suite.tree_benchmark
    |> add_benchmark ("multicore", TreeMulticore.test_general)
  in
  let state_tree_benchmark =
    base_suite.state_tree_benchmark
    |> add_benchmark ("multicore", TreeMulticore.test_leaf_state)
    |> add_benchmark
         ("multicore-state-handler", TreeMulticore.test_leaf_state_effect)
  in
  let state_with_update_tree_benchmark =
    base_suite.state_with_update_tree_benchmark
    |> add_benchmark ("multicore", TreeMulticore.test_leaf_state_update)
  in
  let count_benchmark =
    base_suite.count_benchmark
    |> add_benchmark ("multicore", CapabilityBenchmarks.testCount)
  in
  let generator_benchmark =
    base_suite.generator_benchmark
    |> add_benchmark
         ("multicore", fun n -> ignore (CapabilityBenchmarks.testGenerator n))
  in
  {
    base_suite with
    interpreter_benchmark;
    interpreter_state_benchmark;
    range_benchmarks;
    loop_benchmarks;
    loop_latent_benchmarks;
    loop_incr_benchmark;
    loop_incr'_benchmark;
    loop_state_benchmark;
    queens_all_benchmark;
    queens_one_benchmark;
    tree_benchmark;
    state_tree_benchmark;
    state_with_update_tree_benchmark;
    count_benchmark;
    generator_benchmark;
  }
