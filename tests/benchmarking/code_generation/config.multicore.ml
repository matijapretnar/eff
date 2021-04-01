open NativeMulticore
open Benchmark_config

let add_benchmark b (benchmark_set : 'a -> 'a benchmark_set) n =
  let benchmark_set = benchmark_set n in
  { benchmark_set with benchmarks = benchmark_set.benchmarks @ [ b ] }

let test_suite =
  let base_suite = default_test_suite in
  let interpreter_benchmark =
    add_benchmark
      ( "Multicore",
        forget_value InterpMulticore.bigTest,
        fun n -> InterpMulticore.bigTest n = -1 )
      base_suite.interpreter_benchmark
  in
  let interpreter_state_benchmark =
    add_benchmark
      ( "Multicore",
        forget_value InterpMulticore.testState,
        fun n -> InterpMulticore.testState n = -1 )
      base_suite.interpreter_state_benchmark
  in

  let range_benchmarks =
    base_suite.range_benchmarks
    |> add_benchmark
         ( "Multicore",
           forget_value RangeMulticore.test,
           always_true RangeMulticore.test )
    |> add_benchmark
         ( "Multicore custom list type",
           forget_value RangeMulticoreCustomList.test,
           always_true RangeMulticoreCustomList.test )
  in
  let loop_benchmarks =
    base_suite.loop_benchmarks
    |> add_benchmark
         ( "Multicore",
           forget_value LoopMulticore.test_pure,
           fun n -> LoopMulticore.test_pure n = () )
  in
  let loop_latent_benchmarks =
    base_suite.loop_latent_benchmarks
    |> add_benchmark
         ( "Multicore",
           forget_value LoopMulticore.loop_latent,
           fun n -> LoopMulticore.loop_latent n = () )
  in
  let loop_incr_benchmark =
    base_suite.loop_incr_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value LoopMulticore.test_incr,
           fun n -> LoopMulticore.test_incr n = n )
  in
  let loop_incr'_benchmark =
    base_suite.loop_incr'_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value LoopMulticore.test_incr',
           fun n -> LoopMulticore.test_incr' n = n )
  in
  let loop_state_benchmark =
    base_suite.loop_state_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value LoopMulticore.test_state,
           fun n -> LoopMulticore.test_state n = n )
  in
  let queens_one_benchmark =
    base_suite.queens_one_benchmark
    |> add_benchmark
         ( "Multicore translated",
           forget_value QueensMulticoreTranslated.queens_one_option,
           always_true QueensMulticoreTranslated.queens_one_option )
  in
  let queens_one_cps_benchmark =
    base_suite.queens_one_cps_benchmark
    |> add_benchmark
         ( "Multicore translated",
           forget_value QueensMulticoreTranslated.queens_one_cps,
           always_true QueensMulticoreTranslated.queens_one_cps )
  in
  let queens_all_benchmark =
    base_suite.queens_all_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value QueensMulticore.queens_all,
           always_true QueensMulticore.queens_all )
    |> add_benchmark
         ( "Multicore translated",
           forget_value QueensMulticoreTranslated.queens_all,
           always_true QueensMulticoreTranslated.queens_all )
  in
  let tree_benchmark =
    base_suite.tree_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value TreeMulticore.test_general,
           always_true TreeMulticore.test_general )
  in
  let state_tree_benchmark =
    base_suite.state_tree_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value TreeMulticore.test_leaf_state,
           always_true TreeMulticore.test_leaf_state )
    |> add_benchmark
         ( "Multicore state handler",
           forget_value TreeMulticore.test_leaf_state_effect,
           always_true TreeMulticore.test_leaf_state_effect )
  in
  let state_with_update_tree_benchmark =
    base_suite.state_with_update_tree_benchmark
    |> add_benchmark
         ( "Multicore",
           forget_value TreeMulticore.test_leaf_state_update,
           always_true TreeMulticore.test_leaf_state_update )
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
    queens_one_cps_benchmark;
    tree_benchmark;
    state_tree_benchmark;
    state_with_update_tree_benchmark;
  }
