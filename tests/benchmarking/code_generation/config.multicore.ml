let add_benchmark b (benchmark_set : 'a -> 'a Benchmark_config.benchmark_set) n
    =
  let benchmark_set = benchmark_set n in
  { benchmark_set with benchmarks = benchmark_set.benchmarks @ [ b ] }

let test_suite =
  let base_suite = Benchmark_config.default_test_suite in
  let interpreter_benchmark =
    add_benchmark
      ( "Multicore",
        Benchmark_config.forget_value NativeMulticore.InterpMulticore.bigTest,
        fun n -> NativeMulticore.InterpMulticore.bigTest n = -1 )
      base_suite.interpreter_benchmark
  in
  { base_suite with interpreter_benchmark }
