type 'a benchmark_set = {
  name : string;
  benchmarks : (string * (int -> 'a)) list;
  parameter_unit : string;
  parameters : int list;
}

let extract_value f x = OcamlHeader.run (f x)

let ignore_value f x = ignore (Sys.opaque_identity (f x))

type test_suite = {
  loop_benchmarks : unit benchmark_set;
  loop_latent_benchmarks : unit benchmark_set;
  loop_incr_benchmark : int benchmark_set;
  loop_incr'_benchmark : int benchmark_set;
  loop_state_benchmark : int benchmark_set;
  queens_one_cps_benchmark : unit benchmark_set;
  queens_one_benchmark : unit benchmark_set;
  queens_all_benchmark : unit benchmark_set;
  interpreter_benchmark : int benchmark_set;
  interpreter_state_benchmark : int benchmark_set;
  range_benchmarks : unit benchmark_set;
  tree_benchmark : int benchmark_set;
  state_tree_benchmark : int benchmark_set;
  state_with_update_tree_benchmark : int benchmark_set;
  count_benchmark : int benchmark_set;
  generator_benchmark : unit benchmark_set;
  queen_capabilty_benchmarks : unit benchmark_set;
}

let loop_benchmarks =
  {
    name = "LOOP PURE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", LoopOpt.test_pure);
        ("Native", LoopNative.test_pure);
      ];
    parameters = [ 1000 ];
    parameter_unit = "loops";
  }

let loop_latent_benchmarks =
  {
    name = "LOOP LATENT BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", extract_value LoopOpt.test_latent);
        ("Native", LoopNative.test_latent);
      ];
    parameters = [ 1000 ];
    parameter_unit = "loops";
  }

let loop_incr_benchmark =
  {
    name = "LOOP INCR BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", LoopOpt.test_incr);
        ("Native", LoopNative.test_incr);
      ];
    parameters = [ 1000 ];
    parameter_unit = "loops";
  }

let loop_incr'_benchmark =
  {
    name = "LOOP INCR' BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", LoopOpt.test_incr');
        ("Native", LoopNative.test_incr');
      ];
    parameters = [ 1000 ];
    parameter_unit = "loops";
  }

let loop_state_benchmark =
  {
    name = "LOOP STATE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", LoopOpt.test_state);
        ("Native", LoopNative.test_state);
      ];
    parameters = [ 1000 ];
    parameter_unit = "loops";
  }

let queens_one_cps_benchmark =
  {
    name = "QUEENS ONE CPS BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", ignore_value QueensOpt.queens_one_cps);
        ("Native", ignore_value QueensNative.queens_one_cps);
      ];
    parameters = [ 8 ];
    parameter_unit = "queens";
  }

let queens_one_benchmark =
  {
    name = "QUEENS ONE OPTION BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", ignore_value QueensOpt.queens_one_option);
        ("Native", ignore_value QueensNative.queens_one_option);
      ];
    parameters = [ 8 ];
    parameter_unit = "queens";
  }

let queens_all_benchmark =
  {
    name = "QUEENS ALL BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", ignore_value QueensOpt.queens_all);
        ("Native", ignore_value QueensNative.queens_all);
      ];
    parameters = [ 8 ];
    parameter_unit = "queens";
  }

let interpreter_benchmark =
  {
    name = "INTERPRETER BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", InterpOpt.bigTest);
        ("Native exception", InterpNative.bigTestException);
        ("Native option", InterpNative.bigTestOption);
      ];
    parameters = [ 200; 2 * 200; 4 * 200; 8 * 200 ];
    parameter_unit = "size";
  }

let interpreter_state_benchmark =
  {
    name = "INTERPRETER STATE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", InterpOpt.testState);
        ("Native pure", InterpNative.testState);
      ];
    parameters = [ 200; 2 * 200; 4 * 200; 8 * 200 ];
    parameter_unit = "size";
  }

let range_benchmarks =
  {
    name = "RANGE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", ignore_value RangeOpt.test);
        ("Native", ignore_value RangeNative.test);
      ];
    parameters = [ 100 ];
    parameter_unit = "";
  }

let tree_benchmark =
  {
    name = "TREE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", TreeOpt.test_general);
        ("Native", TreeNative.test_general);
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100 ];
    parameter_unit = "leaf_val";
  }

let state_tree_benchmark =
  {
    name = "STATE TREE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", TreeOpt.test_leaf_state);
        ("Native", TreeNative.test_leaf_state);
        ("Native pure state", TreeNative.test_leaf_pure_state);
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100 ];
    parameter_unit = "leaf_val";
  }

let state_with_update_tree_benchmark =
  {
    name = "STATE TREE BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", TreeOpt.test_leaf_state_update);
        ( "Generated, optimized merged",
          TreeOpt.test_leaf_state_update_merged_handler );
        ("Native", TreeNative.test_leaf_state_update);
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100 ];
    parameter_unit = "leaf_val";
  }

let count_benchmark =
  {
    name = "COUNT BENCHMARK";
    benchmarks =
      [
        ("Generated, optimized", Capability_benchmarksOpt.testCount);
        ("Native", Capability_benchmarks_native.testCount);
        ("CPS paper", Capability_benchmarks_cps_paper.handledCount_generated);
      ];
    parameters = [ 1_000_000; 2 * 1_000_000; 4 * 1_000_000; 8 * 1_000_000 ];
    parameter_unit = "N";
  }

let generator_benchmark =
  {
    name = "GENERATOR BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          ignore_value Capability_benchmarksOpt.testGenerator );
        ("Native", ignore_value Capability_benchmarks_native.testGenerator);
        ( "CPS paper",
          ignore_value
            Capability_benchmarks_cps_paper.handledGenerator_generated );
      ];
    parameters = [ 1_000_000; 2 * 1_000_000; 4 * 1_000_000; 8 * 1_000_000 ];
    parameter_unit = "N";
  }

let queen_capabilty_benchmarks =
  {
    name = "QUEEN CAPABILTY BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          ignore_value Capability_benchmarksOpt.queens_all );
        ("Native", ignore_value Capability_benchmarks_native.findSolution);
        ( "CPS paper",
          ignore_value Capability_benchmarks_cps_paper.findSolution_generated );
      ];
    parameters = [ 16 ];
    parameter_unit = "N";
  }

let default_test_suite =
  {
    loop_benchmarks;
    loop_latent_benchmarks;
    loop_incr_benchmark;
    loop_incr'_benchmark;
    loop_state_benchmark;
    queens_one_cps_benchmark;
    queens_one_benchmark;
    queens_all_benchmark;
    interpreter_benchmark;
    interpreter_state_benchmark;
    range_benchmarks;
    tree_benchmark;
    state_tree_benchmark;
    state_with_update_tree_benchmark;
    count_benchmark;
    generator_benchmark;
    queen_capabilty_benchmarks;
  }
