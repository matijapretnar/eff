type 'a benchmark_set = {
  name : string;
  filename : string;
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
  (* partially optimized versions *)
  loop_pure_optimizer : unit benchmark_set;
  loop_latent_optimizer : unit benchmark_set;
  loop_incr_optimizer : int benchmark_set;
  loop_state_optimizer : int benchmark_set;
}

let loop_pure_optimizer =
  {
    name = "LOOP PURE PARTIAL OPTIMIZED BENCHMARK";
    filename = "loop_pure_optimizer";
    benchmarks =
      [
        ("native", Partial_optimizations.loop_pure__native);
        ("no-opts", Partial_optimizations.loop_pure__direct);
        ("purity-aware", Partial_optimizations.loop_pure__purity_aware);
        ("full-opt", Partial_optimizations.loop_pure__opt);
      ];
    parameters =
      [
        10_000;
        20_000;
        30_000;
        40_000;
        50_000;
        60_000;
        70_000;
        80_000;
        90_000;
        100_000;
      ];
    parameter_unit = "loops";
  }

let loop_latent_optimizer =
  {
    name = "LOOP LATENT PARTIAL OPTIMIZED BENCHMARK";
    filename = "loop_latent_optimizer";
    benchmarks =
      [
        ("native", Partial_optimizations.loop_latent__native);
        ("no-opts", Partial_optimizations.loop_latent__direct);
        ("purity-aware", Partial_optimizations.loop_latent__purity_aware);
        ("full-opt", Partial_optimizations.loop_latent__opt);
      ];
    parameters =
      [
        10_000;
        20_000;
        30_000;
        40_000;
        50_000;
        60_000;
        70_000;
        80_000;
        90_000;
        100_000;
      ];
    parameter_unit = "loops";
  }

let loop_incr_optimizer =
  {
    name = "LOOP INCR PARTIAL OPTIMIZED BENCHMARK";
    filename = "loop_incr_optimizer";
    benchmarks =
      [
        ("native", Partial_optimizations.loop_incr__native);
        ("no-opts", Partial_optimizations.loop_incr__direct);
        ("purity-aware", Partial_optimizations.loop_incr__purity_aware);
        ("full-opt", Partial_optimizations.loop_incr__opt);
      ];
    parameters =
      [
        10_000;
        20_000;
        30_000;
        40_000;
        50_000;
        60_000;
        70_000;
        80_000;
        90_000;
        100_000;
      ];
    parameter_unit = "loops";
  }

let loop_state_optimizer =
  {
    name = "LOOP STATE PARTIAL OPTIMIZED BENCHMARK";
    filename = "loop_state_optimizer";
    benchmarks =
      [
        ("native", Partial_optimizations.loop_state__native);
        ("no-opts", Partial_optimizations.loop_state__direct);
        ("purity-aware", Partial_optimizations.loop_state__purity_aware);
        ("full-opt", Partial_optimizations.loop_state__opt);
      ];
    parameters =
      [
        10_000;
        20_000;
        30_000;
        40_000;
        50_000;
        60_000;
        70_000;
        80_000;
        90_000;
        100_000;
      ];
    parameter_unit = "loops";
  }

let loop_benchmarks =
  {
    name = "LOOP PURE BENCHMARK";
    filename = "loop_benchmarks";
    benchmarks =
      [ ("native", LoopNative.test_pure); ("generated", LoopOpt.test_pure) ];
    parameters = [ 1000; 2000; 3000; 4000; 5000; 6000; 7000; 8000; 9000; 10000 ];
    parameter_unit = "loops";
  }

let loop_latent_benchmarks =
  {
    name = "LOOP LATENT BENCHMARK";
    filename = "loop_latent_benchmarks";
    benchmarks =
      [
        ("native", LoopNative.test_latent);
        ("generated", extract_value LoopOpt.test_latent);
      ];
    parameters = [ 1000; 2000; 3000; 4000; 5000; 6000; 7000; 8000; 9000; 10000 ];
    parameter_unit = "loops";
  }

let loop_incr_benchmark =
  {
    name = "LOOP INCR BENCHMARK";
    filename = "loop_incr";
    benchmarks =
      [ ("native", LoopNative.test_incr); ("generated", LoopOpt.test_incr) ];
    parameters = [ 1000; 2000; 3000; 4000; 5000; 6000; 7000; 8000; 9000; 10000 ];
    parameter_unit = "loops";
  }

let loop_incr'_benchmark =
  {
    name = "LOOP INCR' BENCHMARK";
    filename = "loop_incr'";
    benchmarks =
      [ ("native", LoopNative.test_incr'); ("generated", LoopOpt.test_incr') ];
    parameters = [ 1000; 2000; 3000; 4000; 5000; 6000; 7000; 8000; 9000; 10000 ];
    parameter_unit = "loops";
  }

let loop_state_benchmark =
  {
    name = "LOOP STATE BENCHMARK";
    filename = "loop_state";
    benchmarks =
      [ ("native", LoopNative.test_state); ("generated", LoopOpt.test_state) ];
    parameters = [ 1000; 2000; 3000; 4000; 5000; 6000; 7000; 8000; 9000; 10000 ];
    parameter_unit = "loops";
  }

let queens_one_benchmark =
  {
    name = "QUEENS ONE SOLUTION BENCHMARK";
    filename = "queens_one";
    benchmarks =
      [
        ("native-option", ignore_value QueensNative.queens_one_option);
        ("generated-option", ignore_value QueensOpt.queens_one_option);
        ("native-cps", ignore_value QueensNative.queens_one_cps);
        ("generated-cps", ignore_value QueensOpt.queens_one_cps);
        ( "generated-capabilities-code",
          ignore_value Capability_benchmarksOpt.queens_all );
        ("native-cap", ignore_value Capability_benchmarks_native.findSolution);
        ( "capabilities",
          ignore_value Capability_benchmarks_cps_paper.findSolution_generated );
        (* ("eio-cps", ignore_value QueensEffInOcaml.queens_one_cps); *)
        (* ("eio-opt", ignore_value QueensEffInOcaml.queens_one_option); *)
        (* ("hia-cps", ignore_value QueensHandlersInAction.queens_one_cps); *)
        (* ("hia-opt", ignore_value QueensHandlersInAction.queens_one_option); *)
      ];
    parameters = [ 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20 ];
    parameter_unit = "queens";
  }

let queens_all_benchmark =
  {
    name = "QUEENS ALL BENCHMARK";
    filename = "queens_all";
    benchmarks =
      [
        ("native", ignore_value QueensNative.queens_all);
        ("generated", ignore_value QueensOpt.queens_all);
        ( "capabilities",
          ignore_value Capabilities_our_versions.queensAll_generated );
        (* ("eio", ignore_value QueensEffInOcaml.queens_all); *)
        (* ("eio", ignore_value QueensHandlersInAction.queens_all); *)
      ];
    parameters = [ 8; 9; 10; 11; 12; 13 ];
    parameter_unit = "queens";
  }

let interpreter_benchmark =
  {
    name = "INTERPRETER BENCHMARK";
    filename = "interpreter";
    benchmarks =
      [
        ("native-pure", InterpNative.bigTestOption);
        ("native-exception", InterpNative.bigTestException);
        (* ("generated", InterpOpt.bigTest); *)
        ("generated-loop-100", InterpOpt.bigTestLoop);
        ("capabilities-loop-100", Capabilities_our_versions.bigTestLoop);
      ];
    parameters = [ 200; 2 * 200; 4 * 200; 8 * 200; 16 * 200; 32 * 200 ];
    parameter_unit = "size";
  }

let interpreter_state_benchmark =
  {
    name = "INTERPRETER STATE BENCHMARK";
    filename = "interpreter_state";
    benchmarks =
      [
        ("native", InterpNative.testState);
        (* ("generated", InterpOpt.testState); *)
        ("generated-loop-100", InterpOpt.testStateLoop);
        ("capabilities-loop-100", Capabilities_our_versions.testStateLoop);
      ];
    parameters = [ 200; 2 * 200; 4 * 200; 8 * 200; 16 * 200; 32 * 200 ];
    parameter_unit = "size";
  }

let range_benchmarks =
  {
    name = "RANGE BENCHMARK";
    filename = "range_benchmarks";
    benchmarks =
      [
        ("native", ignore_value RangeNative.test);
        ("generated", ignore_value RangeOpt.test);
        ( "capabilities",
          ignore_value Capabilities_our_versions.rangeBenchmark_generated );
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100; 16 * 100; 32 * 100 ];
    parameter_unit = "";
  }

let tree_benchmark =
  {
    name = "TREE BENCHMARK";
    filename = "tree";
    benchmarks =
      [
        ("native", TreeNative.test_general);
        (* ("generated", TreeOpt.test_general); *)
        ("generated-loop", TreeOpt.test_general_loop);
        ("capabilities-loop", Capabilities_our_versions.test_general_loop);
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100; 16 * 100; 32 * 100 ];
    parameter_unit = "leaf_val";
  }

let state_tree_benchmark =
  {
    name = "STATE TREE BENCHMARK";
    filename = "state_tree";
    benchmarks =
      [
        ("native-pure", TreeNative.test_leaf_pure_state);
        ("native-ref", TreeNative.test_leaf_state);
        (* ("generated", TreeOpt.test_leaf_state); *)
        ("generated-loop", TreeOpt.test_leaf_state_loop);
        ("capabilities-loop", Capabilities_our_versions.test_leaf_state);
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100; 16 * 100; 32 * 100 ];
    parameter_unit = "leaf_val";
  }

let state_with_update_tree_benchmark =
  {
    name = "STATE TREE BENCHMARK";
    filename = "state_with_update_tree";
    benchmarks =
      [
        ("native", TreeNative.test_leaf_state_update);
        (* ("generated", TreeOpt.test_leaf_state_update); *)
        ("generated-loop", TreeOpt.test_leaf_state_update_loop);
        (* ("generated-merged", TreeOpt.test_leaf_state_update_merged_handler); *)
        ( "generated-merged-loop",
          TreeOpt.test_leaf_state_update_merged_handler_loop );
        ("capabilities-loop", Capabilities_our_versions.test_leaf_state_update);
      ];
    parameters = [ 100; 2 * 100; 4 * 100; 8 * 100; 16 * 100; 32 * 100 ];
    parameter_unit = "leaf_val";
  }

let count_benchmark =
  {
    name = "COUNT BENCHMARK";
    filename = "count";
    benchmarks =
      [
        ("native", Capability_benchmarks_native.testCount);
        ("generated", Capability_benchmarksOpt.testCount);
        ("capabilities", Capability_benchmarks_cps_paper.handledCount_generated);
      ];
    parameters =
      [ 1_000_000; 2 * 1_000_000; 4 * 1_000_000; 8 * 1_000_000; 16 * 1_000_000 ];
    parameter_unit = "N";
  }

let generator_benchmark =
  {
    name = "GENERATOR BENCHMARK";
    filename = "generator";
    benchmarks =
      [
        ("native", ignore_value Capability_benchmarks_native.testGenerator);
        ("generated", ignore_value Capability_benchmarksOpt.testGenerator);
        ( "capabilities",
          ignore_value
            Capability_benchmarks_cps_paper.handledGenerator_generated );
      ];
    parameters =
      [ 1_000_000; 2 * 1_000_000; 4 * 1_000_000; 8 * 1_000_000; 16 * 1_000_000 ];
    parameter_unit = "N";
  }

let default_test_suite =
  {
    loop_benchmarks;
    loop_latent_benchmarks;
    loop_incr_benchmark;
    loop_incr'_benchmark;
    loop_state_benchmark;
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
    loop_pure_optimizer;
    loop_latent_optimizer;
    loop_incr_optimizer;
    loop_state_optimizer;
  }
