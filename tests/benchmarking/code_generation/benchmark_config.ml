type 'a benchmark_set = {
  name : string;
  benchmarks : (string * ('a -> unit) * ('a -> bool)) list;
  param : 'a;
}

let forget_value f x =
  let _ = f x in
  ()

let always_true f x =
  let _ = f x in
  true

type test_suite = {
  loop_benchmarks : int -> int benchmark_set;
  loop_latent_benchmarks : int -> int benchmark_set;
  loop_incr_benchmark : int -> int benchmark_set;
  loop_incr'_benchmark : int -> int benchmark_set;
  loop_state_benchmark : int -> int benchmark_set;
  queens_one_cps_benchmark : int -> int benchmark_set;
  queens_one_benchmark : int -> int benchmark_set;
  queens_all_benchmark : int -> int benchmark_set;
  interpreter_benchmark : int -> int benchmark_set;
  range_benchmarks : int -> int benchmark_set;
  tree_benchmark : int -> int benchmark_set;
  state_tree_benchmark : int -> int benchmark_set;
}

let loop_benchmarks number_of_loops =
  {
    name = "LOOP PURE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt.test_pure,
          fun n -> LoopOpt.test_pure n = () );
        ( "Native",
          forget_value LoopNative.test_pure,
          fun n -> LoopNative.test_pure n = () );
      ];
    param = number_of_loops;
  }

let loop_latent_benchmarks number_of_loops =
  {
    name = "LOOP LATENT BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt.test_latent,
          always_true LoopOpt.test_latent );
        ( "Native",
          forget_value LoopNative.test_latent,
          always_true LoopNative.test_latent );
      ];
    param = number_of_loops;
  }

let loop_incr_benchmark num =
  {
    name = "LOOP INCR BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt.test_incr,
          fun n -> LoopOpt.test_incr n = num );
        ( "Native",
          forget_value LoopNative.test_incr,
          fun n -> LoopNative.test_incr n = num );
      ];
    param = num;
  }

let loop_incr'_benchmark num =
  {
    name = "LOOP INCR' BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt.test_incr',
          fun n -> LoopOpt.test_incr' n = num );
        ( "Native",
          forget_value LoopNative.test_incr',
          fun n -> LoopNative.test_incr' n = num );
      ];
    param = num;
  }

let loop_state_benchmark num =
  {
    name = "LOOP STATE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt.test_state,
          fun n -> LoopOpt.test_state n = num );
        ( "Native",
          forget_value LoopNative.test_state,
          fun n -> LoopNative.test_state n = num );
      ];
    param = num;
  }

let queens_one_cps_benchmark number_of_queens =
  {
    name = "QUEENS ONE CPS BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value QueensOpt.queens_one_cps,
          always_true QueensOpt.queens_one_cps );
        ( "Native",
          forget_value QueensNative.queens_one_cps,
          always_true QueensNative.queens_one_cps );
      ];
    param = number_of_queens;
  }

let queens_one_benchmark number_of_queens =
  {
    name = "QUEENS ONE OPTION BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value QueensOpt.queens_one_option,
          always_true QueensOpt.queens_one_option );
        ( "Native",
          forget_value QueensNative.queens_one_option,
          always_true QueensNative.queens_one_option );
      ];
    param = number_of_queens;
  }

let queens_all_benchmark number_of_queens =
  {
    name = "QUEENS ALL BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value QueensOpt.queens_all,
          always_true QueensOpt.queens_all );
        ( "Native",
          forget_value QueensNative.queens_all,
          always_true QueensNative.queens_all );
      ];
    param = number_of_queens;
  }

let interpreter_benchmark n =
  {
    name = "INTERPRETER BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value InterpOpt.bigTest,
          fun n -> InterpOpt.bigTest n = -1 );
        ( "Native exception",
          forget_value InterpNative.bigTestException,
          fun n -> InterpNative.bigTestException n = -1 );
        ( "Native option",
          forget_value InterpNative.bigTestOption,
          fun n -> InterpNative.bigTestOption n = -1 );
      ];
    param = n;
  }

let range_benchmarks number_of_range =
  {
    name = "RANGE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value RangeOpt.test,
          always_true RangeOpt.test );
        ("Native", forget_value RangeNative.test, always_true RangeNative.test);
      ];
    param = number_of_range;
  }

let tree_benchmark number =
  {
    name = "TREE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value TreeOpt.test_general,
          always_true TreeOpt.test_general );
        ( "Native",
          forget_value TreeNative.test_general,
          always_true TreeNative.test_general );
      ];
    param = number;
  }

let state_tree_benchmark number =
  {
    name = "STATE TREE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value TreeOpt.test_leaf_state,
          always_true TreeOpt.test_leaf_state );
        ( "Native",
          forget_value TreeNative.test_leaf_state,
          always_true TreeNative.test_leaf_state );
      ];
    param = number;
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
    range_benchmarks;
    tree_benchmark;
    state_tree_benchmark;
  }
