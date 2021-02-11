open Bechamel
open Toolkit
open Notty_unix

let number_of_loops = 100

and number_of_queens = 8

and number_of_range = 10

let run_loop_pure = false

and run_loop_latent = false

and run_loop_incr = false

and run_loop_incr' = false

and run_loop_state = false

and run_queens_one = true

and run_queens_all = true

and run_interp = false

and run_range = false

open Bechamel
open Toolkit

let benchmark test =
  let ols =
    Analyze.ols ~bootstrap:0 ~r_square:true ~predictors:Measure.[| run |]
  in
  let instances =
    Instance.[ minor_allocated; major_allocated; monotonic_clock; promoted ]
  in
  let cfg =
    Benchmark.cfg ~limit:500 ~quota:(Time.second 0.5) ~kde:(Some 500) ()
  in
  let raw_results = Benchmark.all cfg instances test in
  let results =
    List.map (fun instance -> Analyze.all ols instance raw_results) instances
  in
  let results = Analyze.merge ols instances results in
  (results, raw_results)

let () =
  List.iter
    (fun v -> Bechamel_notty.Unit.add v (Measure.unit v))
    Instance.[ minor_allocated; major_allocated; monotonic_clock; promoted ]

let img (window, results) =
  Bechamel_notty.Multiple.image_of_ols_results ~rect:window
    ~predictor:Measure.run results

let run_and_show test =
  let window =
    match winsize Unix.stdout with
    | Some (w, h) -> { Bechamel_notty.w; h }
    | None -> { Bechamel_notty.w = 80; h = 1 }
  in
  let results, _ = benchmark test in
  img (window, results) |> eol |> output_image

let st = Staged.stage

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

let loop_benchmarks =
  {
    name = "LOOP PURE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt._test_pure_16,
          fun n -> LoopOpt._test_pure_16 n = () );
        ( "Hand written",
          forget_value LoopHandWritten.test_pure,
          fun n -> LoopHandWritten.test_pure n = () );
        ( "Native",
          forget_value LoopNative.test_pure,
          fun n -> LoopNative.test_pure n = () );
      ];
    param = number_of_loops;
  }

let loop_latent_benchmarks =
  {
    name = "LOOP LATENT BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value LoopOpt._test_latent_41,
          always_true LoopOpt._test_latent_41 );
        ( "Hand written",
          forget_value LoopHandWritten.test_latent,
          always_true LoopHandWritten.test_latent );
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
          forget_value LoopOpt._test_incr_60,
          fun n -> LoopOpt._test_incr_60 n = num );
        ( "Hand written",
          forget_value LoopHandWritten.test_incr,
          fun n -> LoopHandWritten.test_incr n = num );
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
          forget_value LoopOpt._test_incr'_97,
          fun n -> LoopOpt._test_incr'_97 n = num );
        ( "Hand written",
          forget_value LoopHandWritten.test_incr',
          fun n -> LoopHandWritten.test_incr' n = num );
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
          forget_value LoopOpt._test_state_150,
          fun n -> LoopOpt._test_state_150 n = num );
        ( "Hand written",
          forget_value LoopHandWritten.test_state,
          fun n -> LoopHandWritten.test_state n = num );
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
          forget_value QueensOpt._queens_one_cps_238,
          always_true QueensOpt._queens_one_cps_238 );
        ( "Hand written",
          forget_value QueensHandWritten.queens_one_cps,
          always_true QueensHandWritten.queens_one_cps );
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
          forget_value QueensOpt._queens_one_option_140,
          always_true QueensOpt._queens_one_option_140 );
        ( "Hand written",
          forget_value QueensHandWritten.queens_one_option,
          always_true QueensHandWritten.queens_one_option );
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
          forget_value QueensOpt._queens_all_188,
          always_true QueensOpt._queens_all_188 );
        ( "Hand written",
          forget_value QueensHandWritten.queens_all,
          always_true QueensHandWritten.queens_all );
        ( "Native",
          forget_value QueensNative.queens_all,
          always_true QueensNative.queens_all );
      ];
    param = number_of_queens;
  }

let interpreter_benchmark =
  {
    name = "INTERPRETER BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value InterpOpt._bigTest_5,
          always_true InterpOpt._bigTest_5 );
      ];
    param = ();
  }

let range_benchmarks number_of_range =
  {
    name = "RANGE BENCHMARK";
    benchmarks =
      [
        ( "Generated, optimized",
          forget_value RangeOpt._test_1,
          always_true RangeOpt._test_1 );
        ("Native", forget_value RangeNative.test, always_true RangeNative.test);
      ];
    param = number_of_range;
  }

let run_and_show_set benchmark_set =
  List.iter
    (fun (name, _, tester) ->
      try
        if not @@ tester benchmark_set.param then
          Printf.printf "Test: %s was wrong\n" name
      with e ->
        Printf.printf "Test: %s failed at runtime with: %s \n" name
          (Printexc.to_string e))
    benchmark_set.benchmarks;
  run_and_show
  @@ Test.make_grouped ~name:"" ~fmt:"%s%s"
       (List.map
          (fun (name, fn, _) ->
            Test.make ~name (st (fun () -> fn benchmark_set.param)))
          benchmark_set.benchmarks);
  Printf.printf "\n\n"

let () =
  if run_loop_pure then (
    let set = loop_benchmarks in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_loop_latent then (
    let set = loop_latent_benchmarks in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set loop_latent_benchmarks);
  if run_loop_incr then (
    let set = loop_incr_benchmark number_of_loops in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_loop_incr' then
    List.iter
      (fun n ->
        let set = loop_incr'_benchmark n in
        Printf.printf "%s (%d loops):\n" set.name set.param;
        run_and_show_set set)
      [ number_of_loops; 2 * number_of_loops ];
  if run_loop_state then (
    let set = loop_incr_benchmark number_of_loops in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_queens_one then (
    let set = queens_one_cps_benchmark number_of_queens in
    Printf.printf "%s (%d queens):\n" set.name set.param;
    run_and_show_set set);
  if run_queens_one then (
    let set = queens_one_benchmark number_of_queens in
    Printf.printf "%s (%d queens):\n" set.name set.param;
    run_and_show_set set);
  if run_queens_all then (
    let set = queens_all_benchmark number_of_queens in
    Printf.printf "%s (%d queens):\n" set.name set.param;
    run_and_show_set set);
  if run_interp then (
    let set = interpreter_benchmark in
    Printf.printf "%s :\n" set.name;
    run_and_show_set set);
  if run_range then (
    let set = range_benchmarks number_of_range in
    Printf.printf "%s :\n" set.name;
    run_and_show_set set)
