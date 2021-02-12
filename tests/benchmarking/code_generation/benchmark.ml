open Bechamel
open Toolkit
open Notty_unix

let suite : Benchmark_config.test_suite = Config.test_suite

let number_of_loops = 100

and number_of_queens = 8

and number_of_range = 100

and size_of_interp_expression = 200

let run_loop_pure = true

and run_loop_latent = true

and run_loop_incr = true

and run_loop_incr' = true

and run_loop_state = true

and run_queens_one = true

and run_queens_all = true

and run_interp = false

and run_range = true

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

let forget_value f x =
  let _ = f x in
  ()

let always_true f x =
  let _ = f x in
  true

let run_and_show_set (benchmark_set : 'a Benchmark_config.benchmark_set) =
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
    let set = suite.loop_benchmarks number_of_loops in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_loop_latent then (
    let set = suite.loop_latent_benchmarks number_of_loops in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_loop_incr then (
    let set = suite.loop_incr_benchmark number_of_loops in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_loop_incr' then
    List.iter
      (fun n ->
        let set = suite.loop_incr'_benchmark n in
        Printf.printf "%s (%d loops):\n" set.name set.param;
        run_and_show_set set)
      [ number_of_loops; 2 * number_of_loops ];
  if run_loop_state then (
    let set = suite.loop_incr_benchmark number_of_loops in
    Printf.printf "%s (%d loops):\n" set.name set.param;
    run_and_show_set set);
  if run_queens_one then (
    let set = suite.queens_one_cps_benchmark number_of_queens in
    Printf.printf "%s (%d queens):\n" set.name set.param;
    run_and_show_set set);
  if run_queens_one then (
    let set = suite.queens_one_benchmark number_of_queens in
    Printf.printf "%s (%d queens):\n" set.name set.param;
    run_and_show_set set);
  if run_queens_all then (
    let set = suite.queens_all_benchmark number_of_queens in
    Printf.printf "%s (%d queens):\n" set.name set.param;
    run_and_show_set set);
  if run_interp then (
    let set = suite.interpreter_benchmark size_of_interp_expression in
    Printf.printf "%s (size: %d):\n" set.name size_of_interp_expression;
    run_and_show_set set);
  if run_interp then (
    let set = suite.interpreter_benchmark (size_of_interp_expression * 5) in
    Printf.printf "%s (size: %d):\n" set.name size_of_interp_expression;
    run_and_show_set set);
  if run_range then (
    let set = suite.range_benchmarks number_of_range in
    Printf.printf "%s :\n" set.name;
    run_and_show_set set)
