open Bechamel
open Toolkit

let instance = Instance.monotonic_clock

let limit = 100

let second_quota = 0.1

module StringMap = Map.Make (String)
module IntMap = Map.Make (Int)

let measure_benchmark benchmark baseline =
  let ols =
    Analyze.ols ~bootstrap:0 ~r_square:true ~predictors:Measure.[| run |]
  in
  let cfg = Benchmark.cfg ~limit ~quota:(Time.second second_quota) () in
  let raw_results = Benchmark.all cfg [ instance ] benchmark in
  let analyzed_results =
    List.map (fun instance -> Analyze.all ols instance raw_results) [ instance ]
  in
  let merged_results = Analyze.merge ols [ instance ] analyzed_results in
  let benchmark_results =
    Hashtbl.fold
      (fun instance_label instance_result benchmark_results ->
        let instance_results =
          Hashtbl.fold
            (fun case_label case_estimates instance_results ->
              match Analyze.OLS.estimates case_estimates with
              | Some [ case_result ] ->
                  StringMap.add case_label case_result instance_results
              | _ -> assert false)
            instance_result StringMap.empty
        in
        (instance_label, instance_results) :: benchmark_results)
      merged_results []
  in
  let instance_results =
    match benchmark_results with
    | [ (_instance_label, instance_results) ] -> instance_results
    | _ -> assert false
  in
  let baseline_result = StringMap.find baseline instance_results in
  let normalized_results =
    StringMap.map (fun result -> result /. baseline_result) instance_results
  in
  normalized_results

let transpose_nested_map map_by_a_by_b =
  IntMap.fold
    (fun a of_a map_by_b_by_a ->
      StringMap.fold
        (fun b v map_by_b_by_a ->
          let of_b =
            StringMap.find_opt b map_by_b_by_a
            |> Option.value ~default:IntMap.empty
          in
          let of_b' = IntMap.add a v of_b in
          StringMap.add b of_b' map_by_b_by_a)
        of_a map_by_b_by_a)
    map_by_a_by_b StringMap.empty

let measure_benchmark_set
    (benchmark_set : 'a Benchmark_suite.Benchmark_config.benchmark_set) =
  let baseline =
    match benchmark_set.benchmarks with
    | (baseline, _) :: _ -> baseline
    | _ -> assert false
  in
  let measure_at_param param =
    print_int param;
    (* flush_all (); *)
    let benchmark_at_param =
      Test.make_grouped ~name:"" ~fmt:"%s%s"
        (List.map
           (fun (name, fn) ->
             Test.make ~name (Staged.stage (fun () -> ignore (fn param))))
           benchmark_set.benchmarks)
    in
    measure_benchmark benchmark_at_param baseline
  in
  let results_by_param =
    List.fold_left
      (fun measurements param ->
        IntMap.add param (measure_at_param param) measurements)
      IntMap.empty benchmark_set.parameters
  in
  transpose_nested_map results_by_param

let display_benchmark_set_results
    (set : 'a Benchmark_suite.Benchmark_config.benchmark_set) benchmark_results
    =
  StringMap.iter
    (fun test_label test_results ->
      let chan =
        open_out (Printf.sprintf "tables/%s-%s.table" set.filename test_label)
      in
      Printf.fprintf chan "# %s: %s\n" set.name test_label;
      IntMap.iter
        (fun param param_result ->
          Printf.fprintf chan "%d %d\n" param
            (int_of_float (100. *. param_result)))
        test_results;
      close_out chan)
    benchmark_results;
  print_newline ()

let run_benchmark_set (set : 'a Benchmark_suite.Benchmark_config.benchmark_set)
    =
  print_endline set.name;
  let results = measure_benchmark_set set in
  display_benchmark_set_results set results

let suite = Benchmark_suite.Config.test_suite

let _ = run_benchmark_set suite.loop_benchmarks

let _ = run_benchmark_set suite.loop_latent_benchmarks

let _ = run_benchmark_set suite.loop_incr_benchmark

let _ = run_benchmark_set suite.loop_incr'_benchmark

let _ = run_benchmark_set suite.loop_state_benchmark

let _ = run_benchmark_set suite.queens_one_benchmark

let _ = run_benchmark_set suite.queens_all_benchmark

let _ = run_benchmark_set suite.interpreter_benchmark

let _ = run_benchmark_set suite.interpreter_state_benchmark

let _ = run_benchmark_set suite.range_benchmarks

let _ = run_benchmark_set suite.tree_benchmark

let _ = run_benchmark_set suite.loop_pure_optimizer

let _ = run_benchmark_set suite.loop_incr_optimizer

let _ = run_benchmark_set suite.loop_latent_optimizer

let _ = run_benchmark_set suite.loop_state_optimizer
