open Bechamel
open Toolkit
open Notty_unix

let benchmark test =
  let ols =
    Analyze.ols ~bootstrap:0 ~r_square:true ~predictors:Measure.[| run |]
  in
  let instances =
    Instance.[ minor_allocated; major_allocated; monotonic_clock; promoted ]
  in
  let cfg = Benchmark.cfg ~limit:5000 ~quota:(Time.second 5.0) () in
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

(* Modified module to also include percentages *)
module Multiple = struct
  open Bechamel_notty
  open Bechamel
  open Notty

  [@@@warning "-26-27"]

  let image_of_header ~rect (results : 'a results) =
    let instances = Hashtbl.fold (fun k _ a -> k :: a) results [] in
    let _, result = hashtbl_choose results in
    let max_length_of_names =
      Hashtbl.fold (fun name _ -> max (String.length name)) result 0
    in
    let max_length_of_instances =
      List.fold_right
        (fun label -> max (String.length label))
        instances max_length_of_values
    in
    let max_length_of_fields =
      max max_length_of_values max_length_of_instances
    in

    let tt =
      List.map
        (fun _ -> [ break_t 1 1; line (max_length_of_fields + 4) 1 ])
        instances
      |> List.concat
    in
    let tt = corner_tl 1 1 :: line (max_length_of_names + 4) 1 :: tt in
    let tt = tt @ [ corner_tr 1 1 ] in

    let cc =
      List.map
        (fun instance ->
          let rest = max_length_of_instances - String.length instance + 2 in
          [
            sideline 1 1;
            I.(string A.empty instance |> I.hpad 2 0);
            I.void rest 0;
          ])
        instances
      |> List.concat
    in
    let cc =
      sideline 1 1
      :: I.(string A.(st italic) "name")
      :: I.void max_length_of_names 1
      :: cc
    in
    let cc = cc @ [ sideline 1 1 ] in

    let bb =
      List.map
        (fun _ -> [ cross 1 1; line (max_length_of_fields + 4) 1 ])
        instances
      |> List.concat
    in
    let bb = break_l 1 1 :: line (max_length_of_names + 4) 1 :: bb in
    let bb = bb @ [ break_r 1 1 ] in

    let open Notty in
    I.vcat [ I.hcat tt; I.hcat cc; I.hcat bb ]

  let calculate_ols : predictor:string -> Analyze.OLS.t -> float =
   fun ~predictor v ->
    if not (List.mem predictor (Analyze.OLS.predictors v)) then
      Fmt.invalid_arg "Predictor %s was not computed in %a." predictor
        Analyze.OLS.pp v;

    let responder = Analyze.OLS.responder v in
    let unit_responder = Unit.unit_of_label responder in
    let unit_predictor = Unit.unit_of_label predictor in
    match Analyze.OLS.estimates v with
    | None ->
        assert false (* (I.string A.(bg red ++ st bold) "#none", 999999.0) *)
    | Some values -> (
        match
          List.fold_left2
            (fun a v p -> if String.equal p predictor then Some v else a)
            None values (Analyze.OLS.predictors v)
        with
        | Some value -> value
        | None -> assert false)

  let percentage_image_of_ols_fields ~max_length_of_names
      ~max_length_of_instances ~rect ~predictor img name
      (tests : Analyze.OLS.t list) (values : float list) min_values =
    let max_length_of_fields =
      max max_length_of_values max_length_of_instances
    in
    let ll =
      [
        sideline 1 1;
        I.(string A.empty name |> hpad 2 0);
        I.void (max_length_of_names + 4 - 2 - String.length name) 1;
      ]
    in
    let responder v = Analyze.OLS.responder v in
    let unit_responder responder = Unit.unit_of_label responder in
    let unit_predictor v = Unit.unit_of_label predictor in
    let attrs v =
      match Analyze.OLS.r_square v with
      | Some r_square ->
          if r_square <= 0.5 then A.(bg red ++ st bold)
          else if r_square <= 0.75 then A.(fg red)
          else if r_square <= 0.90 then A.(fg yellow)
          else if r_square <= 0.98 then A.(fg green)
          else A.(bg green ++ st bold)
      | None -> A.(fg white)
    in
    let cc =
      List.map2
        (fun test value mn ->
          let resp = responder test in
          let s =
            Fmt.strf "%6.04f %s/%s | %4.0f%%" value (unit_responder resp)
              (unit_predictor test)
              (value /. mn *. 100.0)
          in
          let k = I.string (attrs test) s in
          [ sideline 1 1; I.(hsnap ~align:`Right (max_length_of_fields + 4)) k ])
        tests values
      |> List.map2 (fun x f -> f x) min_values
      |> List.concat
    in
    let rr = [ sideline 1 1 ] in

    let open Notty.Infix in
    img <-> I.hcat (ll @ cc @ rr)

  let image_of_ols_results :
      ?sort:(string -> string -> int) ->
      rect:rect ->
      predictor:string ->
      Analyze.OLS.t results ->
      image =
   fun ?(sort = String.compare) ~rect ~predictor results ->
    let header = image_of_header ~rect results in
    let instances = Hashtbl.fold (fun k _ a -> k :: a) results [] in
    let _, result = hashtbl_choose results in
    let max_length_of_names =
      Hashtbl.fold (fun name _ -> max (String.length name)) result 0
    in
    let max_length_of_instances =
      List.fold_right
        (fun label -> max (String.length label))
        instances max_length_of_values
    in

    let tests = Hashtbl.fold (fun name _ a -> name :: a) result [] in
    let tests = List.sort sort tests in
    (* Run all tests *)
    let number_results =
      List.map
        (fun tname ->
          let instances =
            Hashtbl.fold
              (fun label result a -> Hashtbl.find result tname :: a)
              results []
          in
          let scores = List.map (calculate_ols ~predictor) instances in
          (instances, scores))
        tests
    in
    let scores = List.map snd number_results in
    let rec transpose l =
      match l with
      | [] -> []
      | [] :: xss -> transpose xss
      | (x :: xs) :: xss ->
          (x :: List.map List.hd xss) :: transpose (xs :: List.map List.tl xss)
    in
    let top =
      List.map (List.fold_left min Float.max_float) (transpose scores)
    in
    let header_and_body_with_percentages =
      List.fold_left2
        (fun img name (tests, vals) ->
          percentage_image_of_ols_fields ~max_length_of_names
            ~max_length_of_instances ~rect ~predictor img name tests vals top)
        header tests number_results
    in
    let max_length_of_fields =
      max max_length_of_values max_length_of_instances
    in

    let bottom =
      List.map
        (fun _ -> [ break_b 1 1; line (max_length_of_fields + 4) 1 ])
        instances
      |> List.concat
    in
    let bottom = corner_bl 1 1 :: line (max_length_of_names + 4) 1 :: bottom in
    let bottom = bottom @ [ corner_br 1 1 ] in

    let open Notty.Infix in
    header_and_body_with_percentages <-> I.hcat bottom
end

let img (window, results) =
  Multiple.image_of_ols_results ~rect:window ~predictor:Measure.run results

let run_and_show test =
  let window =
    match winsize Unix.stdout with
    | Some (w, h) -> { Bechamel_notty.w; h }
    | None -> { Bechamel_notty.w = 80; h = 1 }
  in
  let results, _b = benchmark test in
  (* Hashtbl.iter (fun k _ -> print_endline k) b; *)
  img (window, results) |> eol |> output_image

let run_and_show_set
    (benchmark_set : 'a Benchmark_suite.Benchmark_config.benchmark_set) param =
  run_and_show
  @@ Test.make_grouped ~name:"" ~fmt:"%s%s"
       (List.map
          (fun (name, fn) ->
            Test.make ~name
              (Staged.stage (fun () ->
                   try ignore (fn param)
                   with e ->
                     Printf.printf "Test: %s failed at runtime with: %s \n" name
                       (Printexc.to_string e))))
          benchmark_set.benchmarks);
  Printf.printf "\n\n"

let suite = Benchmark_suite.Config.test_suite

let run_benchmarks set =
  List.iter
    (fun param ->
      Printf.printf "%s (%d %s):\n" set.Benchmark_suite.Benchmark_config.name
        param set.parameter_unit;
      run_and_show_set set param)
    set.parameters

let () =
  run_benchmarks suite.loop_benchmarks;

  run_benchmarks suite.loop_latent_benchmarks;

  run_benchmarks suite.loop_incr_benchmark;

  run_benchmarks suite.loop_incr'_benchmark;

  run_benchmarks suite.loop_state_benchmark;

  run_benchmarks suite.queens_one_benchmark;

  run_benchmarks suite.queens_all_benchmark;

  run_benchmarks suite.interpreter_benchmark;

  run_benchmarks suite.interpreter_state_benchmark

let () =
  run_benchmarks suite.loop_pure_optimizer;

  run_benchmarks suite.loop_pure_optimizer;

  run_benchmarks suite.loop_incr_optimizer;

  run_benchmarks suite.loop_latent_optimizer;

  run_benchmarks suite.loop_state_optimizer
