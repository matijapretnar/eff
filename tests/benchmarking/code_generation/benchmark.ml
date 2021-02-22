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

and run_interp = true

and run_range = true

let benchmark test =
  let ols =
    Analyze.ols ~bootstrap:0 ~r_square:true ~predictors:Measure.[| run |]
  in
  let instances =
    Instance.[ minor_allocated; major_allocated; monotonic_clock; promoted ]
  in
  let cfg =
    (* Benchmark.cfg ~limit:5000 ~quota:(Time.second 5.0) ~kde:(Some 1000) () *)
    Benchmark.cfg ~limit:500 ~quota:(Time.second 0.5) ~kde:(Some 100) ()
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
  let results, b = benchmark test in
  Hashtbl.iter (fun k _ -> print_endline k) b;
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
  if run_interp then
    List.iter
      (fun n ->
        let set = suite.interpreter_benchmark n in
        Printf.printf "%s (size: %d):\n" set.name set.param;
        run_and_show_set set)
      [
        size_of_interp_expression;
        2 * size_of_interp_expression;
        4 * size_of_interp_expression;
        8 * size_of_interp_expression;
      ];
  if run_range then (
    let set = suite.range_benchmarks number_of_range in
    Printf.printf "%s :\n" set.name;
    run_and_show_set set)
