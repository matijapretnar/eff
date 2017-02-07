open Core.Std
open Core_bench.Std

let number_of_loops = 10000
and number_of_queens_one = 8
and number_of_queens_all = 8
and number_of_loops_effect = 100000

let run_loop = true
and run_loop_acc = true
and run_queens_one = true
and run_queens_all = true
and run_interp = true
and run_parser_short = true
and run_loopEffect = true

let () =
  if run_loop then begin
  Printf.printf "LOOP BENCHMARK (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 7cc7606 (18-03-2016)" (fun () -> Loop7cc7606._loop_281 number_of_loops);
      Bench.Test.create ~name:"Handlers - ce4263d (10-10-2016)" (fun () -> Loopce4263d._loop_279 number_of_loops);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> LoopHandlers.loop number_of_loops);
      Bench.Test.create ~name:"Handlers - 14b03fe (07-02-2017)" (fun () -> Loop14b03fe._loop_216 number_of_loops);
      Bench.Test.create ~name:"Native - option" (fun () -> LoopNative.loop_option number_of_loops);
      Bench.Test.create ~name:"Native - fail" (fun () -> LoopNative.loop_fail number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_acc then begin
  Printf.printf "LOOP BENCHMARK WITH TAIL CALL(%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 7cc7606 (18-03-2016)" (fun () -> Loop7cc7606.run (Loop7cc7606._loop_acc_292 number_of_loops) 0);
      Bench.Test.create ~name:"Handlers - ce4263d (10-10-2016)" (fun () -> Loopce4263d.run (Loopce4263d._loop_acc_290 number_of_loops) 0);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> LoopHandlers.loop_acc number_of_loops 0);
      Bench.Test.create ~name:"Handlers - 14b03fe (07-02-2017)" (fun () -> Loop14b03fe._loop_acc_227 number_of_loops 0);
      Bench.Test.create ~name:"Native - option" (fun () -> LoopNative.loop_acc_option number_of_loops 0);
      Bench.Test.create ~name:"Native - fail" (fun () -> LoopNative.loop_acc_fail number_of_loops 0);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_one then begin
  Printf.printf "FIRST SOLUTION OF n-QUEENS (%d queens):\n" number_of_queens_one;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - not optimized" (fun () -> Queensunopt._queens_one_326 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - 7cc7606 (18-03-2016)" (fun () -> Queens7cc7606._queens_one_350 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - ce4263d (10-10-2016)" (fun () -> Queensce4263d._queens_one_348 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - 4bf5385 (01-12-2016)" (fun () -> Queens4bf5385._queens_one_322 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - 29c8f51 (22-12-2016)" (fun () -> Queens29c8f51._queens_one_322 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - faebf45 (02-01-2017)" (fun () -> Queensfaebf45._queens_one_319 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> QueensHandlers.queens_one number_of_queens_one);
      Bench.Test.create ~name:"Handlers - 14b03fe (07-02-2017 tweaked)" (fun () -> Queens14b03fe._queens_one_285 number_of_queens_all);
      Bench.Test.create ~name:"Native - option" (fun () -> QueensNative.queens_one_option number_of_queens_one);
      Bench.Test.create ~name:"Native - fail" (fun () -> QueensNative.queens_one_fail number_of_queens_one);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "ALL SOLUTIONS OF n-QUEENS (%d queens):\n" number_of_queens_all;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - not optimized" (fun () -> Queensunopt._queens_all_328 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - 7cc7606 (18-03-2016)" (fun () -> Queens7cc7606._queens_all_352 number_of_queens_all);
      Bench.Test.create ~name:"Handlers - 29c8f51 (22-12-2016)" (fun () -> Queens29c8f51._queens_all_324 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - faebf45 (02-01-2017)" (fun () -> Queensfaebf45._queens_all_321 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> QueensHandlers.queens_all number_of_queens_all);
      Bench.Test.create ~name:"Handlers - 14b03fe (07-02-2017 tweaked)" (fun () -> Queens14b03fe._queens_all_289 number_of_queens_all);
      Bench.Test.create ~name:"Native - lists" (fun () -> QueensNative.queens_all number_of_queens_all);
    ]);
  Printf.printf "\n\n"
  end;
  if run_interp then begin
  Printf.printf "INTERPRETER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - not optimized" (fun () -> Interpunopt._bigTest_424 ());
      Bench.Test.create ~name:"Handlers - 4f3a6da (04-01-2017)" (fun () -> Interp4f3a6da._bigTest_424 ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_parser_short then begin
  Printf.printf "PARSER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - not optimized" (fun () -> Parserunopt._parseTest_348 ());
      Bench.Test.create ~name:"Handlers - faebf45 (03-01-2017)" (fun () -> Parserfaebf45._parseTest_348 ());
      Bench.Test.create ~name:"Handlers - 4f3a6da (04-01-2017)" (fun () -> Parser4f3a6da._parseTest_348 ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_loopEffect then begin
  Printf.printf "LOOP WITH EFFECT (%d loops):\n" number_of_loops_effect;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Handlers - 9ef2c16 (10-01-2017)" (fun () -> LoopEffect9ef2c16._loop_w_handler0_316 number_of_loops_effect); *)
      (* Bench.Test.create ~name:"Handlers - 14b03fe (07-02-2017 tweaked)" (fun () -> LoopEffect14b03fe._loop_w_handler0_270 number_of_loops_effect); *)
      (* Bench.Test.create ~name:"Handlers - tick" (fun () -> LoopEffect14b03fe._loop_w_handler0_270 number_of_loops_effect); *)
      Bench.Test.create ~name:"Handlers - state" (fun () -> LoopEffect2d319b2._loop_w_handler3_279 number_of_loops_effect);
      Bench.Test.create ~name:"Handlers - state" (fun () -> LoopEffect2d319b2._loop_w_handler4_282 number_of_loops_effect);
      Bench.Test.create ~name:"Native - pure" (fun () -> LoopEffectNative.loop_w_handler0 number_of_loops_effect);
      Bench.Test.create ~name:"Native - incr" (fun () -> LoopEffectNative.loop_w_handler1 number_of_loops_effect);
      Bench.Test.create ~name:"Native - state" (fun () -> LoopEffectNative.loop_w_handler2 number_of_loops_effect);
    ]);
  Printf.printf "\n\n"
  end;
