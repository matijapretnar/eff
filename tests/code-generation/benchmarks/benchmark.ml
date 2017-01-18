open Core.Std
open Core_bench.Std

let number_of_loops = 10000
and number_of_queens_one = 8
and number_of_queens_all = 8
and number_of_loops_effect = 100000

let run_loop = false
and run_loop_acc = false
and run_queens_one = false
and run_queens_all = false
and run_interp = false
and run_parser_short = false
and run_loopEffect = true

let () =
  if run_loop then begin
  Printf.printf "LOOP BENCHMARK (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 7cc7606 (18-03-2016)" (fun () -> Loop7cc7606._loop_281 number_of_loops);
      Bench.Test.create ~name:"Handlers - ce4263d (10-10-2016)" (fun () -> Loopce4263d._loop_279 number_of_loops);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> LoopHandlers.loop number_of_loops);
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
      Bench.Test.create ~name:"Handlers - 29c8f51e (22-12-2016)" (fun () -> Queens29c8f51e._queens_one_322 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - faebf456 (02-01-2017)" (fun () -> Queensfaebf456._queens_one_319 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> QueensHandlers.queens_one number_of_queens_one);
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
      Bench.Test.create ~name:"Handlers - 29c8f51e (22-12-2016)" (fun () -> Queens29c8f51e._queens_all_324 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - faebf456 (02-01-2017)" (fun () -> Queensfaebf456._queens_all_321 number_of_queens_one);
      Bench.Test.create ~name:"Handlers - hand-written" (fun () -> QueensHandlers.queens_all number_of_queens_all);
      Bench.Test.create ~name:"Native - lists" (fun () -> QueensNative.queens_all number_of_queens_all);
    ]);
  Printf.printf "\n\n"
  end;
  if run_interp then begin
  Printf.printf "INTERPRETER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - not optimized" (fun () -> Interpunopt._bigTest_424 ());
      Bench.Test.create ~name:"Handlers - 4f3a6da1 (04-01-2017)" (fun () -> Interp4f3a6da1._bigTest_424 ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_parser_short then begin
  Printf.printf "PARSER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - not optimized" (fun () -> Parserunopt._parseTest_348 ());
      Bench.Test.create ~name:"Handlers - faebf456 (03-01-2017)" (fun () -> Parserfaebf456._parseTest_348 ());
      Bench.Test.create ~name:"Handlers - 4f3a6da1 (04-01-2017)" (fun () -> Parser4f3a6da1._parseTest_348 ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_loopEffect then begin
  Printf.printf "LOOP WITH EFFECT WITH UNIT RESULT BENCHMARK (%d loops):\n" number_of_loops_effect;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 9ef2c167 (10-01-2017)" (fun () -> LoopEffect9ef2c167._loop_w_handler0_316 number_of_loops_effect);
      Bench.Test.create ~name:"Native" (fun () -> LoopEffectNative.loop_w_handler0 number_of_loops_effect);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loopEffect then begin
  Printf.printf "LOOP WITH EFFECT WITH INT RESULT BENCHMARK (%d loops):\n" number_of_loops_effect;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 9ef2c167 (10-01-2017)" (fun () -> LoopEffect9ef2c167._loop_w_handler1_319 number_of_loops_effect);
      Bench.Test.create ~name:"Native" (fun () -> LoopEffectNative.loop_w_handler1 number_of_loops_effect);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loopEffect then begin
  Printf.printf "LOOP WITH EFFECT WITH TUPLE RESULT BENCHMARK (%d loops):\n" number_of_loops_effect;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 9ef2c167 (10-01-2017)" (fun () -> LoopEffect9ef2c167._loop_w_handler2_322 number_of_loops_effect);
      Bench.Test.create ~name:"Native" (fun () -> LoopEffectNative.loop_w_handler2 number_of_loops_effect);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loopEffect then begin
  Printf.printf "LOOP WITH EFFECT NO INCREMENT RESULT BENCHMARK (%d loops):\n" number_of_loops_effect;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 9ef2c167 (10-01-2017)" (fun () -> LoopEffect9ef2c167._loop_w_handler3_325 number_of_loops_effect);
      Bench.Test.create ~name:"Native" (fun () -> LoopEffectNative.loop_w_handler3 number_of_loops_effect);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loopEffect then begin
  Printf.printf "LOOP WITH EFFECT WITH STATE BENCHMARK (%d loops):\n" number_of_loops_effect;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Handlers - 9ef2c167 (10-01-2017)" (fun () -> LoopEffect9ef2c167._loop_w_handler4_328 number_of_loops_effect);
      Bench.Test.create ~name:"Native" (fun () -> LoopEffectNative.loop_w_handler4 number_of_loops_effect);
    ]);
  Printf.printf "\n\n"
  end;
