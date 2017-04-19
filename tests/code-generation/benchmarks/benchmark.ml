open Core.Std
open Core_bench.Std

let number_of_loops = 10000
and number_of_queens = 8
and number_of_range = 10000

let run_loop_pure = false
and run_loop_latent = false
and run_loop_incr = false
and run_loop_state = false
and run_queens_one = false
and run_queens_all = false
and run_parser = false
and run_interp = false
and run_small_interp = true
and run_range = true

let () =
  if run_loop_pure then begin
  Printf.printf "LOOP PURE BENCHMARK (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> LoopNoOptImpure._test_pure_11 number_of_loops);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> LoopOptImpure._test_pure_11 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> LoopNoOptPure._test_pure_11 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> LoopOptPure._test_pure_11 number_of_loops);
      Bench.Test.create ~name:"Hand written" (fun () -> LoopHandWritten.test_pure number_of_loops);
      Bench.Test.create ~name:"Native" (fun () -> LoopNative.test_pure number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_latent then begin
  Printf.printf "LOOP LATENT BENCHMARK (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> LoopNoOptImpure._test_latent_22 number_of_loops);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> LoopOptImpure._test_latent_22 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> LoopNoOptPure._test_latent_22 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> LoopOptPure._test_latent_22 number_of_loops);
      Bench.Test.create ~name:"Hand written" (fun () -> LoopHandWritten.test_latent number_of_loops);
      Bench.Test.create ~name:"Native" (fun () -> LoopNative.test_latent number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_incr then begin
  Printf.printf "LOOP INCR BENCHMARK (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> LoopNoOptImpure._test_incr_38 number_of_loops);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> LoopOptImpure._test_incr_38 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> LoopNoOptPure._test_incr_38 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> LoopOptPure._test_incr_38 number_of_loops);
      Bench.Test.create ~name:"Hand written" (fun () -> LoopHandWritten.test_incr number_of_loops);
      Bench.Test.create ~name:"Native" (fun () -> LoopNative.test_incr number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_state then begin
  Printf.printf "LOOP STATE BENCHMARK (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> LoopNoOptImpure._test_state_59 number_of_loops);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> LoopOptImpure._test_state_59 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> LoopNoOptPure._test_state_59 number_of_loops);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> LoopOptPure._test_state_59 number_of_loops);
      Bench.Test.create ~name:"Hand written" (fun () -> LoopHandWritten.test_state number_of_loops);
      Bench.Test.create ~name:"Native" (fun () -> LoopNative.test_state number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_one then begin
  Printf.printf "QUEENS ONE CPS BENCHMARK (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_one_cps_96 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_one_cps_96 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_one_cps_96 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_one_cps_96 number_of_queens);
      Bench.Test.create ~name:"Hand written" (fun () -> QueensHandWritten.queens_one_cps number_of_queens);
      Bench.Test.create ~name:"Native - CPS" (fun () -> QueensNative.queens_one_cps number_of_queens);
      Bench.Test.create ~name:"Native - exceptions" (fun () -> QueensNative.queens_one_exceptions number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_one then begin
  Printf.printf "QUEENS ONE OPTION BENCHMARK (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_one_option_94 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_one_option_94 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_one_option_94 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_one_option_94 number_of_queens);
      Bench.Test.create ~name:"Hand written" (fun () -> QueensHandWritten.queens_one_option number_of_queens);
      Bench.Test.create ~name:"Native - option" (fun () -> QueensNative.queens_one_option number_of_queens);
      Bench.Test.create ~name:"Native - exceptions" (fun () -> QueensNative.queens_one_exceptions number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Hand written" (fun () -> QueensHandWritten.queens_all number_of_queens);
      Bench.Test.create ~name:"Native" (fun () -> QueensNative.queens_all number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_parser then begin
  Printf.printf "PARSER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> ParserNoOptImpure._parseTest_91 ());
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> ParserOptImpure._parseTest_91 ());
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> ParserNoOptPure._parseTest_91 ());
      (* Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> ParserOptPure._parseTest_91 ()); *)
      Bench.Test.create ~name:"Native" (fun () -> ParserNative.parseTest ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_interp then begin
  Printf.printf "INTERPRETER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> InterpNoOptImpure._bigTest_179 ());
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> InterpOptImpure._bigTest_179 ());
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> InterpNoOptPure._bigTest_179 ());
      (* Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> InterpOptPure._bigTest_179 ()); *)
      Bench.Test.create ~name:"Native" (fun () -> InterpNative.bigTest ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_interp then begin
  Printf.printf "FLAT INTERPRETER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> FlatNoOptImpure._bigTest_201 ());
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> FlatOptImpure._bigTest_201 ());
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> FlatNoOptPure._bigTest_201 ());
      (* Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> FlatOptPure._bigTest_201 ()); *)
      (* Bench.Test.create ~name:"Native" (fun () -> FlatNative.bigTest ()); *)
    ]);
  Printf.printf "\n\n"
  end;
  if run_small_interp then begin
  Printf.printf "SMALL INTERPRETER BENCHMARK:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> Interp_small.bigTest ());
      (* Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> FlatOptPure._bigTest_201 ()); *)
      Bench.Test.create ~name:"Native" (fun () -> InterpNative.bigTest ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_range then begin
  Printf.printf "RANGE BENCHMARKS:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> RangeNoPureNoOpt._test_222 number_of_range);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> RangeOptNoPure._test_222 number_of_range);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> RangePureNoOpt._test_222 number_of_range);
       Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> RangeOptPure._test_222 number_of_range);
      (* Bench.Test.create ~name:"Native" (fun () -> FlatNative.bigTest ()); *)
    ]);
  Printf.printf "\n\n"
  end;
