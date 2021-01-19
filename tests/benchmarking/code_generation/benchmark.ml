open Core
open Core_bench
open Loop
open Queens
open Interp
open Range

let number_of_loops = 10

and number_of_queens = 8

and number_of_range = 10

let run_loop_pure = false

and run_loop_latent = false

and run_loop_incr = false

and run_loop_incr' = false

and run_loop_state = false

and run_queens_one = false

and run_queens_all = false

and run_interp = false

and run_range = false

let () =
  print_endline "heeelou";
  if run_loop_pure then (
    Printf.printf "LOOP PURE BENCHMARK (%d loops):\n" number_of_loops;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               LoopNooptImpure._test_pure_11 number_of_loops);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               LoopOptImpure._test_pure_11 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               LoopNooptPure._test_pure_11 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               LoopOptPure._test_pure_11 number_of_loops);
           Bench.Test.create ~name:"Hand written" (fun () ->
               LoopHandWritten.test_pure number_of_loops);
           Bench.Test.create ~name:"Native" (fun () ->
               LoopNative.test_pure number_of_loops);
         ]);
    Printf.printf "\n\n");
  if run_loop_latent then (
    Printf.printf "LOOP LATENT BENCHMARK (%d loops):\n" number_of_loops;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               LoopNooptImpure._test_latent_22 number_of_loops);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               LoopOptImpure._test_latent_22 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               LoopNooptPure._test_latent_22 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               LoopOptPure._test_latent_22 number_of_loops);
           Bench.Test.create ~name:"Hand written" (fun () ->
               LoopHandWritten.test_latent number_of_loops);
           Bench.Test.create ~name:"Native" (fun () ->
               LoopNative.test_latent number_of_loops);
         ]);
    Printf.printf "\n\n");
  if run_loop_incr then (
    Printf.printf "LOOP INCR BENCHMARK (%d loops):\n" number_of_loops;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               LoopNooptImpure._test_incr_38 number_of_loops);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               LoopOptImpure._test_incr_38 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               LoopNooptPure._test_incr_38 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               LoopOptPure._test_incr_38 number_of_loops);
           Bench.Test.create ~name:"Hand written" (fun () ->
               LoopHandWritten.test_incr number_of_loops);
           Bench.Test.create ~name:"Native" (fun () ->
               LoopNative.test_incr number_of_loops);
         ]);
    Printf.printf "\n\n");
  if run_loop_incr' then (
    Printf.printf "LOOP INCR' BENCHMARK (%d loops):\n" 100;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               LoopNooptImpure._test_incr'_47 100);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               LoopOptImpure._test_incr'_47 100);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               LoopNooptPure._test_incr'_47 100);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               LoopOptPure._test_incr'_47 100);
           Bench.Test.create ~name:"Hand written" (fun () ->
               LoopHandWritten.test_incr' 100);
           Bench.Test.create ~name:"Native" (fun () ->
               LoopNative.test_incr' 100);
         ]);
    Printf.printf "\n\n");
  if run_loop_incr' then (
    Printf.printf "LOOP INCR' BENCHMARK (%d loops):\n" 200;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               LoopNooptImpure._test_incr'_47 200);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               LoopOptImpure._test_incr'_47 200);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               LoopNooptPure._test_incr'_47 200);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               LoopOptPure._test_incr'_47 200);
           Bench.Test.create ~name:"Hand written" (fun () ->
               LoopHandWritten.test_incr' 200);
           Bench.Test.create ~name:"Native" (fun () ->
               LoopNative.test_incr' 200);
         ]);
    Printf.printf "\n\n");
  if run_loop_state then (
    Printf.printf "LOOP STATE BENCHMARK (%d loops):\n" number_of_loops;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               LoopNooptImpure._test_state_68 number_of_loops);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               LoopOptImpure._test_state_68 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               LoopNooptPure._test_state_68 number_of_loops);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               LoopOptPure._test_state_68 number_of_loops);
           Bench.Test.create ~name:"Hand written" (fun () ->
               LoopHandWritten.test_state number_of_loops);
           Bench.Test.create ~name:"Native" (fun () ->
               LoopNative.test_state number_of_loops);
         ]);
    Printf.printf "\n\n");
  if run_queens_one then (
    Printf.printf "QUEENS ONE CPS BENCHMARK (%d queens):\n" number_of_queens;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               QueensNoOptImpure._queens_one_cps_96 number_of_queens);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               QueensOptImpure._queens_one_cps_96 number_of_queens);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               QueensNoOptPure._queens_one_cps_96 number_of_queens);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               QueensOptPure._queens_one_cps_96 number_of_queens);
           Bench.Test.create ~name:"Hand written" (fun () ->
               QueensHandWritten.queens_one_cps number_of_queens);
           Bench.Test.create ~name:"Native - CPS" (fun () ->
               QueensNative.queens_one_cps number_of_queens);
           Bench.Test.create ~name:"Native - exceptions" (fun () ->
               QueensNative.queens_one_exceptions number_of_queens);
         ]);
    Printf.printf "\n\n");
  if run_queens_one then (
    Printf.printf "QUEENS ONE OPTION BENCHMARK (%d queens):\n" number_of_queens;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               QueensNoOptImpure._queens_one_option_94 number_of_queens);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               QueensOptImpure._queens_one_option_94 number_of_queens);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               QueensNoOptPure._queens_one_option_94 number_of_queens);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               QueensOptPure._queens_one_option_94 number_of_queens);
           Bench.Test.create ~name:"Hand written" (fun () ->
               QueensHandWritten.queens_one_option number_of_queens);
           Bench.Test.create ~name:"Native - option" (fun () ->
               QueensNative.queens_one_option number_of_queens);
           Bench.Test.create ~name:"Native - exceptions" (fun () ->
               QueensNative.queens_one_exceptions number_of_queens);
         ]);
    Printf.printf "\n\n");
  if run_queens_all then (
    Printf.printf "QUEENS ALL BENCHMARK (%d queens):\n" number_of_queens;
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               QueensNoOptImpure._queens_all_100 number_of_queens);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               QueensOptImpure._queens_all_100 number_of_queens);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               QueensNoOptPure._queens_all_100 number_of_queens);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               QueensOptPure._queens_all_100 number_of_queens);
           Bench.Test.create ~name:"Hand written" (fun () ->
               QueensHandWritten.queens_all number_of_queens);
           Bench.Test.create ~name:"Native" (fun () ->
               QueensNative.queens_all number_of_queens);
         ]);
    Printf.printf "\n\n");
  if run_interp then (
    Printf.printf "INTERPRETER BENCHMARK:\n";
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               InterpNoOptImpure._bigTest_38 ());
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               InterpOptImpure._bigTest_38 ());
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               InterpNoOptPure._bigTest_38 ());
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               InterpOptPure._bigTest_38 ());
           Bench.Test.create ~name:"Native" (fun () -> InterpNative.bigTest ());
         ]);
    Printf.printf "\n\n");
  if run_range then (
    Printf.printf "RANGE BENCHMARKS:\n";
    Command.run
      (Bench.make_command
         [
           Bench.Test.create ~name:"Generated, impure, not optimized" (fun () ->
               RangeNoPureNoOpt._test_222 number_of_range);
           Bench.Test.create ~name:"Generated, impure, optimized" (fun () ->
               RangeOptNoPure._test_222 number_of_range);
           Bench.Test.create ~name:"Generated, pure, not optimized" (fun () ->
               RangePureNoOpt._test_222 number_of_range);
           Bench.Test.create ~name:"Generated, pure, optimized" (fun () ->
               RangeOptPure._test_222 number_of_range);
           (* Bench.Test.create ~name:"Native" (fun () -> FlatNative.bigTest ()); *)
         ]);
    Printf.printf "\n\n")
