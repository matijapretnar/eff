open Core.Std
open Core_bench.Std

let number_of_loops = 10000
and number_of_queens = 8

let run_loop_pure = true
and run_loop_latent = true
and run_loop_incr = true
and run_loop_state = true
and run_queens_one = true
and run_queens_all = true
and run_interp = true
and run_parser_short = true

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
  Printf.printf "QUEENS ONE BENCHMARK (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_one_89 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_one_89 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_one_89 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_one_89 number_of_queens);
      Bench.Test.create ~name:"Hand written" (fun () -> QueensHandWritten.queens_one number_of_queens);
      Bench.Test.create ~name:"Native - CPS" (fun () -> QueensNative.queens_one_cps number_of_queens);
      Bench.Test.create ~name:"Native - option" (fun () -> QueensNative.queens_one_option number_of_queens);
      Bench.Test.create ~name:"Native - exceptions" (fun () -> QueensNative.queens_one_exceptions number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_93 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_93 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_93 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_93 number_of_queens);
      Bench.Test.create ~name:"Hand written" (fun () -> QueensHandWritten.queens_all number_of_queens);
      Bench.Test.create ~name:"Native" (fun () -> QueensNative.queens_all number_of_queens);
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
      Bench.Test.create ~name:"Native - option" (fun () -> ParserNative.parseTest ());
    ]);
  Printf.printf "\n\n"
  end;
