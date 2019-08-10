open Core
open Core_bench.Std

let number_of_loops = 10000
and number_of_queens = 8
and number_of_range = 100

let run_loop_pure = true
and run_loop_latent = true
and run_loop_incr = true
and run_loop_incr' = true
and run_loop_state = true
and run_queens_one = true
and run_queens_all = false
and run_interp = false
and run_range = false

let () =
  if run_loop_pure then begin
  Printf.printf "loop_pure (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> LoopHandWritten.test_pure number_of_loops);
      Bench.Test.create ~name:"native" (fun () -> LoopNative.test_pure number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_latent then begin
  Printf.printf "loop_latent (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> LoopHandWritten.test_latent number_of_loops);
      Bench.Test.create ~name:"native" (fun () -> LoopNative.test_latent number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_incr then begin
  Printf.printf "loop_incr (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> LoopHandWritten.test_incr number_of_loops);
      Bench.Test.create ~name:"native" (fun () -> LoopNative.test_incr number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_incr' then begin
  Printf.printf "loop_incr2 (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> LoopHandWritten.test_incr' number_of_loops);
      Bench.Test.create ~name:"native" (fun () -> LoopNative.test_incr' number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_loop_state then begin
  Printf.printf "loop_state (%d loops):\n" number_of_loops;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> LoopHandWritten.test_state number_of_loops);
      Bench.Test.create ~name:"native" (fun () -> LoopNative.test_state number_of_loops);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_one then begin
  Printf.printf "queens_one (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> QueensHandWritten.queens_one_cps number_of_queens);
      Bench.Test.create ~name:"native" (fun () -> QueensNative.queens_one_cps number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "queens_all (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"handwritten" (fun () -> QueensHandWritten.queens_all number_of_queens);
      Bench.Test.create ~name:"native" (fun () -> QueensNative.queens_all number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_interp then begin
  Printf.printf "interp:\n";
  Command.run (Bench.make_command [
      Bench.Test.create ~name:"native" (fun () -> InterpNative.bigTest ());
    ]);
  Printf.printf "\n\n"
  end;
  if run_range then begin
  Printf.printf "range:\n";
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Native" (fun () -> FlatNative.bigTest ()); *)
    ]);
  Printf.printf "\n\n"
  end;
