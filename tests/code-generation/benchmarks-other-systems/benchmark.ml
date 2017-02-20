open Core.Std
open Core_bench.Std

let number_of_queens = 8

and run_queens_one = true
and run_queens_all = true

let () =
  if run_queens_one then begin
  Printf.printf "QUEENS ONE OPTION BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_one_option number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_one_option number_of_queens);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_one_option number_of_queens);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_one_option_94 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_one_option_94 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_one_option_94 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_one_option_94 number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_one then begin
  Printf.printf "QUEENS ONE CPS BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_one_cps number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_one_cps number_of_queens);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_one_cps number_of_queens);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_one_cps_96 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_one_cps_96 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_one_cps_96 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_one_cps_96 number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" number_of_queens;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_all number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_all number_of_queens);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_all number_of_queens);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 number_of_queens);
    ]);
  Printf.printf "\n\n"
  end;
