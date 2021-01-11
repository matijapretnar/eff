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
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" 9;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_all number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_all 9);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_all 9);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 9);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" 10;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_all number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_all 10);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_all 10);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 10);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" 11;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_all number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_all 11);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_all 11);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 11);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" 12;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_all number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_all 12);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_all 12);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 12);
    ]);
  Printf.printf "\n\n"
  end;
  if run_queens_all then begin
  Printf.printf "QUEENS ALL BENCHMARK COMPARISON WITH OTHER SYSTEMS (%d queens):\n" 13;
  Command.run (Bench.make_command [
      (* Bench.Test.create ~name:"Multicore ocaml" (fun () -> Multicore.queens_all number_of_queens); *)
      Bench.Test.create ~name:"Eff directly in ocaml" (fun () -> EffInOcaml.queens_all 13);
      Bench.Test.create ~name:"Handlers in action" (fun () -> HandlersInAction.queens_all 13);
      (* Bench.Test.create ~name:"Generated, impure, not optimized" (fun () -> QueensNoOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, impure, optimized" (fun () -> QueensOptImpure._queens_all_100 number_of_queens);
      Bench.Test.create ~name:"Generated, pure, not optimized" (fun () -> QueensNoOptPure._queens_all_100 number_of_queens); *)
      Bench.Test.create ~name:"Generated, pure, optimized" (fun () -> QueensOptPure._queens_all_100 13);
    ]);
  Printf.printf "\n\n"
  end;
