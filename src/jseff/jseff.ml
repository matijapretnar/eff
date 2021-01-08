open Shared
open Utils
open Js_of_ocaml

let js_formatter _format echo =
  let buffer = ref "" in
  let out s p n = buffer := !buffer ^ String.sub s p n in
  let flush () =
    (Js.Unsafe.fun_call echo [| Js.Unsafe.inject (Js.string !buffer) |] : unit);
    buffer := ""
  in
  Format.make_formatter out flush

module Shell = Shell.Make (Runtime.Backend)

(* Export the interface to Javascript. *)
let _ =
  Js.export "jseff"
    (object%js
       method initialize echo =
         Config.output_formatter := js_formatter "[;#00a8ff;#192a56]" echo;
         Config.error_formatter := js_formatter "[b;#e84118;#192a56]" echo;
         let state = Shell.initialize () in
         let state = Shell.load_source Stdlib_eff.stdlib state in
         Format.fprintf !Config.output_formatter "eff %s@." Config.version;
         Format.fprintf !Config.output_formatter "[Type #help for help.]@.";
         state

       method executeSource state source =
         try Shell.execute_source (Js.to_string source) state
         with Error.Error err ->
           Error.print err;
           state

       method loadSource state source =
         try Shell.load_source (Js.to_string source) state
         with Error.Error err ->
           Error.print err;
           state
    end)
