(** Create a [Format.formatter] from a Javascript print callback. *)
let js_formatter format echo =
let buffer = ref "" in
Format.make_formatter
(fun s p n -> buffer := !buffer ^ String.sub s p n)
(fun () ->
  (Js.Unsafe.fun_call echo [| Js.Unsafe.inject (Js.string ("[" ^ format ^ !buffer ^ "]")) |] : unit) ;
  buffer := "")

let output_formatter echo = js_formatter "[;#00a8ff;#192a56]" echo
let error_formatter echo = js_formatter "[b;#e84118;#192a56]" echo

(* Export the interface to Javascript. *)
let _ =
Js.export "jseff"
  (object%js

     method reset echo =
       Config.output_formatter := output_formatter echo;
       Config.error_formatter := error_formatter echo;
       Tctx.reset ();
       Shell.initial_state

     method toplevel echo env cmd =
       let ppf = output_formatter echo in
       try
         Shell.execute_source ppf (Js.to_string cmd) env
       with
         Error.Error err -> Error.print err; env

     method usefile echo env cmds =
       let ppf = output_formatter echo in
       try
         Shell.execute_source ppf (Js.to_string cmds) env
       with
         Error.Error err -> Error.print err; env
   end)
