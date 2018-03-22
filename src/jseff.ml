(** Create a [Format.formatter] from a Javascript print callback. *)
let js_formatter echo =
let buffer = ref "" in
Format.make_formatter
(fun s p n -> buffer := !buffer ^ String.sub s p n )
(fun () ->
  (Js.Unsafe.fun_call echo [| Js.Unsafe.inject (Js.string !buffer) |] : unit) ;
  buffer := "")

(* Export the interface to Javascript. *)
let _ =
Js.export "jseff"
  (object%js

     method reset echo =
       let ppf = js_formatter echo in
       Shell.initial_state

     method toplevel echo env cmd =
       let ppf = js_formatter echo in
       Shell.use_textfile ppf (Js.to_string cmd) env

     method usefile echo env cmds =
       let ppf = js_formatter echo in
       Shell.use_textfile ppf (Js.to_string cmds) env
   end)
