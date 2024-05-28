(* Compilation to multicore ocaml *)
open Utils
module Term = Language.Term
module Type = Language.Type

module Backend : Language.Backend.S = struct
  (* ------------------------------------------------------------------------ *)
  (* Setup *)

  type label = Pattern of Term.pattern | Variable of Term.variable

  let print_label label =
    match label with
    | Pattern p -> Term.print_pattern p
    | Variable var -> Term.Variable.print var

  type program_element = {
    label : label;
    free_params : Type.FreeParams.params;
    constraints : Language.Constraints.t;
  }

  type state = { prog : program_element list list }

  let initial_state = { prog = [] }

  (* ------------------------------------------------------------------------ *)
  (* Processing functions *)
  let process_computation state _ = state

  let process_type_of state _ =
    (* Print.warning "[#typeof] commands are ignored when compiling to OCaml."; *)
    state

  let process_def_effect state _ = state

  let process_top_let state defs =
    let elements =
      List.fold_right
        (fun (pattern, _, cstr, comp) elements ->
          {
            free_params = Type.calculate_polarity_dirty_ty comp.ty;
            constraints = cstr;
            label = Pattern pattern;
          }
          :: elements)
        defs []
    in
    { prog = elements :: state.prog }

  let process_top_let_rec state defs =
    let elements =
      List.fold_right
        (fun (var, (_, cstr, abs)) elements ->
          {
            free_params = Type.calculate_polarity_abs_ty abs.ty;
            constraints = cstr;
            label = Variable var;
          }
          :: elements)
        (Assoc.to_list defs) []
    in
    { prog = elements :: state.prog }

  let load_primitive_value state _ _ = state
  let load_primitive_effect state _ _ = state
  let process_tydef state _tydefs = state

  let finalize state =
    Format.fprintf !Config.output_formatter
      "// Constraints graph\ndigraph {\n\tlabelloc=b\n\trankdir=BT\n";

    let uid = ref 0 in
    let print_element { label; free_params; constraints } =
      Format.fprintf !Config.output_formatter
        "  subgraph cluster_%i { // %t\n    label=\"Value: %t\"%t \n}\n" !uid
        (print_label label) (print_label label)
        (Language.Constraints.print_dot ~param_polarity:free_params
           ~header:(fun () -> "")
           ~footer:(fun () -> "")
           constraints);
      uid := !uid + 1
    in

    List.rev state.prog
    |> List.iter (fun elements ->
           match elements with
           | [] -> assert false
           | [ element ] -> print_element element
           | _ -> assert false);

    Format.fprintf !Config.output_formatter "}\n"
end

(*
   make && ./eff.exe --output-dot   --no-stdlib -g a.eff > a.dot  -V 4 2>a.out
*)
