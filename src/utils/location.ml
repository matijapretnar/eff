(** Source code locations *)

type t =
  | Unknown
  | Known of known

and known = {
  filename: string;
  start_line: int;
  start_column: int;
  end_line: int;
  end_column: int;
}

let print loc ppf =
  match loc with
  | Unknown -> Format.fprintf ppf "unknown location"
  | Known {filename; start_line; start_column; end_line; end_column} ->
    if String.length filename != 0 then
      Format.fprintf ppf "file %S, line %d, char %d" filename start_line start_column
    else
      Format.fprintf ppf "line %d, char %d" (start_line - 1) start_column

let unknown = Unknown

(** Dismantles a lexing position into its filename, line and column. *)
let dismantle lexing_position =
  let filename = lexing_position.Lexing.pos_fname
  and line = lexing_position.Lexing.pos_lnum
  and column = lexing_position.Lexing.pos_cnum - lexing_position.Lexing.pos_bol + 1 in
  filename, line, column

let make start_lexing_position end_lexing_position =
  let start_filename, start_line, start_column = dismantle start_lexing_position
  and end_filename, end_line, end_column = dismantle end_lexing_position in
  assert (start_filename = end_filename);
  Known {filename = start_filename; start_line; start_column; end_line; end_column}

let merge loc1 loc2 =
  match loc1, loc2 with
  | Known loc1, Known loc2 ->
      Known {loc1 with end_line = loc2.end_line; end_column = loc2.end_column}
  | _, _ -> Unknown

let of_lexeme lex =
  make (Lexing.lexeme_start_p lex) (Lexing.lexeme_end_p lex)
