(** Source code locations *)

type t = {
  filename : string;
  start_line : int;
  start_column : int;
  end_line : int;
  end_column : int;
}

let print { filename; start_line; start_column; _ } ppf =
  if String.length filename != 0 then
    Format.fprintf ppf "file %S, line %d, char %d" filename start_line
      start_column
  else Format.fprintf ppf "line %d, char %d" (start_line - 1) start_column

(** Dismantles a lexing position into its filename, line and column. *)
let dismantle lexing_position =
  let filename = lexing_position.Lexing.pos_fname
  and line = lexing_position.Lexing.pos_lnum
  and column =
    lexing_position.Lexing.pos_cnum - lexing_position.Lexing.pos_bol + 1
  in
  (filename, line, column)

let make start_lexing_position end_lexing_position =
  let start_filename, start_line, start_column = dismantle start_lexing_position
  and end_filename, end_line, end_column = dismantle end_lexing_position in
  assert (start_filename = end_filename);
  { filename = start_filename; start_line; start_column; end_line; end_column }

let union loc1 loc2 =
  if loc1.filename <> loc2.filename then
    invalid_arg "Location.union: locations do not belong to the same file"
  else
    let start_line, start_column =
      min
        (loc1.start_line, loc1.start_column)
        (loc2.start_line, loc2.start_column)
    and end_line, end_column =
      max (loc1.end_line, loc1.end_column) (loc2.end_line, loc2.end_column)
    in
    { loc1 with start_line; start_column; end_line; end_column }

let of_lexeme lex = make (Lexing.lexeme_start_p lex) (Lexing.lexeme_end_p lex)
