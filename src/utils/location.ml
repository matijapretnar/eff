(** Source code locations *)

type t =
  | Unknown
  | Known of known

and known = {
  filename: string;
  start_line: int;
  start_col: int;
  end_line: int;
  end_col: int;
}

let print loc ppf =
  match loc with
  | Unknown -> Format.fprintf ppf "unknown location"
  | Known {filename; start_line; start_col; end_line; end_col} ->
    if String.length filename != 0 then
      Format.fprintf ppf "file %S, line %d, char %d" filename start_line start_col
    else
      Format.fprintf ppf "line %d, char %d" (start_line - 1) start_col

let unknown = Unknown

(** Dismantles a lexing position into its filename, line and column. *)
let dismantle lexpos =
  let filename = lexpos.Lexing.pos_fname
  and line = lexpos.Lexing.pos_lnum
  and col = lexpos.Lexing.pos_cnum - lexpos.Lexing.pos_bol + 1 in
  filename, line, col

let make start_lexpos end_lexpos =
  let start_filename, start_line, start_col = dismantle start_lexpos
  and end_filename, end_line, end_col = dismantle end_lexpos in
  assert (start_filename = end_filename);
  Known {filename = start_filename; start_line; start_col; end_line; end_col}

let join loc1 loc2 =
  match loc1, loc2 with
  | Known loc1, Known loc2 ->
      Known {loc1 with end_line = loc2.end_line; end_col = loc2.end_col}
  | _, _ -> Unknown

let of_lexeme lex =
  make (Lexing.lexeme_start_p lex) (Lexing.lexeme_end_p lex)
