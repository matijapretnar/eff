let fprintf = Format.fprintf

let print ?(max_level=9999) ?(at_level=0) ppf =
  if max_level < at_level then
    begin
      Format.fprintf ppf "(@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@])") ppf
    end
  else
    begin
      Format.fprintf ppf "@[";
      Format.kfprintf (fun ppf -> Format.fprintf ppf "@]") ppf
    end

let position pos ppf =
  match pos with
  | Common.Position (begin_pos, end_pos) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol + 1 in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in

      if String.length filename != 0 then
        Format.fprintf ppf "file %S, line %d, char %d" filename begin_line begin_char
      else
        Format.fprintf ppf "line %d, char %d" (begin_line - 1) begin_char

let rec sequence sep pp vs ppf =
  match vs with
  | [] -> ()
  | [v] -> pp v ppf
  | v :: vs -> Format.fprintf ppf "%t%s@ %t" (pp v) sep (sequence sep pp vs)

and field pp (f, v) ppf = fprintf ppf "%s = %t" f (pp v)

let const c ppf =
  match c with
  | Common.Integer k -> fprintf ppf "%s" (Big_int.string_of_big_int k)
  | Common.String s -> fprintf ppf "%S" s
  | Common.Boolean b -> fprintf ppf "%B" b
  | Common.Float f -> fprintf ppf "%F" f

let rec pattern ?max_level (p,_) ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match p with
  | Pattern.Var x -> print "%t" (Newprint.variable x)
  | Pattern.As (p, x) -> print "%t as %t" (pattern p) (Newprint.variable x)
  | Pattern.Const c -> const c ppf
  | Pattern.Tuple lst -> print "(@[<hov>%t@])" (sequence "," pattern lst)
  | Pattern.Record lst -> print "{@[<hov>%t@]}" (sequence ";" (field pattern) lst)
  | Pattern.Variant (lbl, None) when lbl = Common.nil -> print "[]"
  | Pattern.Variant (lbl, None) -> print "%s" lbl
  | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
      print "[@[<hov>@[%t@]%t@]]" (pattern v1) (pattern_list v2)
  | Pattern.Variant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (pattern p)
  | Pattern.Nonbinding -> print "_"

and pattern_list ?(max_length=299) (p, pos) ppf =
  if max_length > 1 then
    match p with
    | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
        fprintf ppf ",@ %t%t" (pattern v1) (pattern_list ~max_length:(max_length - 1) v2)
    | Pattern.Variant (lbl, None) when lbl = Common.nil -> ()
    | p -> fprintf ppf "(??? %t ???)" (pattern (p, pos))
  else
    fprintf ppf ",@ ..."

let rec computation ?max_level c ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst c with
  | Core.Apply (e1, e2) -> print ~at_level:1 "%t %t" (expression e1) (expression ~max_level:0 e2)
  | Core.Value e -> print ~at_level:1 "value %t" (expression ~max_level:0 e)
  | Core.Match (e, lst) -> print "match %t with (@[<hov>%t@])" (expression e) (sequence " | " case lst)
  | Core.While (c1, c2) -> print "while %t do %t done" (computation c1) (computation c2)
  | Core.For (i, e1, e2, c, d) -> print "for %t = ... " (Newprint.variable i)
  | Core.New (eff, None) -> print "new %s" eff
  | Core.New (eff, Some (e, lst)) -> print "new %s @ %t with ... end" eff (expression e)
  | Core.Handle (e, c) -> print "handle %t with %t" (expression e) (computation c)
  | Core.Let (lst, c) -> print "let @[<hov>%t@] in %t" (sequence " | " let_abstraction lst) (computation c)
  | Core.LetRec (lst, c) -> print "let rec ... in %t" (computation c)
  | Core.Check c -> print "check %t" (computation c)


and expression ?max_level e ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst e with
  | Core.Var x -> print "%t" (Newprint.variable x)
  | Core.Const c -> print "%t" (const c)
  | Core.Tuple lst -> print "(@[<hov>%t@])" (sequence "," expression lst)
  | Core.Record lst -> print "{@[<hov>%t@]}" (sequence ";" (field expression) lst)
  | Core.Variant (lbl, None) -> print "%s" lbl
  | Core.Variant (lbl, Some e) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (expression e)
  | Core.Lambda a -> print "fun %t" (abstraction a)
  | Core.Handler _  -> print "<handler>"
  | Core.Operation (e, op) -> print "%t#%s" (expression e) op

and abstraction (p, c) ppf =
  fprintf ppf "%t -> %t" (pattern p) (computation c)

and let_abstraction (p, c) ppf =
  fprintf ppf "%t = %t" (pattern p) (computation c)

and case a ppf =
  fprintf ppf "%t" (abstraction a)

let instance inst ppf =
  match inst with
  | (_, Some desc, _) -> fprintf ppf "<%s>" desc
  | (i, None, _) -> fprintf ppf "<instance #%d>" i

let operation (inst, op) ppf = fprintf ppf "%t.%s" (instance inst) op

let rec value ?max_level v ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match v with
  | Value.Const c -> const c ppf
  | Value.Tuple lst -> print "(@[<hov>%t@])" (sequence "," value lst)
  | Value.Record lst -> print "{@[<hov>%t@]}" (sequence ";" (field value) lst)
  | Value.Variant (lbl, None) when lbl = Common.nil -> print "[]"
  | Value.Variant (lbl, None) -> print "%s" lbl
  | Value.Variant (lbl, Some (Value.Tuple [v1; v2])) when lbl = Common.cons ->
      print "[@[<hov>@[%t@]%t@]]" (value v1) (list v2)
  | Value.Variant (lbl, Some v) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (value v)
  | Value.Closure _ -> print "<fun>"
  | Value.Instance inst  -> instance inst ppf
  | Value.Handler _  -> print "<handler>"

and list ?(max_length=299) v ppf =
  if max_length > 1 then
    match v with
    | Value.Variant (lbl, Some (Value.Tuple [v1; v2])) when lbl = Common.cons ->
        fprintf ppf ";@ %t%t" (value v1) (list ~max_length:(max_length - 1) v2)
    | Value.Variant (lbl, None) when lbl = Common.nil -> ()
    | _ -> assert false
  else
    fprintf ppf ";@ ..."

let result r ppf =
  match r with
  | Value.Value v -> value v ppf
  | Value.Operation (op, v, _) ->
      fprintf ppf "Operation %t %t" (operation op) (value v)

let to_string m =
  (Format.kfprintf (fun _ -> Format.flush_str_formatter ()) Format.str_formatter) m


let verbosity = ref 3
let message ?pos msg_type v =
  if v <= !verbosity then
    begin
      begin match pos with
      | None -> Format.eprintf "@[%s: " msg_type
      | Some pos -> Format.eprintf "@[%s (%t): " msg_type (position pos)
      end;
      Format.kfprintf (fun ppf -> fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (pos, err_type, msg) = message ?pos err_type 1 "%s" msg
let check ~pos = message ~pos "Check" 2
let warning ~pos = message ~pos "Warning" 3
let info ?pos = message ?pos "Info" 4
let debug ?pos = message ?pos "Debug" 5
