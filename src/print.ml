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
  | Common.Nowhere ->
      Format.fprintf ppf "unknown position"
  | Common.Position (begin_pos, end_pos) ->
      let begin_char = begin_pos.Lexing.pos_cnum - begin_pos.Lexing.pos_bol + 1 in
      let begin_line = begin_pos.Lexing.pos_lnum in
      let filename = begin_pos.Lexing.pos_fname in

      if String.length filename != 0 then
        Format.fprintf ppf "file %S, line %d, char %d" filename begin_line begin_char
      else
        Format.fprintf ppf "line %d, char %d" begin_line begin_char

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
  | Pattern.Var x -> print "%s" x
  | Pattern.As (p, x) -> print "%t as %s" (pattern p) x
  | Pattern.Const c -> const c ppf
  | Pattern.Tuple lst -> print "(@[<hov>%t@])" (sequence "," pattern lst)
  | Pattern.Record lst -> print "(@[<hov>%t@])" (sequence ";" (field pattern) lst)
  | Pattern.Variant (lbl, None) when lbl = Common.nil -> print "[]"
  | Pattern.Variant (lbl, None) -> print "%s" lbl
  | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
      print "[@[<hov>@[%t@]%t@]]" (pattern v1) (pattern_list v2)
  | Pattern.Variant (lbl, Some p) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (pattern p)
  | Pattern.Nonbinding -> print "_"

and pattern_list ?(max_length=299) (p,_) ppf =
  if max_length > 1 then
    match p with
    | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
        fprintf ppf ",@ %t%t" (pattern v1) (pattern_list ~max_length:(max_length - 1) v2)
    | Pattern.Variant (lbl, None) when lbl = Common.nil -> ()
    | _ -> assert false
  else
    fprintf ppf ",@ ..."

let ty ?sbst poly t ppf =
  let sbst = (match sbst with Some sbst -> sbst | None -> Type.beautify t) in
  let rec ty ?max_level t ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
    let print_param s p =
      let k = (match Common.lookup p sbst with None -> ~-p | Some k -> k) in
      if 0 <= k && k <= 25
      then print "%s%c" s (char_of_int (k + int_of_char 'a'))
      else print "%sty%i" s (k - 25)
    in
    match t with
      | Type.Arrow (t1, t2) ->
          print ~at_level:5 "@[<h>%t ->@ %t@]" (ty ~max_level:4 t1) (ty t2)
      | Type.Basic b -> print "%s" b
      | Type.Apply (t, []) ->
          print "%s" t
      | Type.Apply (t, [s]) ->
          print ~at_level:1 "%t %s" (ty ~max_level:1 s) t
      | Type.Apply (t, ts) ->
          print ~at_level:1 "(%t) %s" (sequence ", " (ty ~max_level:0) ts) t

      | Type.Param p ->
        let c = (if List.mem p poly then "'" else "'_") in
          print_param c p

      | Type.Tuple [] -> print "unit"
      | Type.Tuple ts -> print ~at_level:2 "@[<hov>%t@]" (sequence " *" (ty ~max_level:1) ts)
      | Type.Record ts -> print "{@[<hov>%t@]}" (sequence "; " (field ty) ts)
      | Type.Sum [] -> print "empty"
      | Type.Sum (_::_) -> assert false
      | Type.Handler {Type.value=t1; Type.finally=t2} ->
          print ~at_level:4 "%t =>@ %t" (ty ~max_level:2 t1) (ty t2)
      | Type.Effect _ -> print "<effect>"
  in
    ty t ppf

(*
let subst sbst ppf =
  fprintf ppf "[@[<hov>%t@]]" (sequence ", " (fun (p,t) ppf -> fprintf ppf "%d/%t" p (ty ~sbst:[] t)) sbst)
*)

let rec computation ?max_level c ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst c with
  | Inter.Apply (e1, e2) -> print ~at_level:1 "%t %t" (expression e1) (expression ~max_level:0 e2)
  | Inter.Value e -> print ~at_level:1 "value %t" (expression ~max_level:0 e)
  | Inter.Match (e, lst) -> print "match %t with (@[<hov>%t@])" (expression e) (sequence " | " case lst)
  | Inter.While (c1, c2) -> print "while %t do %t done" (computation c1) (computation c2)
  | Inter.For (i, e1, e2, c, d) -> print "for %s = ... " i
  | Inter.New (eff, None) -> print "new %s" eff
  | Inter.New (eff, Some (e, lst)) -> print "new %s @ %t with ... end" eff (expression e)
  | Inter.Handle (e, c) -> print "handle %t with %t" (expression e) (computation c)
  | Inter.Let (lst, c) -> print "let %d @[<hov>%t@] in %t" (List.length lst) (sequence " | " let_abstraction lst) (computation c)
  | Inter.LetRec (lst, c) -> print "let rec ... in %t" (computation c)
  | Inter.Check c -> print "check %t" (computation c)


and expression ?max_level e ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst e with
  | Inter.Var x -> print "%s" x
  | Inter.Const c -> print "%t" (const c)
  | Inter.Tuple lst -> print "(@[<hov>%t@])" (sequence "," expression lst)
  | Inter.Record lst -> print "{@[<hov>%t@]}" (sequence ";" (field expression) lst)
  | Inter.Variant (lbl, None) -> print "%s" lbl
  | Inter.Variant (lbl, Some e) ->
    print ~at_level:1 "%s @[<hov>%t@]" lbl (expression e)
  | Inter.Lambda a -> print "fun %t" (abstraction a)
  | Inter.Handler _  -> print "<handler>"
  | Inter.Operation (e, op) -> print "%t#%s" (expression e) op

and abstraction (p, c) ppf =
  fprintf ppf "%t -> %t" (pattern p) (computation c)

and let_abstraction (p, c) ppf =
  fprintf ppf "%t = %t" (pattern p) (computation c)

and case a ppf =
  fprintf ppf "%t" (abstraction a)

let operation ((i, _, _), op) ppf =
  fprintf ppf "<instance #%d>.%s" i op

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
  | Value.Instance (i, _, _)  -> print "<instance #%d>" i
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
let message ?(pos=Common.Nowhere) msg_type v =
  if v <= !verbosity then
    begin
      Format.eprintf "@[%s (%t): " msg_type (position pos);
      Format.kfprintf (fun ppf -> fprintf ppf "@]@.") Format.err_formatter
    end
  else
    Format.ifprintf Format.err_formatter

let error (pos, err_type, msg) = message ~pos (err_type) 1 "%s" msg
let check ?pos = message ?pos "Check" 2
let warning ?pos = message ?pos "Warning" 3
let debug ?pos = message ?pos "Debug" 4
