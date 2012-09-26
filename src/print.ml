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
  | Pattern.Var x -> print "%d" x
  | Pattern.As (p, x) -> print "%t as %d" (pattern p) x
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

and pattern_list ?(max_length=299) (p,_) ppf =
  if max_length > 1 then
    match p with
    | Pattern.Variant (lbl, Some (Pattern.Tuple [v1; v2], _)) when lbl = Common.cons ->
        fprintf ppf ",@ %t%t" (pattern v1) (pattern_list ~max_length:(max_length - 1) v2)
    | Pattern.Variant (lbl, None) when lbl = Common.nil -> ()
    | _ -> assert false
  else
    fprintf ppf ",@ ..."

let instance i ppf =
  match i with
  | Constr.InstanceParam (Type.Instance_Param i) -> print ppf "#%d" i
  | Constr.InstanceTop -> print ppf "?"

let region_param (_, _, rs) ((Type.Region_Param k) as p) ppf =
  let c = (if List.mem p rs then "'" else "'_") in
    print ppf "<%srgn%i>" c k

let dirt_param (_, ds, _) ((Type.Dirt_Param k) as p) ppf =
  let c = (if List.mem p ds then "'" else "'_") in
    print ppf "<%sdrt%i>" c k

let region poly reg ppf =
  match reg with
    | Constr.RegionParam p -> print ppf "<%t>" (region_param poly p)
    | Constr.RegionAtom i -> print ppf "<%t>" (instance i)

let dirt ((_, ds, _) as poly) drt ppf =
  match drt with
    | Constr.DirtEmpty -> print ppf ""
    | Constr.DirtParam p -> print ppf "%t" (dirt_param poly p)
    | Constr.DirtAtom (rgn, op) -> print ppf "%t#%s" (region_param poly rgn) op

let fresh_instances frsh ppf =
  match frsh with
    | [] -> print ppf ""
    | frsh ->  print ppf "new %t." (sequence "" (fun (Type.Instance_Param i) ppf -> print ppf "%d" i) frsh)

let ty_param ps p ppf =
  let (Type.Ty_Param k) = p in
  let c = (if List.mem p ps then "'" else "'_") in
    if 0 <= k && k <= 25
    then print ppf "%s%c" c (char_of_int (k + int_of_char 'a'))
    else print ppf "%sty%i" c (k - 25)

let rec ty ((ps, _, _) as poly) t ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
    match t with
    (* XXX Should we print which instances are fresh? *)
    | Type.Arrow (t1, (frsh, t2, drt)) ->
        print ~at_level:5 "@[<h>%t ->@ %t %t[%t]@]"
        (ty ~max_level:4 t1)
        (fresh_instances frsh)
        (ty ~max_level:4 t2)
        (dirt_param poly drt)
        (* print ~at_level:5 "@[<h>%t ->@ %t@]" (ty ~max_level:4 t1) (ty t2) *)
    | Type.Basic b -> print "%s" b
    | Type.Apply (t, (lst, _, _)) ->
      begin match lst with
        | [] -> print "%s" t
        | [s] -> print ~at_level:1 "%t %s" (ty ~max_level:1 s) t
        | ts -> print ~at_level:1 "(%t) %s" (sequence "," ty ts) t
      end
    | Type.Effect (t, (lst, _, _), rgn) ->
      begin match lst with
        | [] -> print "%s%t" t (region_param poly rgn)
        | [s] -> print ~at_level:1 "%t %s%t" (ty ~max_level:1 s) t (region_param poly rgn)
        | ts -> print ~at_level:1 "(%t) %s%t" (sequence "," ty ts) t (region_param poly rgn)
      end
    | Type.TyParam p -> ty_param ps p ppf
    | Type.Tuple [] -> print "unit"
    | Type.Tuple ts -> print ~at_level:2 "@[<hov>%t@]" (sequence " *" (ty ~max_level:1) ts)
    | Type.Handler (t1, t2) ->
        print ~at_level:4 "%t =>@ %t" (ty ~max_level:2 t1) (ty t2)
  in ty t ppf

let constraints poly cstrs ppf =
  let constr cstr ppf = match cstr with
  | Constr.TypeConstraint (ty1, ty2, pos) -> print ppf "%t <= %t" (ty poly ty1) (ty poly ty2)
  | Constr.DirtConstraint (drt1, drt2, pos) -> print ppf "%t <= %t" (dirt poly drt1) (dirt poly drt2)
  | Constr.RegionConstraint (rgn1, rgn2, pos) -> print ppf "%t <= %t" (region poly rgn1) (region poly rgn2)
  in
  sequence ", " constr cstrs ppf

let ty_scheme (ctx, t, cstrs) ppf =
  let poly = Trio.empty in
  print ppf "%t {%t}" (ty poly t) (constraints poly cstrs)

let dirty_scheme ((poly, _, _) as tysch) drt ppf =
  print ppf "%t[%t]" (ty_scheme tysch) (dirt_param poly drt)

let beautified_ty_scheme tysch = ty_scheme tysch
  (* let tysch = Type.beautify tysch in *)
  (* ty_scheme tysch *)

let beautified_dirty_scheme tysch drt =
  (* let tysch, drt = Type.beautify_dirty tysch drt in *)
  dirty_scheme tysch drt

(*
let subst sbst ppf =
  fprintf ppf "[@[<hov>%t@]]" (sequence ", " (fun (p,t) ppf -> fprintf ppf "%d/%t" p (ty ~sbst:[] t)) sbst)
*)

let rec computation ?max_level c ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst c with
  | Core.Apply (e1, e2) -> print ~at_level:1 "%t %t" (expression e1) (expression ~max_level:0 e2)
  | Core.Value e -> print ~at_level:1 "value %t" (expression ~max_level:0 e)
  | Core.Match (e, lst) -> print "match %t with (@[<hov>%t@])" (expression e) (sequence " | " case lst)
  | Core.While (c1, c2) -> print "while %t do %t done" (computation c1) (computation c2)
  | Core.For (i, e1, e2, c, d) -> print "for %d = ... " i
  | Core.New (eff, None) -> print "new %s" eff
  | Core.New (eff, Some (e, lst)) -> print "new %s @ %t with ... end" eff (expression e)
  | Core.Handle (e, c) -> print "handle %t with %t" (expression e) (computation c)
  | Core.Let (lst, c) -> print "let %d @[<hov>%t@] in %t" (List.length lst) (sequence " | " let_abstraction lst) (computation c)
  | Core.LetRec (lst, c) -> print "let rec ... in %t" (computation c)
  | Core.Check c -> print "check %t" (computation c)


and expression ?max_level e ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst e with
  | Core.Var x -> print "%d" x
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
let debug ?pos = message ?pos "Debug" 4
