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

let variable (_, x) ppf = print ppf "%s" x

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
  | Pattern.Var x -> print "%t" (variable x)
  | Pattern.As (p, x) -> print "%t as %t" (pattern p) (variable x)
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

let instance i ppf =
  match i with
  | Type.InstanceParam (Type.Instance_Param i) -> print ppf "#%d" i
  | Type.InstanceTop -> print ppf "?"

let region_param ?(non_poly=Trio.empty) ((Type.Region_Param k) as p) ppf =
  let (_, _, rs) = non_poly in
  let c = (if List.mem p rs then "_" else "") in
    print ppf "%sr%i" c (k + 1)

let dirt_param ?(non_poly=Trio.empty) ((Type.Dirt_Param k) as p) ppf =
  let (_, ds, _) = non_poly in
  let c = (if List.mem p ds then "_" else "") in
    print ppf "%sd%i" c (k + 1)

let region ?non_poly reg ppf =
  match reg with
    | Type.RegionParam p -> print ppf "<%t>" (region_param ?non_poly p)
    | Type.RegionAtom i -> print ppf "<%t>" (instance i)

let dirt ?non_poly drt ppf =
  match drt with
    | Type.DirtEmpty -> print ppf ""
    | Type.DirtParam p -> print ppf "%t" (dirt_param ?non_poly p)
    | Type.DirtAtom (rgn, op) -> print ppf "%t#%s" (region_param ?non_poly rgn) op

let fresh_instances frsh ppf =
  match frsh with
    | [] -> print ppf ""
    | frsh ->  print ppf "new %t.@ " (sequence "" (fun (Type.Instance_Param i) ppf -> print ppf "%d" i) frsh)

let ty_param ?(non_poly=Trio.empty) p ppf =
  let (ps, _, _) = non_poly in
  let (Type.Ty_Param k) = p in
  let c = (if List.mem p ps then "'_" else "'") in
    if 0 <= k && k <= 6
    then print ppf "%s%c" c (char_of_int (k + int_of_char 't'))
    else print ppf "%st%i" c (k - 6)

let rec ty ?(non_poly=Trio.empty) t ppf =
  let rec ty ?max_level t ppf =
    let print ?at_level = print ?max_level ?at_level ppf in
    match t with
    (* XXX Should we print which instances are fresh? *)
    | Type.Arrow (t1, (frsh, t2, drt)) ->
        print ~at_level:5 "@[<h>%t -%t->@ %t%t@]"
        (ty ~max_level:4 t1)
        (dirt_param ~non_poly drt)
        (fresh_instances frsh)
        (ty ~max_level:5 t2)
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
        | [] -> print "%s[%t]" t (region_param ~non_poly rgn)
        | [s] -> print ~at_level:1 "%t %s[%t]" (ty ~max_level:1 s) t (region_param ~non_poly rgn)
        | ts -> print ~at_level:1 "(%t) %s[%t]" (sequence "," ty ts) t (region_param ~non_poly rgn)
      end
    | Type.TyParam p -> ty_param ~non_poly p ppf
    | Type.Tuple [] -> print "unit"
    | Type.Tuple ts -> print ~at_level:2 "@[<hov>%t@]" (sequence " *" (ty ~max_level:1) ts)
    | Type.Handler (t1, t2) ->
        print ~at_level:4 "%t =>@ %t" (ty ~max_level:2 t1) (ty t2)
  in ty t ppf

let constraints ?(non_poly=Trio.empty) g ppf =
  let tys = Type.fold_ty (fun p1 p2 pos lst -> (p1, p2) :: lst) g []
  and drts = Type.fold_dirt (fun d1 d2 pos lst -> (d1, d2) :: lst) g []
  and rgns =Type.fold_region (fun r1 r2 pos lst -> (r1, r2) :: lst) g []
  and sort lst = List.sort compare lst
  in
  print ppf "%t%s%t%s%t"
    (sequence "," (fun (p1, p2) ppf -> print ppf "%t <= %t" (ty_param ~non_poly p1) (ty_param ~non_poly p2)) (sort tys))
    (match drts with [] -> "" | _ -> "; ")
    (sequence "," (fun (drt1, drt2) ppf -> print ppf "%t <= %t" (dirt ~non_poly drt1) (dirt ~non_poly drt2)) (sort drts))
    (match rgns with [] -> "" | _ -> "; ")
    (sequence "," (fun (rgn1, rgn2) ppf -> print ppf "%t <= %t" (region ~non_poly rgn1) (region ~non_poly rgn2)) (sort rgns))

let context ctx ppf =
  match ctx with
  | [] -> ()
  | _ -> print ppf "(@[%t@]).@ " (sequence "," (fun (x, t) ppf -> print ppf "%t : %t" (variable x) (ty t)) ctx)

let ty_scheme (ctx, t, cstrs) ppf =
  let sbst = Type.beautifying_subst () in
  let ctx = Common.assoc_map (Type.subst_ty sbst) ctx in
  let t = Type.subst_ty sbst t in
  let cstrs = Type.subst_constraints sbst cstrs in
  print ppf "%t%t | %t" (context ctx) (ty t) (constraints cstrs)

let dirty_scheme (ctx, (frsh, t, drt), cstrs) ppf =
  let sbst = Type.beautifying_subst () in
  let ctx = Common.assoc_map (Type.subst_ty sbst) ctx in
  let t = Type.subst_ty sbst t in
  let drt = sbst.Type.dirt_param drt in
  let cstrs = Type.subst_constraints sbst cstrs in
  print ppf "%t%t%t ! %t | %t"
    (context ctx)
    (fresh_instances frsh)
    (ty t)
    (dirt_param drt)
    (constraints cstrs)

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
  | Core.For (i, e1, e2, c, d) -> print "for %t = ... " (variable i)
  | Core.New (eff, None) -> print "new %s" eff
  | Core.New (eff, Some (e, lst)) -> print "new %s @ %t with ... end" eff (expression e)
  | Core.Handle (e, c) -> print "handle %t with %t" (expression e) (computation c)
  | Core.Let (lst, c) -> print "let @[<hov>%t@] in %t" (sequence " | " let_abstraction lst) (computation c)
  | Core.LetRec (lst, c) -> print "let rec ... in %t" (computation c)
  | Core.Check c -> print "check %t" (computation c)


and expression ?max_level e ppf =
  let print ?at_level = print ?max_level ?at_level ppf in
  match fst e with
  | Core.Var x -> print "%t" (variable x)
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
