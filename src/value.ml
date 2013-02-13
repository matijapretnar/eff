type value =
  | Const of Common.const
  | Tuple of value list
  | Record of (Common.field, value) Common.assoc
  | Variant of Common.label * value option
  | Closure of closure
  | Instance of instance
  | Handler of (result -> result)

and result =
  | Value of value
  | Operation of operation * value * closure

and closure = value -> result

and operation = instance * Common.opsym

and instance = int * string option * resource option

and resource = value ref * (Common.opsym, value -> value -> result) Common.assoc

let unit_value = Tuple []
let unit_result = Value unit_value

let fresh_instance =
  let fresh = Common.fresh Common.id in
  fun description resource -> Instance (fresh (), description, resource)

let to_bool = function
  | Const (Common.Boolean b) -> b
  | _ -> Error.runtime "A boolean value expected."

let to_int = function
  | Const (Common.Integer n) -> n
  | _ -> Error.runtime "An integer value expected."

let to_float = function
  | Const (Common.Float f) -> f
  | _ -> Error.runtime "A floating-point value expected."

let to_str = function
  | Const (Common.String s) -> s
  | _ -> Error.runtime "A string value expected."

let to_instance = function
  | Instance i -> i
  | _ -> Error.runtime "An effect instance expected."

let to_handler = function
  | Handler h -> h
  | _ -> Error.runtime "A handler expected."

let print_instance inst ppf =
  match inst with
  | (_, Some desc, _) -> Format.fprintf ppf "<%s>" desc
  | (i, None, _) -> Format.fprintf ppf "<instance #%d>" i

let print_operation (inst, op) ppf = Format.fprintf ppf "%t.%s" (print_instance inst) op

let rec print_value ?max_level v ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match v with
  | Const c -> Common.print_const c ppf
  | Tuple lst -> print "(@[<hov>%t@])" (Print.sequence "," print_value lst)
  | Record lst -> print "{@[<hov>%t@]}" (Print.sequence ";" (Print.field print_value) lst)
  | Variant (lbl, None) when lbl = Common.nil -> print "[]"
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some (Tuple [v1; v2])) when lbl = Common.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_value v1) (list v2)
  | Variant (lbl, Some v) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_value v)
  | Closure _ -> print "<fun>"
  | Instance inst  -> print_instance inst ppf
  | Handler _  -> print "<handler>"

and list ?(max_length=299) v ppf =
  if max_length > 1 then
    match v with
    | Variant (lbl, Some (Tuple [v1; v2])) when lbl = Common.cons ->
        Format.fprintf ppf ";@ %t%t" (print_value v1) (list ~max_length:(max_length - 1) v2)
    | Variant (lbl, None) when lbl = Common.nil -> ()
    | _ -> assert false
  else
    Format.fprintf ppf ";@ ..."

let print_result r ppf =
  match r with
  | Value v -> print_value v ppf
  | Operation (op, v, _) ->
      Format.fprintf ppf "Operation %t %t" (print_operation op) (print_value v)
