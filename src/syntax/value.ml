type value =
  | Const of Const.t
  | Tuple of value list
  | Record of (CoreTypes.field, value) Assoc.t
  | Variant of CoreTypes.label * value option
  | Closure of closure
  | Handler of (result -> result)

and result = Value of value | Call of CoreTypes.effect * value * closure

and closure = (value -> result)

let unit_value = Tuple []

let unit_result = Value unit_value

let to_bool = function
  | Const Const.Boolean b -> b
  | _ -> Error.runtime "A boolean value expected."


let to_int = function
  | Const Const.Integer n -> n
  | _ -> Error.runtime "An integer value expected."


let to_float = function
  | Const Const.Float f -> f
  | _ -> Error.runtime "A floating-point value expected."


let to_str = function
  | Const Const.String s -> s
  | _ -> Error.runtime "A string value expected."


let to_handler = function
  | Handler h -> h
  | _ -> Error.runtime "A handler expected."


let print_effect eff ppf = Format.fprintf ppf "%s" eff

let rec print_value ?max_level v ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match v with
  | Const c -> Const.print c ppf
  | Tuple lst -> Print.tuple print_value lst ppf
  | Record lst -> Print.record print_value lst ppf
  | Variant (lbl, None) when lbl = CoreTypes.nil -> print "[]"
  | Variant (lbl, None) -> print "%s" lbl
  | Variant (lbl, Some Tuple [v1; v2]) when lbl = CoreTypes.cons ->
      print "[@[<hov>@[%t@]%t@]]" (print_value v1) (list v2)
  | Variant (lbl, Some v) ->
      print ~at_level:1 "%s @[<hov>%t@]" lbl (print_value v)
  | Closure _ -> print "<fun>"
  | Handler _ -> print "<handler>"


and list ?(max_length= 299) v ppf =
  if max_length > 1 then
    match v with
    | Variant (lbl, Some Tuple [v1; v2]) when lbl = CoreTypes.cons ->
        Format.fprintf ppf ";@ %t%t" (print_value v1)
          (list ~max_length:(max_length - 1) v2)
    | Variant (lbl, None) when lbl = CoreTypes.nil -> ()
    | _ -> assert false
  else Format.fprintf ppf ";@ ..."


let print_result r ppf =
  match r with
  | Value v -> print_value v ppf
  | Call (eff, v, _) -> Format.fprintf ppf "Call %s %t" eff (print_value v)
