open Utils
module Const = Language.Const
module CoreTypes = Language.CoreTypes

type value =
  | Const of Const.t
  | Tuple of value list
  | Record of (CoreTypes.Field.t, value) Assoc.t
  | Variant of CoreTypes.Label.t * value option
  | Closure of closure
  | TypeCoercionClosure of (Type.ct_ty -> value)
  | DirtCoercionClosure of (Type.ct_dirt -> value)
  | Handler of (result -> result)

and result = Value of value | Call of CoreTypes.Effect.t * value * closure

and closure = value -> result

let unit_value = Tuple []

let unit_result = Value unit_value

let to_bool = function
  | Const (Const.Boolean b) -> b
  | _ -> Error.runtime "A boolean value expected."

let to_int = function
  | Const (Const.Integer n) -> n
  | _ -> Error.runtime "An integer value expected."

let to_float = function
  | Const (Const.Float f) -> f
  | _ -> Error.runtime "A floating-point value expected."

let to_str = function
  | Const (Const.String s) -> s
  | _ -> Error.runtime "A string value expected."

let to_handler = function
  | Handler h -> h
  | _ -> Error.runtime "A handler expected."

let print_effect eff ppf = Format.fprintf ppf "%t" (CoreTypes.Effect.print eff)

let rec print_value ?max_level v ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match v with
  | Const c -> Const.print c ppf
  | Tuple lst -> Print.tuple print_value lst ppf
  | Record assoc -> Print.record CoreTypes.Field.print print_value assoc ppf
  | Variant (lbl, None) -> print ~at_level:1 "%t" (CoreTypes.Label.print lbl)
  | Variant (lbl, Some v) ->
      print ~at_level:1 "%t @[<hov>%t@]"
        (CoreTypes.Label.print lbl)
        (print_value v)
  | Closure _ -> print "<fun>"
  | Handler _ -> print "<handler>"
  | TypeCoercionClosure _ -> print "<ty_coercion>"
  | DirtCoercionClosure _ -> print "<dir_coercion>"

let print_result r ppf =
  match r with
  | Value v -> print_value v ppf
  | Call (eff, v, _) ->
      Format.fprintf ppf "Call %t %t" (print_effect eff) (print_value v)
