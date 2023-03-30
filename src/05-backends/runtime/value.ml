open Utils
open Language

type value =
  | Const of Const.t
  | Tuple of value list
  | Record of value Type.Field.Map.t
  | Variant of Type.Label.t * value option
  | Closure of closure
  | TypeCoercionClosure of (Type.ct_ty -> value)
  | DirtCoercionClosure of (Type.ct_dirt -> value)
  | Handler of (result -> result)

and result = Value of value | Call of Effect.t * value * closure
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

let print_effect eff ppf = Format.fprintf ppf "%t" (Effect.print eff)

let rec print_value ?max_level v ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match to_list v with
  | Some vs -> print "[@[%t@]]" (Print.sequence "; " print_value vs)
  | None -> (
      match v with
      | Const c -> Const.print c ppf
      | Tuple lst -> Print.tuple print_value lst ppf
      | Record assoc ->
          Print.record Type.Field.print print_value
            (Type.Field.Map.bindings assoc)
            ppf
      | Variant (lbl, None) -> print ~at_level:1 "%t" (Type.Label.print lbl)
      | Variant (lbl, Some v) ->
          print ~at_level:1 "%t @[<hov>%t@]" (Type.Label.print lbl)
            (print_value v)
      | Closure _ -> print "<fun>"
      | Handler _ -> print "<handler>"
      | TypeCoercionClosure _ -> print "<ty_coercion>"
      | DirtCoercionClosure _ -> print "<dir_coercion>")

and to_list = function
  | Variant (lbl, None) when lbl = Type.nil -> Some []
  | Variant (lbl, Some (Tuple [ hd; tl ])) when lbl = Type.cons ->
      Option.bind (to_list tl) (fun vs -> Some (hd :: vs))
  | _ -> None

let print_result r ppf =
  match r with
  | Value v -> print_value v ppf
  | Call (eff, v, _) ->
      Format.fprintf ppf "Call %t %t" (print_effect eff) (print_value v)
