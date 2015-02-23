type 'var t = 'var plain_t * Location.t
and 'var plain_t =
  | Var of 'var
  | As of 'var t * 'var
  | Tuple of ('var t) list
  | Record of (Common.field * 'var t) list
  | Variant of Common.label * ('var t) option
  | Const of Common.const
  | Nonbinding
val pattern_vars : 'var t -> 'var list
val linear_pattern : 'var t -> bool
val linear_record : ('a * 'b) list -> bool
