type t = plain_t Common.pos
and plain_t =
    Var of Common.variable
  | As of t * Common.variable
  | Tuple of t list
  | Record of (Common.field * t) list
  | Variant of Common.label * t option
  | Const of Common.const
  | Nonbinding
val pattern_vars : t -> Common.variable list
val linear_pattern : t -> bool
val linear_record : ('a * 'b) list -> bool
