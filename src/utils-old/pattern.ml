type 'var t = 'var plain_t * Location.t
and 'var plain_t =
  | Var of 'var
  | As of 'var t * 'var
  | Tuple of ('var t) list
  | Record of (OldUtils.field * 'var t) list
  | Variant of OldUtils.label * ('var t) option
  | Const of Const.t
  | Nonbinding
(* Changing the datatype [plain_t] will break [specialize_vector] in [exhaust.ml] because
   of wildcard matches there. *)
