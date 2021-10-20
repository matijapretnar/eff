module Primitives = Language.Primitives

let primitive_source = function
  | Primitives.CompareEq -> "( = )"
  | Primitives.CompareGe -> "( >= )"
  | Primitives.CompareGt -> "( > )"
  | Primitives.CompareLe -> "( <= )"
  | Primitives.CompareLt -> "( < )"
  | Primitives.CompareNe -> "( <> )"
  | Primitives.FloatAcos -> "acos"
  | Primitives.FloatAdd -> "( +. )"
  | Primitives.FloatAsin -> "asin"
  | Primitives.FloatAtan -> "atan"
  | Primitives.FloatCos -> "cos"
  | Primitives.FloatDiv -> "( /. )"
  | Primitives.FloatExp -> "exp"
  | Primitives.FloatExpm1 -> "expm1"
  | Primitives.FloatInfinity -> "infinity"
  | Primitives.FloatLog -> "log"
  | Primitives.FloatLog1p -> "log1p"
  | Primitives.FloatMul -> "( *. )"
  | Primitives.FloatNaN -> "nan"
  | Primitives.FloatNeg -> "( ~-. )"
  | Primitives.FloatNegInfinity -> "neg_infinity"
  | Primitives.FloatOfInt -> "float_of_int"
  | Primitives.FloatSin -> "sin"
  | Primitives.FloatSqrt -> "sqrt"
  | Primitives.FloatSub -> "( -. )"
  | Primitives.FloatTan -> "tan"
  | Primitives.IntegerAdd -> "( + )"
  | Primitives.IntegerDiv -> "( / )"
  | Primitives.IntegerMod -> "( mod )"
  | Primitives.IntegerMul -> "( * )"
  | Primitives.IntegerNeg -> "( ~- )"
  | Primitives.IntegerAbs -> "abs"
  | Primitives.IntegerPow -> "( ** )"
  | Primitives.IntegerSub -> "( - )"
  | Primitives.IntOfFloat -> "int_of_float"
  | Primitives.StringConcat -> "( ^ )"
  | Primitives.StringLength -> "String.length"
  | Primitives.StringOfFloat -> "string_of_float"
  | Primitives.StringOfInt -> "string_of_int"
  | Primitives.StringSub -> "String.sub"
  | Primitives.ToString -> "fun _ -> \"<abstr>\""

let top_level_handler_source = function
  | Primitives.Print -> ("s", "k", "print_string s; continue k ()")
  | Primitives.RandomInt -> ("i", "k", "continue k (Random.int i)")
  | Primitives.RandomFloat -> ("f", "k", "continue k (Random.float f)")
  | Primitives.Read -> ("()", "k", "continue k (read_line ())")
  | Primitives.Raise -> ("_", "_", "failwith \"Not supported\"")
  | Primitives.Write -> ("_", "_", "failwith \"Not supported\"")
