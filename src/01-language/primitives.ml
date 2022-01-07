type primitive_value =
  | CompareEq
  | CompareGe
  | CompareGt
  | CompareLe
  | CompareLt
  | CompareNe
  | FloatAcos
  | FloatAdd
  | FloatAsin
  | FloatAtan
  | FloatCos
  | FloatDiv
  | FloatExp
  | FloatExpm1
  | FloatInfinity
  | FloatLog
  | FloatLog1p
  | FloatMul
  | FloatNaN
  | FloatNeg
  | FloatNegInfinity
  | FloatOfInt
  | FloatSin
  | FloatSqrt
  | FloatSub
  | FloatTan
  | IntegerAdd
  | IntegerDiv
  | IntegerMod
  | IntegerMul
  | IntegerNeg
  | IntegerAbs
  | IntegerPow
  | IntegerSub
  | IntOfFloat
  | StringConcat
  | StringLength
  | StringOfFloat
  | StringOfInt
  | StringSub
  | ToString

type primitive_effect = Print | Read | Raise | RandomInt | RandomFloat | Write

(* Keep these lists up to date with the type sabove, otherwise the missing primitives will not be loaded *)
let primitive_values =
  [
    CompareEq;
    CompareGe;
    CompareGt;
    CompareLe;
    CompareLt;
    CompareLt;
    CompareNe;
    FloatAcos;
    FloatAdd;
    FloatAsin;
    FloatAtan;
    FloatCos;
    FloatDiv;
    FloatExp;
    FloatExpm1;
    FloatInfinity;
    FloatLog;
    FloatLog1p;
    FloatMul;
    FloatNaN;
    FloatNeg;
    FloatNegInfinity;
    FloatOfInt;
    FloatSin;
    FloatSqrt;
    FloatSub;
    FloatTan;
    IntegerAdd;
    IntegerDiv;
    IntegerMod;
    IntegerMul;
    IntegerNeg;
    IntegerAbs;
    IntegerPow;
    IntegerSub;
    IntOfFloat;
    StringConcat;
    StringLength;
    StringOfFloat;
    StringOfInt;
    StringSub;
    ToString;
  ]

let primitive_effects = [ Print; Read; Raise; RandomInt; RandomFloat; Write ]

let primitive_value_name = function
  | CompareEq -> "="
  | CompareGe -> ">="
  | CompareGt -> ">"
  | CompareLe -> "<="
  | CompareLt -> "<"
  | CompareNe -> "<>"
  | FloatAcos -> "acos"
  | FloatAdd -> "+."
  | FloatAsin -> "asin"
  | FloatAtan -> "atan"
  | FloatCos -> "cos"
  | FloatDiv -> "/."
  | FloatExp -> "exp"
  | FloatExpm1 -> "expm1"
  | FloatInfinity -> "infinity"
  | FloatLog -> "log"
  | FloatLog1p -> "log1p"
  | FloatMul -> "*."
  | FloatNaN -> "nan"
  | FloatNeg -> "~-."
  | FloatNegInfinity -> "neg_infinity"
  | FloatOfInt -> "float_of_int"
  | FloatSin -> "sin"
  | FloatSqrt -> "sqrt"
  | FloatSub -> "-."
  | FloatTan -> "tan"
  | IntegerAdd -> "+"
  | IntegerDiv -> "/"
  | IntegerMod -> "mod"
  | IntegerMul -> "*"
  | IntegerNeg -> "~-"
  | IntegerAbs -> "abs"
  | IntegerPow -> "**"
  | IntegerSub -> "-"
  | IntOfFloat -> "int_of_float"
  | StringConcat -> "^"
  | StringLength -> "string_length"
  | StringOfFloat -> "string_of_float"
  | StringOfInt -> "string_of_int"
  | StringSub -> "sub"
  | ToString -> "to_string"

let primitive_effect_name = function
  | Print -> "Print"
  | Read -> "Read"
  | Raise -> "Raise"
  | RandomInt -> "RandomInt"
  | RandomFloat -> "RandomFloat"
  | Write -> "Write"
