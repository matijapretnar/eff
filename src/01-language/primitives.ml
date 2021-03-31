type primitive =
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

(* Keep this list up to date with the type above, otherwise the missing primitives will not be loaded *)
let primitives =
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

let primitive_name = function
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
