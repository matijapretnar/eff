open Type

let pure_arrow t1 t2 = Type.Arrow (t1, pure_ty t2)

let binary_op_ty t1 t2 ty = Type.Arrow (t1, pure_ty (pure_arrow t2 ty))

let int_ty = Type.TyBasic Const.IntegerTy

let float_ty = Type.TyBasic Const.FloatTy

let bool_ty = Type.TyBasic Const.BooleanTy

let string_ty = Type.TyBasic Const.StringTy

let unary_integer_op_ty = pure_arrow int_ty int_ty

let binary_integer_op_ty = binary_op_ty int_ty int_ty int_ty

let unary_float_op_ty = pure_arrow float_ty float_ty

let binary_float_op_ty = binary_op_ty float_ty float_ty float_ty

let binary_string_op_ty = binary_op_ty string_ty string_ty string_ty

(* TODO: I want to be polymorphic *)
let comparison_ty = binary_op_ty int_ty int_ty bool_ty

let primitive_type_scheme = function
  | Language.Primitives.CompareEq -> comparison_ty
  | CompareGe -> comparison_ty
  | CompareGt -> comparison_ty
  | CompareLe -> comparison_ty
  | CompareLt -> comparison_ty
  | CompareNe -> comparison_ty
  | FloatAcos -> unary_float_op_ty
  | FloatAdd -> binary_float_op_ty
  | FloatAsin -> unary_float_op_ty
  | FloatAtan -> unary_float_op_ty
  | FloatCos -> unary_float_op_ty
  | FloatDiv -> binary_float_op_ty
  | FloatExp -> unary_float_op_ty
  | FloatExpm1 -> unary_float_op_ty
  | FloatInfinity -> float_ty
  | FloatLog -> unary_float_op_ty
  | FloatLog1p -> unary_float_op_ty
  | FloatMul -> binary_float_op_ty
  | FloatNaN -> float_ty
  | FloatNeg -> unary_float_op_ty
  | FloatNegInfinity -> float_ty
  | FloatOfInt -> pure_arrow int_ty float_ty
  | FloatSin -> binary_float_op_ty
  | FloatSqrt -> binary_float_op_ty
  | FloatSub -> binary_float_op_ty
  | FloatTan -> binary_float_op_ty
  | IntegerAdd -> binary_integer_op_ty
  | IntegerDiv -> binary_integer_op_ty
  | IntegerMod -> binary_integer_op_ty
  | IntegerMul -> binary_integer_op_ty
  | IntegerNeg -> unary_integer_op_ty
  | IntegerAbs -> unary_integer_op_ty
  | IntegerPow -> binary_integer_op_ty
  | IntegerSub -> binary_integer_op_ty
  | IntOfFloat -> pure_arrow float_ty int_ty
  | StringConcat -> binary_string_op_ty
  | StringLength -> pure_arrow string_ty int_ty
  | StringOfFloat -> pure_arrow string_ty float_ty
  | StringOfInt -> pure_arrow string_ty int_ty
  | StringSub ->
      pure_arrow string_ty (pure_arrow int_ty (pure_arrow int_ty string_ty))
  | ToString -> pure_arrow int_ty string_ty
