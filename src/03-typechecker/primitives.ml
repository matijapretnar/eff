open Language

let mono_type ty = ([], ty)

let poly_type ty =
  let a = CoreTypes.TyParam.fresh () in
  ([ a ], ty (Type.TyParam a))

let unary_integer_op_ty =
  ([], Type.Arrow (Type.Basic Const.IntegerTy, Type.Basic Const.IntegerTy))

let binary_op_ty ty1 ty2 ty = Type.Arrow (ty1, Type.Arrow (ty2, ty))

let binary_integer_op_ty = ([], binary_op_ty Type.int_ty Type.int_ty Type.int_ty)

let unary_float_op_ty = ([], Type.Arrow (Type.float_ty, Type.float_ty))

let binary_float_op_ty =
  ([], binary_op_ty Type.float_ty Type.float_ty Type.float_ty)

let comparison_ty = poly_type (fun a -> binary_op_ty a a Type.bool_ty)

let primitive_type_scheme = function
  | Primitives.CompareEq -> comparison_ty
  | Primitives.CompareGe -> comparison_ty
  | Primitives.CompareGt -> comparison_ty
  | Primitives.CompareLe -> comparison_ty
  | Primitives.CompareLt -> comparison_ty
  | Primitives.CompareNe -> comparison_ty
  | Primitives.FloatAcos -> unary_float_op_ty
  | Primitives.FloatAdd -> binary_float_op_ty
  | Primitives.FloatAsin -> unary_float_op_ty
  | Primitives.FloatAtan -> unary_float_op_ty
  | Primitives.FloatCos -> unary_float_op_ty
  | Primitives.FloatDiv -> binary_float_op_ty
  | Primitives.FloatExp -> unary_float_op_ty
  | Primitives.FloatExpm1 -> unary_float_op_ty
  | Primitives.FloatInfinity -> mono_type Type.float_ty
  | Primitives.FloatLog -> unary_float_op_ty
  | Primitives.FloatLog1p -> unary_float_op_ty
  | Primitives.FloatMul -> binary_float_op_ty
  | Primitives.FloatNaN -> mono_type Type.float_ty
  | Primitives.FloatNeg -> unary_float_op_ty
  | Primitives.FloatNegInfinity -> mono_type Type.float_ty
  | Primitives.FloatOfInt -> mono_type (Type.Arrow (Type.int_ty, Type.float_ty))
  | Primitives.FloatSin -> binary_float_op_ty
  | Primitives.FloatSqrt -> binary_float_op_ty
  | Primitives.FloatSub -> binary_float_op_ty
  | Primitives.FloatTan -> binary_float_op_ty
  | Primitives.IntegerAdd -> binary_integer_op_ty
  | Primitives.IntegerDiv -> binary_integer_op_ty
  | Primitives.IntegerMod -> binary_integer_op_ty
  | Primitives.IntegerMul -> binary_integer_op_ty
  | Primitives.IntegerNeg -> unary_integer_op_ty
  | Primitives.IntegerAbs -> unary_integer_op_ty
  | Primitives.IntegerPow -> binary_integer_op_ty
  | Primitives.IntegerSub -> binary_integer_op_ty
  | Primitives.IntOfFloat -> mono_type (Type.Arrow (Type.float_ty, Type.int_ty))
  | Primitives.StringConcat ->
      mono_type (binary_op_ty Type.string_ty Type.string_ty Type.string_ty)
  | Primitives.StringLength ->
      mono_type (Type.Arrow (Type.string_ty, Type.int_ty))
  | Primitives.StringOfFloat ->
      mono_type (Type.Arrow (Type.float_ty, Type.string_ty))
  | Primitives.StringOfInt ->
      mono_type (Type.Arrow (Type.int_ty, Type.string_ty))
  | Primitives.StringSub ->
      mono_type
        (Type.Arrow
           ( Type.string_ty,
             Type.Arrow (Type.int_ty, Type.Arrow (Type.int_ty, Type.string_ty))
           ))
  | Primitives.ToString ->
      poly_type (fun a -> Type.Arrow (a, Type.Basic Const.StringTy))
