open Language
module Type = Language.Type
open Type

let pure_arrow t1 t2 = Type.arrow (t1, pure_ty t2)
let binary_op_ty t1 t2 ty = Type.arrow (t1, pure_ty (pure_arrow t2 ty))
let unary_integer_op_ty = TyScheme.monotype (pure_arrow int_ty int_ty)
let binary_integer_op_ty = TyScheme.monotype (binary_op_ty int_ty int_ty int_ty)
let unary_float_op_ty = TyScheme.monotype (pure_arrow float_ty float_ty)

let binary_float_op_ty =
  TyScheme.monotype (binary_op_ty float_ty float_ty float_ty)

let binary_string_op_ty =
  TyScheme.monotype (binary_op_ty string_ty string_ty string_ty)

let poly_ty ty_body =
  let ty = Type.fresh_ty_with_fresh_skel () in
  let params = Type.free_params_ty ty in
  {
    TyScheme.params;
    TyScheme.ty = ty_body ty;
    TyScheme.constraints = Constraints.empty;
  }

let comparison_ty = poly_ty (fun ty -> binary_op_ty ty ty bool_ty)

let primitive_value_type_scheme = function
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
  | FloatInfinity -> TyScheme.monotype float_ty
  | FloatLog -> unary_float_op_ty
  | FloatLog1p -> unary_float_op_ty
  | FloatMul -> binary_float_op_ty
  | FloatNaN -> TyScheme.monotype float_ty
  | FloatNeg -> unary_float_op_ty
  | FloatNegInfinity -> TyScheme.monotype float_ty
  | FloatOfInt -> TyScheme.monotype (pure_arrow int_ty float_ty)
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
  | IntOfFloat -> TyScheme.monotype (pure_arrow float_ty int_ty)
  | StringConcat -> binary_string_op_ty
  | StringLength -> TyScheme.monotype (pure_arrow string_ty int_ty)
  | StringOfFloat -> TyScheme.monotype (pure_arrow float_ty string_ty)
  | StringOfInt -> TyScheme.monotype (pure_arrow int_ty string_ty)
  | StringSub ->
      TyScheme.monotype
        (pure_arrow string_ty (pure_arrow int_ty (pure_arrow int_ty string_ty)))
  | ToString -> poly_ty (fun ty -> pure_arrow ty string_ty)

let primitive_effect_signature = function
  | Primitives.Print -> (string_ty, Type.unit_ty)
  | Primitives.Read -> (Type.unit_ty, string_ty)
  | Primitives.Raise -> (string_ty, Type.empty_ty)
  | Primitives.RandomInt -> (int_ty, int_ty)
  | Primitives.RandomFloat -> (float_ty, float_ty)
  | Primitives.Write -> (Type.tuple [ string_ty; string_ty ], Type.unit_ty)
