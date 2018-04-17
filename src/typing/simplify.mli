
(* represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) OldUtils.assoc

(* simplify the types of a pure type *)
val simplify_ty : context -> Type.ty -> (context * Type.ty)

(* simplify the types of a dirty type *)
val simplify_dirty : context -> Type.dirty -> (context * Type.dirty)