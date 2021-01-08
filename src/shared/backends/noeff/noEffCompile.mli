val compile_type : Types.target_ty -> NoEffSyntax.ty

val compile_expr : Typed.expression -> NoEffSyntax.term

val compile_comp : Typed.computation -> NoEffSyntax.term

val compile_pattern : Typed.pattern -> NoEffSyntax.pattern
