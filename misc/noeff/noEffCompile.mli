val compile_type : Type.target_ty -> NoEffSyntax.ty

val compile_expr : Term.expression -> NoEffSyntax.term

val compile_comp : Term.computation -> NoEffSyntax.term

val compile_pattern : Term.pattern -> NoEffSyntax.pattern
