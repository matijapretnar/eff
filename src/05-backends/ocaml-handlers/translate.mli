open Language

val of_expression : Term.expression -> Syntax.term
val of_computation : Term.computation -> Syntax.term
val of_abstraction : Term.abstraction -> Syntax.abstraction
val of_pattern : Term.pattern -> Syntax.pattern
val of_type : Type.ty -> Syntax.ty
val of_tydef : Type.tydef -> Syntax.tydef
