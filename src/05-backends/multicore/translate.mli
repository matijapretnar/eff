open Language
module CoreSyntax = UntypedSyntax

val of_computation : CoreSyntax.computation -> Syntax.term

val of_pattern : CoreSyntax.pattern -> Syntax.pattern

val of_type : Type.ty -> Syntax.ty

val of_tydef : Type.tydef -> Syntax.tydef
