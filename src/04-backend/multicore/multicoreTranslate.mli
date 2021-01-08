open Language
module CoreSyntax = UntypedSyntax

val of_computation : CoreSyntax.computation -> MulticoreSyntax.term

val of_pattern : CoreSyntax.pattern -> MulticoreSyntax.pattern

val of_type : Type.ty -> MulticoreSyntax.ty

val of_tydef : Type.tydef -> MulticoreSyntax.tydef
