module Multicore = MulticoreSyntax
module CoreSyntax = UntypedSyntax

val of_computation : CoreSyntax.computation -> Multicore.term

val of_pattern : CoreSyntax.pattern -> Multicore.pattern

val of_type : Type.ty -> Multicore.ty

val of_tydef : Tctx.tydef -> Multicore.tydef
