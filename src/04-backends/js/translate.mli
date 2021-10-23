open Language
module CoreSyntax = UntypedSyntax

val of_computation : CoreSyntax.computation -> Syntax.js_term

val of_abstraction :
  ?_match_gen:CoreTypes.Variable.t option ->
  CoreSyntax.abstraction ->
  Syntax.variable * Syntax.js_term

val of_abstraction_generic :
  ?_match_gen:CoreTypes.Variable.t option ->
  CoreSyntax.abstraction ->
  Syntax.variable * Syntax.js_term list * Syntax.js_term
