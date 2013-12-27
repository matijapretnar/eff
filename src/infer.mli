val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
         val infer_let :
           pos:Common.position ->
           Ctx.t ->
           (Syntax.variable Pattern.t * Syntax.computation) list ->
           (Syntax.variable * Scheme.ty_scheme) list * Scheme.context *
           (Scheme.context * Type.dirty * Constraints.t ->
            Scheme.context * Type.dirty * Constraints.t)
         val infer_let_rec :
           pos:Common.position ->
           Ctx.t ->
           (Syntax.variable * Syntax.abstraction) list ->
           (Syntax.variable * Scheme.ty_scheme) list *
           (Scheme.context * Type.dirty * Constraints.t ->
            Scheme.context * Type.dirty * Constraints.t)
 val infer_comp : Ctx.t -> Syntax.computation -> Scheme.dirty_scheme