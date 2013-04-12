val warn_implicit_sequencing : bool ref
val disable_typing : bool ref
         val infer_let :
           pos:Common.position ->
           Ctx.t ->
           (Core.variable Pattern.t * Core.computation) list ->
           (Core.variable * Scheme.ty_scheme) list *
           (Core.variable * Type.ty) list * (Core.variable * Type.ty) list *
           Type.dirt * Scheme.change list *
           (Scheme.dirty_scheme -> Scheme.dirty_scheme)
         val infer_let_rec :
           pos:Common.position ->
           Ctx.t ->
           (Core.variable * Core.abstraction) list ->
           (Core.variable * Scheme.ty_scheme) list *
           (Core.variable * Type.ty) list * (Core.variable * Type.ty) list *
           Scheme.change list *
           ((Core.variable * Type.ty) list * Type.dirty * Constraints.t ->
            Scheme.context * Type.dirty * Constraints.t)
 val infer_comp : Ctx.t -> Core.computation -> Scheme.dirty_scheme