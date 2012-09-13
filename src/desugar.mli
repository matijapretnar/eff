val external_ty :
  (Common.tyname -> bool) ->
  Syntax.ty ->
  (Type.ty_param, Type.dirt_param, Type.region_param) Trio.t * Type.ty * 'a list
val tydefs :
  pos:Common.position ->
  (Common.tyname * (Common.typaram list * Syntax.tydef)) list ->
  (Common.tyname *
   ((Type.ty_param, Type.dirt_param, Type.region_param) Trio.t * Tctx.tydef))
  list
val computation : Syntax.term -> Core.computation
val let_rec : Syntax.term -> Core.abstraction
