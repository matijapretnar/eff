val fprintf : Format.formatter -> ('a, Format.formatter, unit) format -> 'a
val print :
  ?max_level:int ->
  ?at_level:int ->
  Format.formatter -> ('a, Format.formatter, unit, unit) format4 -> 'a
val position : Common.position -> Format.formatter -> unit
val sequence :
  string ->
  ('a -> Format.formatter -> unit) -> 'a list -> Format.formatter -> unit
val field :
  ('a -> Format.formatter -> unit) -> string * 'a -> Format.formatter -> unit
val const : Common.const -> Format.formatter -> unit
val pattern : ?max_level:int -> int Pattern.t -> Format.formatter -> unit
val pattern_list : ?max_length:int -> int Pattern.t -> Format.formatter -> unit
val region_param :
  'a * 'b * Type.region_param list ->
  Type.region_param -> Format.formatter -> unit
val dirt_param :
  'a * Type.dirt_param list * 'b ->
  Type.dirt_param -> Format.formatter -> unit
val region :
  'a * 'b * Type.region_param list -> Constr.region -> Format.formatter -> unit
val dirt :
  'a * Type.dirt_param list * Type.region_param list ->
  Constr.dirt -> Format.formatter -> unit
val fresh_instances : Type.instance_param list -> Format.formatter -> unit
val ty_param :
  Type.ty_param list -> Type.ty_param -> Format.formatter -> unit
val ty :
  Type.ty_param list * Type.dirt_param list * Type.region_param list ->
  Type.ty -> Format.formatter -> unit
val constraints :
  Type.ty_param list * Type.dirt_param list * Type.region_param list ->
  Constr.constraints list -> Format.formatter -> unit
val ty_scheme :
  (Type.ty_param list * Type.dirt_param list * Type.region_param list) *
  Type.ty * Constr.constraints list -> Format.formatter -> unit
val dirty_scheme :
  (Type.ty_param list * Type.dirt_param list * Type.region_param list) *
  Type.ty * Constr.constraints list ->
  Type.dirt_param -> Format.formatter -> unit
val beautified_ty_scheme :
  (Type.ty_param list * Type.dirt_param list * Type.region_param list) *
  Type.ty * Constr.constraints list -> Format.formatter -> unit
val beautified_dirty_scheme :
  (Type.ty_param list * Type.dirt_param list * Type.region_param list) *
  Type.ty * Constr.constraints list ->
  Type.dirt_param -> Format.formatter -> unit
val computation :
  ?max_level:int -> Core.computation -> Format.formatter -> unit
val expression :
  ?max_level:int -> Core.expression -> Format.formatter -> unit
val abstraction : Core.abstraction -> Format.formatter -> unit
val let_abstraction :
  int Pattern.t * Core.computation -> Format.formatter -> unit
val case : Core.abstraction -> Format.formatter -> unit
val instance : int * string option * 'a -> Format.formatter -> unit
val operation :
  (int * string option * 'a) * string -> Format.formatter -> unit
val value : ?max_level:int -> Value.value -> Format.formatter -> unit
val list : ?max_length:int -> Value.value -> Format.formatter -> unit
val result : Value.result -> Format.formatter -> unit
val to_string : ('a, Format.formatter, unit, string) format4 -> 'a
val verbosity : int ref
val message :
  ?pos:Common.position ->
  string -> int -> ('a, Format.formatter, unit, unit) format4 -> 'a
val error : Common.position option * string * string -> unit
val check :
  pos:Common.position -> ('a, Format.formatter, unit, unit) format4 -> 'a
val warning :
  pos:Common.position -> ('a, Format.formatter, unit, unit) format4 -> 'a
val debug :
  ?pos:Common.position -> ('a, Format.formatter, unit, unit) format4 -> 'a
