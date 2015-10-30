(** Syntax of the core language. *)

module Variable = Symbol.Make(Symbol.String)
module EffectMap = Map.Make(String)

type variable = Variable.t
type pattern = variable Pattern.t

type ('term, 'scheme) annotation = {
  term: 'term;
  scheme: 'scheme;
  location: Location.t;
}

let annotate t sch loc = {
  term = t;
  scheme = sch;
  location = loc;
}

(** Pure expressions *)
type expression = (plain_expression, Scheme.ty_scheme) annotation
and plain_expression =
  | Var of variable
  | Const of Const.t
  | Tuple of expression list
  | Record of (Common.field, expression) Common.assoc
  | Variant of Common.label * expression option
  | Lambda of abstraction
  | Effect of Common.effect
  | Handler of handler

(** Impure computations *)
and computation = (plain_computation, Scheme.dirty_scheme) annotation
and plain_computation =
  | Value of expression
  | Let of (pattern * computation) list * computation
  | LetRec of (variable * abstraction) list * computation
  | Match of expression * abstraction list
  | While of computation * computation
  | For of variable * expression * expression * computation * bool
  | Apply of expression * expression
  | Handle of expression * computation
  | Check of computation

(** Handler definitions *)
and handler = {
  operations : (operation, abstraction2) Common.assoc;
  value : abstraction;
  finally : abstraction;
}

(** Abstractions that take one argument. *)
and abstraction = pattern * computation

(** Abstractions that take two arguments. *)
and abstraction2 = pattern * pattern * computation

and operation = Common.opsym

let empty_dirt () = { Type.ops = []; Type.rest = Type.fresh_dirt_param () }

let const ~loc c =
  let ty = match c with
  | Const.Integer _ -> Type.int_ty
  | Const.String _ -> Type.string_ty
  | Const.Boolean _ -> Type.bool_ty
  | Const.Float _ -> Type.float_ty
  in
  {
    term = Const c;
    scheme = ([], ty, Constraints.empty);
    location = loc;
  }

let tuple ~loc es =
  let ctx, tys, constraints =
    List.fold_right (fun e (ctx, tys, constraints) ->
      let e_ctx, e_ty, e_constraints = e.scheme in
      e_ctx @ ctx, e_ty :: tys, Constraints.union e_constraints constraints
    ) es ([], [], Constraints.empty)
  in
  {
    term = Tuple es;
    scheme = Scheme.normalize_context ~loc (ctx, Type.Tuple tys, constraints);
    location = loc;
  }

let value ~loc e =
  let ctx, ty, constraints = e.scheme in
  {
    term = Value e;
    scheme = (ctx, (ty, empty_dirt ()), constraints);
    location = loc
  }
