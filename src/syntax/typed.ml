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

let var ~loc x ty_sch =
  {
    term = Var x;
    scheme = ty_sch;
    location = loc;
  }

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
    scheme = Scheme.clean_ty_scheme ~loc (ctx, Type.Tuple tys, constraints);
    location = loc;
  }

let record ~loc = function
  | [] -> assert false
  | ((fld, _) :: _) as lst ->
    if not (Pattern.linear_record lst) then
      Error.typing ~loc "Fields in a record must be distinct";
    begin match Tctx.infer_field fld with
    | None -> Error.typing ~loc "Unbound record field label %s" fld
    | Some (ty, (ty_name, fld_tys)) ->
        if List.length lst <> List.length fld_tys then
          Error.typing ~loc "The record of type %s has an incorrect number of fields" ty_name;
        let infer (fld, e) (ctx, constraints) =
          begin match Common.lookup fld fld_tys with
          | None -> Error.typing ~loc "Unexpected field %s in a record of type %s" fld ty_name
          | Some fld_ty ->
              let e_ctx, e_ty, e_constraints = e.scheme in
              e_ctx @ ctx, Constraints.add_ty_constraint ~loc e_ty fld_ty constraints
          end
      in
      let ctx, constraints = List.fold_right infer lst ([], Constraints.empty) in
      {
        term = Record lst;
        scheme = Scheme.clean_ty_scheme ~loc (ctx, ty, constraints);
        location = loc;
      }
    end

let variant ~loc (lbl, e) =
    begin match Tctx.infer_variant lbl with
    | None -> Error.typing ~loc "Unbound constructor %s" lbl
    | Some (ty, arg_ty) ->
        let ty_sch = begin match e, arg_ty with
          | None, None -> ([], ty, Constraints.empty)
          | Some e, Some arg_ty ->
              let e_ctx, e_ty, e_constraints = e.scheme in
              let constraints = Constraints.add_ty_constraint ~loc e_ty arg_ty e_constraints in
              e_ctx, ty, constraints
          | None, Some _ -> Error.typing ~loc "Constructor %s should be applied to an argument" lbl
          | Some _, None -> Error.typing ~loc "Constructor %s cannot be applied to an argument" lbl
        end
        in
        {
          term = Variant (lbl, e);
          scheme = ty_sch;
          location = loc
        }
    end

let effect ~loc eff signature =
    match signature eff with
    | None -> Error.typing ~loc "Unbound effect %s" eff
    | Some (ty_par, ty_res) ->
      let r = Type.fresh_region_param () in
      let drt = {Type.ops = [eff, r]; Type.rest = Type.fresh_dirt_param ()} in
      let ty = Type.Arrow (ty_par, (ty_res, drt)) in
      let constraints = Constraints.add_full_region r Constraints.empty in
      {
        term = Effect eff;
        scheme = Scheme.clean_ty_scheme ~loc ([], ty, constraints);
        location = loc;
      }
(* 
let match_cases ~loc e cases =
  let ctx_e, ty_e, cnstrs_e = e.scheme in
  let drty = Type.fresh_dirty (), empty_dirt () in
  let drty_sch = match cases with
  | [] ->
      let constraints = Constraints.add_ty_constraint ~loc ty_e Type.empty_ty cnstrs_e in
      (ctx_e, drty, constraints)
  | _::_ ->
      let infer_case ((p, ty_p) (c_drty_c as a) (ctx, constraints) =
        let ctx_a, ty_p, drty_c, cnstrs_a = a in
        ctx_a @ ctx,
          Constraints.add_ty_constraint ~loc:e.Untyped.location ty_e ty_p (
          Constraints.add_dirty_constraint ~loc:c.Untyped.location drty_c drty (
          Constraints.unon cnstrs_a constraints))
      in
      let ctx, constraints = List.fold_right infer_case cases (ctx_e, cnstrs_e) in
      (ctx, drty, constraints)
  in
  {
    term = Match (e, cases);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc
  } *)
  


let value ~loc e =
  let ctx, ty, constraints = e.scheme in
  {
    term = Value e;
    scheme = (ctx, (ty, empty_dirt ()), constraints);
    location = loc
  }

let while' ~loc c1 c2 =
  let ctx_c1, (ty_c1, drt_c1), cnstrs_c1 = c1.scheme in
  let ctx_c2, (ty_c2, drt_c2), cnstrs_c2 = c2.scheme in
  let drt = Type.fresh_dirt () in
  let drty_sch =
    (ctx_c1 @ ctx_c2, (Type.unit_ty, drt),
        Constraints.add_ty_constraint ~loc ty_c1 Type.bool_ty (
        Constraints.add_ty_constraint ~loc ty_c2 Type.unit_ty (
        Constraints.add_dirt_constraint drt_c1 drt (
        Constraints.add_dirt_constraint drt_c2 drt (
        Constraints.union cnstrs_c1 (
        cnstrs_c2
    )))))) in
  {
    term = While (c1, c2);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let for' ~loc i e1 e2 c up =
  let ctx_e1, ty_e1, cnstrs_e1 = e1.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.scheme in
  let ctx_c, (ty_c, drt_c), cnstrs_c = c.scheme in
  let drty_sch =
    (ctx_e1 @ ctx_e2 @ ctx_c, (Type.unit_ty, drt_c),
        Constraints.add_ty_constraint ~loc:e1.location ty_e1 Type.int_ty (
        Constraints.add_ty_constraint ~loc:e2.location ty_e2 Type.int_ty (
        Constraints.add_ty_constraint ~loc:c.location ty_c Type.unit_ty (
        Constraints.union cnstrs_e1 (
        Constraints.union cnstrs_e2 (
        cnstrs_c
    )))))) in
  {
    term = For (i, e1, e2, c, up);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let apply ~loc e1 e2 =
  let ctx_e1, ty_e1, cnstrs_e1 = e1.scheme in
  let ctx_e2, ty_e2, cnstrs_e2 = e2.scheme in
  let drty = Type.fresh_dirty () in
  let constraints =
    Constraints.add_ty_constraint ~loc ty_e1 (Type.Arrow (ty_e2, drty)) (
    Constraints.union cnstrs_e1 cnstrs_e2) in
  let drty_sch = (ctx_e1 @ ctx_e2, drty, constraints) in
  {
    term = Apply (e1, e2);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let handle ~loc e c =
  let ctx_e, ty_e, cnstrs_e = e.scheme in
  let ctx_c, drty_c, cnstrs_c = c.scheme in
  let drty = Type.fresh_dirty () in
  let constraints =
    Constraints.add_ty_constraint ~loc ty_e (Type.Handler (drty_c, drty)) (
    Constraints.union cnstrs_e cnstrs_c) in
  let drty_sch = (ctx_e @ ctx_c, drty, constraints) in
  {
    term = Handle (e, c);
    scheme = Scheme.clean_dirty_scheme ~loc drty_sch;
    location = loc;
  }

let check ~loc c =
  {
    term = Check c;
    scheme = ([], (Type.unit_ty, empty_dirt ()), Constraints.empty);
    location = loc;
  }
