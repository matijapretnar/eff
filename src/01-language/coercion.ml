open Utils

type ty_coercion = (ty_coercion', Type.ct_ty) typed

and ty_coercion' =
  | ReflTy
  | ArrowCoercion of ty_coercion * dirty_coercion
  | HandlerCoercion of dirty_coercion * dirty_coercion
  | TyCoercionVar of Type.TyCoercionParam.t
  | ApplyCoercion of {
      ty_name : TyName.t;
      tcoers : (ty_coercion * variance) TyParam.Map.t;
    }
  | TupleCoercion of ty_coercion list

and dirt_coercion = (dirt_coercion', Type.ct_dirt) typed

and dirt_coercion' =
  | ReflDirt
  | DirtCoercionVar of Type.DirtCoercionParam.t
  | Empty
  | UnionDirt of (Effect.Set.t * dirt_coercion)

and dirty_coercion = (ty_coercion * dirt_coercion, Type.ct_dirty) typed

let is_trivial_ty_coercion omega =
  let ty1, ty2 = omega.ty in
  Type.equal_ty ty1 ty2

let is_trivial_dirty_coercion omega =
  let drty1, drty2 = omega.ty in
  Type.equal_dirty drty1 drty2

let reflTy ty = { term = ReflTy; ty = (ty, ty) }

let tyCoercionVar omega ct = { term = TyCoercionVar omega; ty = ct }

let dirtCoercionVar omega cd = { term = DirtCoercionVar omega; ty = cd }

let arrowCoercion (tcoer1, dtcoer2) =
  let ty1, ty1' = tcoer1.ty and drty2, drty2' = dtcoer2.ty in
  {
    term = ArrowCoercion (tcoer1, dtcoer2);
    ty = (Type.arrow (ty1', drty2), Type.arrow (ty1, drty2'));
  }

let tupleCoercion tcoers =
  let tys, tys' = tcoers |> List.map (fun tcoer -> tcoer.ty) |> List.split in
  { term = TupleCoercion tcoers; ty = (Type.tuple tys, Type.tuple tys') }

let applyCoercion (ty_name, tcoers) =
  let tys, tys' =
    TyParam.Map.bindings tcoers
    |> List.map (fun (p, (tcoer, variance)) ->
           let t1, t2 = tcoer.ty in
           ((p, (t1, variance)), (p, (t2, variance))))
    |> List.split
  in
  {
    term = ApplyCoercion { ty_name; tcoers };
    ty =
      ( Type.apply (ty_name, tys |> TyParam.Map.of_bindings),
        Type.apply (ty_name, tys' |> TyParam.Map.of_bindings) );
  }

let handlerCoercion (dtcoer1, dtcoer2) =
  let drty1, drty1' = dtcoer1.ty and drty2, drty2' = dtcoer2.ty in
  {
    term = HandlerCoercion (dtcoer1, dtcoer2);
    ty = (Type.handler (drty1', drty2), Type.handler (drty1, drty2'));
  }

let bangCoercion ((ty_coer : ty_coercion), (drt_coer : dirt_coercion)) =
  let ty, ty' = ty_coer.ty and drt, drt' = drt_coer.ty in
  { term = (ty_coer, drt_coer); ty = ((ty, drt), (ty', drt')) }

let reflDirt drt = { term = ReflDirt; ty = (drt, drt) }

let reflDirty (ty, drt) = bangCoercion (reflTy ty, reflDirt drt)

let empty drt = { term = Empty; ty = (Dirt.empty, drt) }

let unionDirt (effs, dcoer) =
  let drt, drt' = dcoer.ty in
  {
    term = UnionDirt (effs, dcoer);
    ty = (Dirt.add_effects effs drt, Dirt.add_effects effs drt');
  }

(* ************************************************************************* *)
(*                         COERCION VARIABLES OF                             *)
(* ************************************************************************* *)

let rec print_ty_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | ReflTy -> print "⟨%t⟩" (Type.print_ty (fst c.ty))
  | ArrowCoercion (tc1, { term = tc2, dc2; _ }) ->
      print ~at_level:3 "%t -{%t}→ %t"
        (print_ty_coercion ~max_level:2 tc1)
        (print_dirt_coercion dc2)
        (print_ty_coercion ~max_level:3 tc2)
  | HandlerCoercion (dc1, dc2) ->
      print "%t ⇛ %t"
        (print_dirty_coercion ~max_level:2 dc1)
        (print_dirty_coercion ~max_level:2 dc2)
  | TyCoercionVar tcp -> print "%t" (Type.TyCoercionParam.print tcp)
  | ApplyCoercion { ty_name; tcoers } -> (
      match TyParam.Map.values tcoers with
      | [] -> print "%t" (TyName.print ty_name)
      | [ (c, _) ] ->
          print ~at_level:1 "%t %t"
            (print_ty_coercion ~max_level:1 c)
            (TyName.print ty_name)
      | cs ->
          let cs = List.map fst cs in
          print ~at_level:1 "(%t) %t"
            (Print.sequence ", " print_ty_coercion cs)
            (TyName.print ty_name))
  | TupleCoercion [] -> print "𝟙"
  | TupleCoercion cos ->
      print ~at_level:2 "%t"
        (Print.sequence "×" (print_ty_coercion ~max_level:1) cos)

and print_dirty_coercion ?max_level { term = tc, dirtc; _ } ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  print ~at_level:2 "%t!%t"
    (print_ty_coercion ~max_level:0 tc)
    (print_dirt_coercion ~max_level:0 dirtc)

and print_dirt_coercion ?max_level c ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.term with
  | ReflDirt -> print "⟨%t⟩" (Dirt.print (fst c.ty))
  | DirtCoercionVar tcp -> print "%t" (Type.DirtCoercionParam.print tcp)
  | Empty ->
      print ~at_level:1 "∅↪︎%t" (Dirt.print ~max_level:0 (snd c.ty))
  | UnionDirt (eset, dc) ->
      print ~at_level:2 "{%t}∪%t" (Effect.Set.print eset)
        (print_dirt_coercion ~max_level:2 dc)

(* ************************************************************************* *)

(* free variables in target terms *)

let rec free_params_ty_coercion coer =
  Type.Params.union
    (free_params_ty_coercion' coer.term)
    (Type.free_params_ct_ty coer.ty)

and free_params_ty_coercion' = function
  | ReflTy -> Type.Params.empty
  | ArrowCoercion (tc, dc) ->
      Type.Params.union
        (free_params_ty_coercion tc)
        (free_params_dirty_coercion dc)
  | HandlerCoercion (dc1, dc2) ->
      Type.Params.union
        (free_params_dirty_coercion dc1)
        (free_params_dirty_coercion dc2)
  | TyCoercionVar _tcp -> Type.Params.empty
  | TupleCoercion tcs ->
      List.fold_left
        (fun free tc -> Type.Params.union free (free_params_ty_coercion tc))
        Type.Params.empty tcs
  | ApplyCoercion { tcoers; _ } ->
      TyParam.Map.fold
        (fun _ (tc, _) free ->
          Type.Params.union free (free_params_ty_coercion tc))
        tcoers Type.Params.empty

and free_params_dirt_coercion coer = Type.free_params_ct_dirt coer.ty

and free_params_dirty_coercion { term = tc, dc; _ } =
  Type.Params.union (free_params_ty_coercion tc) (free_params_dirt_coercion dc)
