open Utils

type t = (t', Type.ct_dirt) typed

and t' =
  | ReflDirt
  | DirtCoercionVar of Type.DirtCoercionParam.t
  | Empty
  | UnionDirt of (Effect.Set.t * t)
  | UnionRight of (Effect.Set.t * t)

let dirtCoercionVar omega cd = { term = DirtCoercionVar omega; ty = cd }
let reflDirt drt = { term = ReflDirt; ty = (drt, drt) }
let empty drt = { term = Empty; ty = (Dirt.empty, drt) }

let unionDirt (effs, dcoer) =
  let drt, drt' = dcoer.ty in
  {
    term = UnionDirt (effs, dcoer);
    ty = (Dirt.add_effects effs drt, Dirt.add_effects effs drt');
  }

let unionRight (effs, dcoer) =
  let drt, drt' = dcoer.ty in
  { term = UnionRight (effs, dcoer); ty = (drt, Dirt.add_effects effs drt') }

let rec equal_dirt_coercion dc1 dc2 =
  let d1, d1' = dc1.ty and d2, d2' = dc2.ty in
  Type.equal_dirt d1 d2 && Type.equal_dirt d1' d2'
  &&
  match (dc1.term, dc2.term) with
  | ReflDirt, ReflDirt -> true
  | Empty, Empty -> true
  | DirtCoercionVar dv1, DirtCoercionVar dv2 -> dv1 = dv2
  | UnionDirt (es1, dc1), UnionDirt (es2, dc2) ->
      Effect.Set.equal es1 es2 && equal_dirt_coercion dc1 dc2
  | _ -> false
