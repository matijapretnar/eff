open Utils
(** Syntax of the core language. *)

type t = (t', Type.ty) typed

and t' =
  | PVar of Variable.t
  | PAs of t * Variable.t
  | PTuple of t list
  | PRecord of t Type.Field.Map.t
  | PVariant of Type.Label.t * t option
  | PConst of Const.t
  | PNonbinding

let pVar p ty = { term = PVar p; ty }

let pAs (p, x) = { term = PAs (p, x); ty = p.ty }

let pNonbinding ty = { term = PNonbinding; ty }

let pConst c = { term = PConst c; ty = Type.type_const c }

let pTuple ps =
  { term = PTuple ps; ty = Type.tuple (List.map (fun x -> x.ty) ps) }

let pVariant (lbl, pat) ty = { term = PVariant (lbl, pat); ty }

let pRecord ty flds =
  (* Ideally, we could reconstruct ty from the field names *)
  { term = PRecord flds; ty }

let rec bound_vars pat =
  match pat.term with
  | PVar x -> Variable.Map.singleton x pat.ty
  | PAs (p, x) -> Variable.Map.add x pat.ty (bound_vars p)
  | PTuple lst ->
      List.fold_right
        (fun p -> Variable.Map.compatible_union (bound_vars p))
        lst Variable.Map.empty
  | PRecord lst ->
      Type.Field.Map.fold
        (fun _fld p -> Variable.Map.compatible_union (bound_vars p))
        lst Variable.Map.empty
  | PVariant (_, None) -> Variable.Map.empty
  | PVariant (_, Some p) -> bound_vars p
  | PConst _ -> Variable.Map.empty
  | PNonbinding -> Variable.Map.empty

let rec print ?max_level p ppf =
  let pp ?at_level = Print.print ?max_level ?at_level ppf in
  match p.term with
  | PVar x -> pp "%t" (Variable.print x)
  | PAs (p, x) -> pp "%t as %t" (print p) (Variable.print x)
  | PConst c -> Const.print c ppf
  | PTuple lst -> Print.tuple print lst ppf
  | PRecord lst ->
      Print.record Type.Field.print print (Type.Field.Map.bindings lst) ppf
  | PVariant (lbl, None) -> pp ~at_level:0 "%t" (Type.Label.print lbl)
  | PVariant (lbl, Some p) ->
      pp ~at_level:1 "%t %t" (Type.Label.print lbl) (print p)
  | PNonbinding -> pp "_"

let rec refresh sbst pat =
  let sbst', pat' = refresh' sbst pat.term in
  (sbst', { pat with term = pat' })

and refresh' sbst = function
  | PVar x ->
      let x' = Variable.refresh x in
      (Assoc.update x x' sbst, PVar x')
  | PAs (p, x) ->
      let x' = Variable.refresh x in
      let sbst, p' = refresh (Assoc.update x x' sbst) p in
      (sbst, PAs (p', x'))
  | PTuple ps ->
      let sbst, ps' =
        List.fold_right
          (fun p (sbst, ps') ->
            let sbst, p' = refresh sbst p in
            (sbst, p' :: ps'))
          ps (sbst, [])
      in
      (sbst, PTuple ps')
  | PRecord flds ->
      let sbst, flds' =
        Type.Field.Map.fold
          (fun lbl p (sbst, flds') ->
            let sbst, p' = refresh sbst p in
            (sbst, Type.Field.Map.add lbl p' flds'))
          flds
          (sbst, Type.Field.Map.empty)
      in
      (sbst, PRecord flds')
  | PVariant (lbl, Some p) ->
      let sbst, p' = refresh sbst p in
      (sbst, PVariant (lbl, Some p'))
  | (PConst _ | PNonbinding | PVariant (_, None)) as p -> (sbst, p)
