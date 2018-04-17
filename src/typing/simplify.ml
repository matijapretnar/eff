
(* represents a context and contains all free variables that occur *)
type context = (Untyped.variable, Type.ty) OldUtils.assoc

type automatype =
  | Alphabet of alphabet
  | Concat of automatype list
  | Union of automatype list
  | KleeneStar of automatype list
  | Empty
  | Epsilon

and alphabet =
  | Prim of (Type.prim_ty * bool)
  | Function of bool
  | Handler of bool
  | Alpha of (Params.ty_param * bool)
  | Domain of bool
  | Range of bool

(* Primitive types *)
(* and prim_ty =
  | BoolTy
  | IntTy
  | FloatTy
  | StringTy
  | UniTy *)

let boolToPolarity b = if (b) then "⁺" else "⁻"

let printAlphabet ?max_level enc ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match enc with
  | Prim (p, b) -> 
    print ~at_level:1 "%s" ((Type.prim_to_string p) ^ (boolToPolarity b))
  | Function b -> 
    print ~at_level:1 "%s" ("->" ^ (boolToPolarity b))
  | Handler b -> 
    print ~at_level:1 "%s" ("=>" ^ (boolToPolarity b))
  | Alpha (a, b) -> 
    Params.print_ty_param a ppf
  | Domain b ->
    print ~at_level:1 "%s" ("d" ^ (boolToPolarity b))
  | Range b -> 
    print ~at_level:1 "%s" ("r" ^ (boolToPolarity b))

let rec printAutomatype ?max_level enc ppf = 
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match enc with
  | Alphabet alphabet -> printAlphabet alphabet ppf
  | Concat c -> 
    print "(";
    Print.sequence " . " (fun elem ppf -> Format.fprintf ppf "%t" (printAutomatype elem)) c ppf;
    print ")"
  | Union c -> 
    print "(";
    Print.sequence " + " (fun elem ppf -> Format.fprintf ppf "%t" (printAutomatype elem)) c ppf;
    print ")"
  | KleeneStar c -> 
    assert false
  | Empty ->
    print ~at_level:1 "∅"
  | Epsilon -> 
    print ~at_level:1 "ε"

let rec encode ty polarity =
  begin match ty with
    | Type.Apply (ty_name, args) -> 
      assert false
    | Type.TyVar p -> 
      Alphabet (Alpha (p, polarity))
    | Type.Prim p -> 
      Alphabet (Prim (p, polarity))
    | Type.Tuple tys -> 
      assert false
    | Type.Arrow (ty1, (ty2, drt)) -> 
      Union [
        Concat [Alphabet (Domain polarity); encode ty1 (not polarity)];
        Concat [Alphabet (Range polarity); encode ty2 polarity];
        Alphabet (Function polarity)
      ]
    | Type.Handler (drty1, drty2) ->
      assert false
    | Type.Bottom -> 
      Empty
    | Type.Top -> 
      Empty
    | Type.Union (ty1, ty2) ->
      Union [
        encode ty1 polarity;
        encode ty2 polarity;
      ]
    | Type.Intersection (ty1, ty2) ->
      Union [
        encode ty1 polarity;
        encode ty2 polarity;
      ]
  end

let decode enc =
  match enc with
  | Alphabet alphabet -> 
    begin match alphabet with
      (* | Prim (p, b) when p == true ->  *)
        (* (Type.TyVar p, Type.Top) *)
      (* | Prim (p, b) when p == false ->  *)
        (* (Type.Bottom, Type.TyVar p) *)
      | Function b -> 
      assert false
      | Handler b -> 
      assert false
      | Alpha (a, b) -> 
      assert false
      | Domain b when b == true ->
        assert false
      | Range b -> 
      assert false
    end
  | Concat c -> 
  assert false
  | Union c -> 
  assert false
  | KleeneStar c -> 
  assert false
  | Empty ->
  assert false
  | Epsilon -> 
  assert false

let simplify_ty ctx ty = 
  (* let print = Print.print Format.std_formatter in *)
  (* let _ = printAutomatype (encode ty true) Format.std_formatter; print "end\n" in *)
  (ctx, ty)

let simplify_dirty ctx dirty = (ctx, dirty)