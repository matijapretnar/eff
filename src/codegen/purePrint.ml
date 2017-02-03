open CommonPrint

type ty_shape =
  | Basic
  | Arrow of ty_shape * dirty_shape
  | Handler of dirty_shape * dirty_shape
  | Tuple of ty_shape list
and dirty_shape =
  | Value of ty_shape
  | Computation of ty_shape

let rec shape_of_ty st = function
  | Type.Param _ -> Basic
  | Type.Apply _ -> Basic
  | Type.Basic _ -> Basic
  | Type.Arrow (ty, dirty) -> Arrow (shape_of_ty st ty, shape_of_dirty st dirty)
  | Type.Tuple tys -> Tuple (List.map (shape_of_ty st) tys)
  | Type.Handler (dirty1, dirty2) -> Handler (shape_of_dirty st dirty1, shape_of_dirty st dirty2)
  | ty -> Print.debug "Don't know the shape of %t" (Type.print_ty ty); assert false
and shape_of_dirty ((ctx, constraints) as st) (ty, drt) =
  if Scheme.is_surely_pure (ctx, (ty, drt), constraints) then
    Value (shape_of_ty st ty)
  else
    Computation (shape_of_ty st ty)

type ty_conversion =
  | TyIdentity
  | Lift of ty_conversion * dirty_conversion
  | LiftHandler of dirty_conversion * dirty_conversion
  | Tuple of ty_conversion list
and dirty_conversion =
  | DirtyIdentity
  | Value of ty_conversion
  | ConvertValues of ty_conversion
  | ConvertComps of ty_conversion

let rec simplify_ty_conversion = function
  | TyIdentity -> TyIdentity
  | Tuple convs ->
      let convs = List.map simplify_ty_conversion convs in
      if List.for_all (fun conv -> conv = TyIdentity) convs then
        TyIdentity
      else
        Tuple convs
  | Lift (conv1, conv2) ->
      begin match simplify_ty_conversion conv1, simplify_dirty_conversion conv2 with
      | TyIdentity, DirtyIdentity -> TyIdentity
      | conv1, conv2 -> Lift (conv1, conv2)
      end
  | LiftHandler (conv1, conv2) ->
      begin match simplify_dirty_conversion conv1, simplify_dirty_conversion conv2 with
      | DirtyIdentity, DirtyIdentity -> TyIdentity
      | conv1, conv2 -> LiftHandler (conv1, conv2)
      end
and simplify_dirty_conversion = function
  | DirtyIdentity -> DirtyIdentity
  | Value conv -> Value (simplify_ty_conversion conv)
  | ConvertValues conv ->
      begin match simplify_ty_conversion conv with
      | TyIdentity -> DirtyIdentity
      | conv -> ConvertValues conv
      end
  | ConvertComps conv ->
      begin match simplify_ty_conversion conv with
      | TyIdentity -> DirtyIdentity
      | conv -> ConvertComps conv
      end

let rec ty_shape_conversion = function
  | Basic _, Basic _ -> TyIdentity
  | Arrow (shape1, shape2), Arrow (shape1', shape2') ->
      Lift (
        ty_shape_conversion (shape1', shape1),
        dirty_shape_conversion (shape2, shape2')
      )
  | Handler (shape1, shape2), Handler (shape1', shape2') ->
      LiftHandler (
        dirty_shape_conversion (shape1', shape1),
        dirty_shape_conversion (shape2, shape2')
      )
  | Tuple shapes1, Tuple shapes2 ->
      Tuple (List.map2 (fun shape1 shape2 -> ty_shape_conversion (shape1, shape2)) shapes1 shapes2)
  | _, _ -> TyIdentity

and dirty_shape_conversion = function
  | Value shape, Value shape' ->
      ConvertValues (ty_shape_conversion (shape, shape'))
  | Value shape, Computation shape' ->
      Value (ty_shape_conversion (shape, shape'))
  | Computation shape, Computation shape' ->
      ConvertComps (ty_shape_conversion (shape, shape'))
  | Computation _, Value _ -> assert false

let rec print_ty_conversion ?(max_level=100000) conv term ppf =
  let print ?at_level = Print.print ~max_level ?at_level ppf in
  match conv with
  | TyIdentity ->
      (term max_level) ppf
  | Lift (TyIdentity, conv2) ->
      let x = Typed.Variable.fresh "x" in
          print ~at_level:2 "(* codomain *)fun %t -> %t"
                (print_variable x)
                (print_dirty_conversion conv2
                (fun m ppf -> Print.print ~max_level:m ppf "%t %t"
                  (term 1)
                  (print_variable x)))
  | Lift (conv1, DirtyIdentity) ->
      let x = Typed.Variable.fresh "x" in
          print ~at_level:2 "(* domain *)fun %t -> %t %t"
                (print_variable x)
                (term 1)
                (print_ty_conversion ~max_level:0 conv1 (fun _ -> print_variable x))
  | Lift (conv1, conv2) ->
      let x = Typed.Variable.fresh "x" in
          print ~at_level:2 "(* both *)fun %t -> %t"
                (print_variable x)
                (print_dirty_conversion conv2
                (fun m ppf -> Print.print ~max_level:m ppf "%t %t"
                  (term 1)
                  (print_ty_conversion ~max_level:0 conv1 (fun _ -> print_variable x))
                )
              )
  | LiftHandler (conv1, conv2) ->
      ()
  | Tuple convs ->
      let xs = List.mapi (fun i conv -> (Typed.Variable.fresh ("x" ^ string_of_int i), conv)) convs in
      print ~at_level:2 "let (%t) = %t in (%t)"
        (Print.sequence ", " print_variable (List.map fst xs))
        (term 100000000)
        (Print.sequence ", " (fun (x, conv) -> print_ty_conversion conv (fun _ -> print_variable x)) xs)
and print_dirty_conversion ?max_level conv (term : int -> Format.formatter -> unit) ppf =
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match conv with
  | DirtyIdentity ->
      (term : int -> Format.formatter -> unit) 1000000 ppf
  | ConvertValues conv ->
      print_ty_conversion ?max_level conv term ppf
  | Value conv ->
      print ~at_level:1 "value %t"
      (print_ty_conversion ~max_level:0 conv term)

let ty_scheme_conversion (ctx1, ty1, constraints1) tysch2 =
  match tysch2 with
  | None -> TyIdentity
  | Some (ctx2, ty2, constraints2) ->
      let shp1 = shape_of_ty (ctx1, constraints1) ty1
      and shp2 = shape_of_ty (ctx2, constraints2) ty2 in
      simplify_ty_conversion (ty_shape_conversion (shp1, shp2))
and dirty_scheme_conversion (ctx1, drty1, constraints1) tysch2 =
  match tysch2 with
  | None -> DirtyIdentity
  | Some (ctx2, drty2, constraints2) ->
      let shp1 = shape_of_dirty (ctx1, constraints1) drty1
      and shp2 = shape_of_dirty (ctx2, constraints2) drty2 in
      simplify_dirty_conversion (dirty_shape_conversion (shp1, shp2))

let rec print_expression ?max_level ?expected_scheme e ppf=
  let conv = ty_scheme_conversion e.Typed.scheme expected_scheme in
  print_ty_conversion ?max_level conv (fun m -> print_expression' ~max_level:m e) ppf

and print_expression' ?max_level e ppf =
  let (ctx, ty, constraints) = e.Typed.scheme in
  Print.debug "printing %t : %t" (Typed.print_expression e) (Scheme.print_ty_scheme e.Typed.scheme);
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match e.Typed.term with
  | Typed.Var x ->
    print "%t" (print_variable x)
  | Typed.BuiltIn (s, _) ->
    print "%s" s
  | Typed.Const c ->
    print "%t" (Const.print c)
  | Typed.Tuple lst ->
    Print.tuple print_expression lst ppf
  | Typed.Record lst ->
    Print.record print_expression lst ppf
  | Typed.Variant (lbl, None) ->
    print "%s" lbl
  | Typed.Variant (lbl, Some e) ->
    print ~at_level:1 "(%s %t)" lbl (print_expression e)
  | Typed.Lambda a ->
    print ~at_level:2 "fun %t" (print_abstraction a)
  | Typed.Handler h ->
    print "%t" (print_handler h)
  | Typed.Effect eff ->
    print ~at_level:2 "effect %t" (print_effect eff)
  | Typed.Pure c ->
    print_computation ?max_level c ppf

and print_computation ?max_level ?expected_scheme c ppf =
  let conv = dirty_scheme_conversion c.Typed.scheme expected_scheme in
  print_dirty_conversion ?max_level conv (fun m -> print_computation' ~max_level:m c) ppf

and print_computation' ?max_level c ppf =
  Print.debug "printing %t : %t" (Typed.print_computation c) (Scheme.print_dirty_scheme c.Typed.scheme);
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
    let (ctx, drty, constraints) = c.Typed.scheme in
    let (_, (Type.Arrow (ty1, _)), _) = e1.Typed.scheme in
    let expected_scheme1 = (ctx, (Type.Arrow (ty1, drty)), constraints)
    and expected_scheme2 = (ctx, ty1, constraints) in
    print ~at_level:1 "%t@ %t"
      (print_expression ~max_level:1 ~expected_scheme:expected_scheme1 e1)
      (print_expression ~max_level:0 ~expected_scheme:expected_scheme2 e2)
  | Typed.Value e ->
    let (ctx, (ty, _), constraints) = c.Typed.scheme in
    let expected_scheme = (ctx, ty, constraints) in
    print ~at_level:1 "%t" (print_expression ~max_level:0 ~expected_scheme e)
  | Typed.Match (e, []) ->
    print ~at_level:2 "(match %t with _ -> assert false)"
      (print_expression e)
  | Typed.Match (e, lst) ->
    let expected_scheme = c.Typed.scheme in
    print ~at_level:2 "(match %t with @[<v>| %t@])"
      (print_expression e)
      (Print.cases (print_abstraction ~expected_scheme) lst)
  | Typed.Handle (e, c) ->
    print ~at_level:1 "handle %t %t"
      (print_expression ~max_level:0 e)
      (print_computation ~max_level:0 c)
  | Typed.Let (lst, c) ->
    print ~at_level:2 "%t" (print_multiple_bind (lst, c))
  | Typed.LetRec (lst, c) ->
    print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Typed.Call (eff, e, a) ->
    let expected_scheme = c.Typed.scheme in
    print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction ~expected_scheme a)
  | Typed.Bind (c1, {Typed.term = (p, c2)}) when Scheme.is_pure c1.Typed.scheme ->
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_computation ~max_level:0 c1)
      (print_computation c2)
  | Typed.Bind (c1, a) ->
    let expected_scheme = c.Typed.scheme in
    print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
      (print_computation ~max_level:0 c1)
      (print_abstraction ~expected_scheme a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
    let expected_scheme = c.Typed.scheme in
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_expression e)
      (print_computation ~expected_scheme c)

and print_handler h ppf =
  Print.print ppf
    "{@[<hov>
      value_clause = (@[fun %t@]);@ 
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with %t) : a -> (b -> _ computation) -> _ computation))
    @]}"
    (print_abstraction h.Typed.value_clause)
    (print_effect_clauses h.Typed.effect_clauses)

and print_effect_clauses eff_clauses ppf =
  let print ?at_level = Print.print ?at_level ppf in
  match eff_clauses with
  | [] ->
    print "| eff' -> fun arg k -> Call (eff', arg, k)"
  | (((_, (t1, t2)) as eff), {Typed.term = (p1, p2, c)}) :: cases ->
    print ~at_level:1
      "| %t -> (fun (%t : %t) (%t : %t -> _ computation) -> %t) %t"
      (print_effect eff)
      (print_pattern p1) (print_type t1)
      (print_pattern p2) (print_type t2)
      (print_computation c)
      (print_effect_clauses cases)

and print_abstraction ?expected_scheme {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation ?expected_scheme c)

and print_multiple_bind (lst, c') ppf =
  match lst with
  | [] -> Format.fprintf ppf "%t" (print_computation c')
  | (p, c) :: lst when Scheme.is_pure c.Typed.scheme ->
      Format.fprintf ppf "let %t = %t in %t"
        (print_pattern p) (print_computation c) (print_multiple_bind (lst, c'))
  | (p, c) :: lst ->
      Format.fprintf ppf "%t >> fun %t -> %t"
        (print_computation c) (print_pattern p) (print_multiple_bind (lst, c'))

and print_top_let_abstraction (p, c) ppf =
  Format.fprintf ppf "%t = %t" (print_pattern p) (print_computation ~max_level:0 c)

and print_let_rec_abstraction (x, a) ppf =
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction a)

(** COMMANDS *)

let print_command (cmd, _) ppf =
  match cmd with
  | Typed.DefEffect (eff, (ty1, ty2)) ->
    Print.print ppf "type (_, _) effect += %t : (%t, %t) effect" (print_effect eff) (print_type ty1) (print_type ty2)
  | Typed.Computation c ->
    print_computation c ppf
  | Typed.TopLet (defs, _) ->
    Print.print ppf "let %t" (Print.sequence "\nand\n" print_top_let_abstraction defs)
  | Typed.TopLetRec (defs, _) ->
    Print.print ppf "let rec %t" (Print.sequence "\nand\n" print_let_rec_abstraction defs)
  | Typed.Use fn ->
    Print.print ppf "#use %S" (compiled_filename fn)
  | Typed.External (x, ty, f) ->
    Print.print ppf "let %t = ( %s )" (print_variable x) f
  | Typed.Tydef tydefs ->
    print_tydefs tydefs ppf
  | Typed.Reset ->
    Print.print ppf "(* #reset directive not supported by OCaml *)"
  | Typed.Quit ->
    Print.print ppf "(* #quit directive not supported by OCaml *)"
  | Typed.TypeOf _ ->
    Print.print ppf "(* #type directive not supported by OCaml *)"
  | Typed.Help ->
    Print.print ppf "(* #help directive not supported by OCaml *)"
