open CommonPrint

type ty_shape =
  | Basic
  | Arrow of ty_shape * dirty_shape
  | Handler of dirty_shape * dirty_shape
  | Tuple of ty_shape list
and dirty_shape =
  | ValueS of ty_shape
  | Computation of ty_shape

let rec print_ty_shape ?(max_level=1000) shape ppf =
  let print ?at_level = Print.print ~max_level ?at_level ppf in
  match shape with
  | Basic ->
    print "X"
  | Tuple shapes ->
    print ~at_level:2 "@[<hov>(%t)@]"
      (Print.sequence ", " (print_ty_shape ~max_level:1) shapes)
  | Arrow (shape1, shape2) ->
    print ~at_level:5 "@[%t -> %t@]"
      (print_ty_shape ~max_level:4 shape1)
      (print_dirty_shape ~max_level:5 shape2)
  | Handler (shape1, shape2) ->
    print ~at_level:6 "@[%t => %t@]"
      (print_dirty_shape ~max_level:4 shape1)
      (print_dirty_shape ~max_level:5 shape2)
and print_dirty_shape ?(max_level=1000) shape ppf =
  let print ?at_level = Print.print ~max_level ?at_level ppf in
  match shape with
  | ValueS shape ->
    print_ty_shape ~max_level shape ppf
  | Computation shape ->
    print ~at_level:3 "@[%t computation@]"
      (print_ty_shape ~max_level:3 shape)

let rec shape_of_ty st = function
  | Type.Param _ -> Basic
  | Type.Apply (ty_name, args) when Tctx.transparent ~loc:Location.unknown ty_name ->
    begin match Tctx.ty_apply ~loc:Location.unknown ty_name args with
    | Tctx.Inline ty' -> shape_of_ty st ty'
    | _ -> assert false
    end
  | Type.Apply _ -> Basic
  | Type.Basic _ -> Basic
  | Type.Arrow (ty, dirty) -> Arrow (shape_of_ty st ty, shape_of_dirty st dirty)
  | Type.Tuple tys -> Tuple (List.map (shape_of_ty st) tys)
  | Type.Handler (dirty1, dirty2) -> Handler (shape_of_dirty st dirty1, shape_of_dirty st dirty2)
  | ty -> Print.debug "Don't know the shape of %t" (Type.print_ty ty); assert false
and shape_of_dirty ((ctx, constraints) as st) (ty, drt) =
  if Scheme.is_surely_pure (ctx, (ty, drt), constraints) then
    ValueS (shape_of_ty st ty)
  else
    Computation (shape_of_ty st ty)

let shape_of_ty_scheme (ctx, ty, constraints) =
  let shp = shape_of_ty (ctx, constraints) ty in
  (* Print.debug "Shape of %t is %t" (Scheme.print_ty_scheme (ctx, ty, constraints)) (print_ty_shape ~max_level:1000 shp); *)
  shp
let shape_of_dirty_scheme (ctx, dirty, constraints) =
  let shp = shape_of_dirty (ctx, constraints) dirty in
  (* Print.debug "Shape of %t is %t" (Scheme.print_dirty_scheme (ctx, dirty, constraints)) (print_dirty_shape ~max_level:1000 shp); *)
  shp

type ty_conversion =
  | TyIdentity
  | Lift of ty_conversion * dirty_conversion
  | LiftHandler of dirty_conversion * dirty_conversion
  | Tuple of ty_conversion list
and dirty_conversion =
  | DirtyIdentity
  | Value of ty_conversion
  | Run of ty_conversion
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
  | Run conv -> Run (simplify_ty_conversion conv)
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
  | Basic, Basic -> TyIdentity
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
  | shape1, shape2 ->
      Error.runtime "%t ~~> %t" (print_ty_shape shape1) (print_ty_shape shape2)

and dirty_shape_conversion = function
  | ValueS shape, ValueS shape' ->
      ConvertValues (ty_shape_conversion (shape, shape'))
  | ValueS shape, Computation shape' ->
      Value (ty_shape_conversion (shape, shape'))
  | Computation shape, Computation shape' ->
      ConvertComps (ty_shape_conversion (shape, shape'))
  | Computation shape, ValueS shape' ->
      Run (ty_shape_conversion (shape, shape'))

let rec print_ty_conversion ?(max_level=100000) conv term ppf =
  let print ?at_level = Print.print ~max_level ?at_level ppf in
  match conv with
  | TyIdentity ->
      (term max_level) ppf
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
      let x = Typed.Variable.fresh "x" in
          print ~at_level:2 "(* both *)fun %t -> %t"
                (print_variable x)
                (print_dirty_conversion conv2
                (fun m ppf -> Print.print ~max_level:m ppf "%t %t"
                  (term 1)
                  (print_dirty_conversion ~max_level:0 conv1 (fun _ -> print_variable x))
                )
              )
  | Tuple convs ->
      let xs = List.mapi (fun i conv -> (Typed.Variable.fresh ("x" ^ string_of_int i), conv)) convs in
      print ~at_level:2 "let (%t) = %t in (%t)"
        (Print.sequence ", " print_variable (List.map fst xs))
        (term 100000000)
        (Print.sequence ", " (fun (x, conv) -> print_ty_conversion conv (fun _ -> print_variable x)) xs)
and print_dirty_conversion ?(max_level=1000) conv term ppf =
  let print ?at_level = Print.print ~max_level ?at_level ppf in
  match conv with
  | DirtyIdentity ->
      term max_level ppf
  | ConvertValues conv ->
      print_ty_conversion ~max_level conv term ppf
  | ConvertComps conv ->
      print ~at_level:1 "lift (%t)"
      (print_ty_conversion ~max_level:0 conv term)
  | Value conv ->
      print ~at_level:1 "value (%t)"
      (print_ty_conversion ~max_level:0 conv term)
  | Run conv ->
      print ~at_level:1 "run (%t)"
      (print_ty_conversion ~max_level:0 conv term)

let ty_scheme_conversion shp1 shp2 =
  match shp2 with
  | None ->
      Print.debug "There is no expected shape";
      TyIdentity
  | Some shp2 ->
      Print.debug "Expected shape is %t" (print_ty_shape shp2);
      simplify_ty_conversion (ty_shape_conversion (shp1, shp2))
and dirty_scheme_conversion shp1 shp2 =
  match shp2 with
  | None ->
      Print.debug "There is no expected shape";
      DirtyIdentity
  | Some shp2 ->
      Print.debug "Expected shape is %t" (print_dirty_shape shp2);
      simplify_dirty_conversion (dirty_shape_conversion (shp1, shp2))

let rec print_expression ?max_level ?expected_shape e ppf=
  let shp = shape_of_ty_scheme e.Typed.scheme in
  Print.debug ~loc:e.Typed.location "Printing expression %t@. Type is %t@. Shape is %t"
    (Typed.print_expression e)
    (Scheme.print_ty_scheme e.Typed.scheme)
    (print_ty_shape shp);
  let conv = ty_scheme_conversion shp expected_shape in
  print_converted_expression ?max_level ppf (conv, e)

and print_converted_expression ?max_level ppf = function
  | Tuple convs, {term = Typed.Tuple lst} ->
      Print.print ?max_level ppf "(%t)"
        (Print.sequence ", " (fun (conv, e) ppf -> print_converted_expression ppf (conv, e)) (List.combine convs lst))
  | conv, e ->
      print_ty_conversion ?max_level conv (fun m -> print_expression' ~max_level:m e) ppf


and print_expression' ?max_level e ppf =
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
    let Arrow (_, expected_shape) = shape_of_ty_scheme e.Typed.scheme in
    print ~at_level:2 "fun %t" (print_abstraction ~expected_shape a)
  | Typed.Handler h ->
    let (Handler (_, expected_shape)) = shape_of_ty_scheme e.Typed.scheme in
    print "%t" (print_handler ~expected_shape h)
  | Typed.Effect eff ->
    print ~at_level:2 "effect %t" (print_effect eff)
  | Typed.Pure c ->
    print_computation ?max_level c ppf

and print_computation ?max_level ?expected_shape c ppf =
  let shp = shape_of_dirty_scheme c.Typed.scheme in
  Print.debug ~loc:c.Typed.location "Printing computation %t@. Type is %t@. Shape is %t"
    (Typed.print_computation c)
    (Scheme.print_dirty_scheme c.Typed.scheme)
    (print_dirty_shape shp);
  let conv = dirty_scheme_conversion shp expected_shape in
  print_converted_computation ?max_level ppf (conv, c)

and print_converted_computation ?max_level ppf = function
  | conv, c ->
      print_dirty_conversion ?max_level conv (fun m -> print_computation' ~max_level:m c) ppf

and print_computation' ?max_level c ppf =
  (* Print.debug "printing %t : %t" (Typed.print_computation c) (Scheme.print_dirty_scheme c.Typed.scheme); *)
  let print ?at_level = Print.print ?max_level ?at_level ppf in
  match c.Typed.term with
  | Typed.Apply (e1, e2) ->
    let shp_c = shape_of_dirty_scheme c.Typed.scheme in
    let (Arrow (shp1, _)) = shape_of_ty_scheme e1.Typed.scheme in
    print ~at_level:1 "%t@ %t"
      (print_expression ~max_level:1 ~expected_shape:(Arrow (shp1, shp_c)) e1)
      (print_expression ~max_level:0 ~expected_shape:shp1 e2)
  | Typed.Value e ->
    let (ValueS expected_shape) = shape_of_dirty_scheme c.Typed.scheme in
    print ~at_level:1 "%t" (print_expression ~max_level:0 ~expected_shape e)
  | Typed.Match (e, []) ->
    print ~at_level:2 "(match %t with _ -> assert false)"
      (print_expression e)
  | Typed.Match (e, lst) ->
    let expected_shape = shape_of_dirty_scheme c.Typed.scheme in
    print ~at_level:2 "(match %t with @[<v>| %t@])"
      (print_expression e)
      (Print.cases (print_abstraction ~expected_shape) lst)
  | Typed.Handle (e, c) ->
    print ~at_level:1 "handler %t %t"
      (print_expression ~max_level:0 e)
      (print_computation ~max_level:0 c)
  | Typed.Let (lst, c) ->
    print ~at_level:2 "%t" (print_multiple_bind (lst, c))
  | Typed.LetRec (lst, c) ->
    print ~at_level:2 "let rec @[<hov>%t@] in %t"
      (Print.sequence " and " print_let_rec_abstraction lst) (print_computation c)
  | Typed.Call (eff, e, a) ->
    let expected_shape = shape_of_dirty_scheme c.Typed.scheme in
    print ~at_level:1 "call %t %t (@[fun %t@])"
      (print_effect eff) (print_expression ~max_level:0 e) (print_abstraction ~expected_shape a)
  | Typed.Bind (c1, {Typed.term = (p, c2)}) when Scheme.is_pure c1.Typed.scheme ->
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_computation ~max_level:0 c1)
      (print_computation c2)
  | Typed.Bind (c1, a) ->
    let expected_shape = shape_of_dirty_scheme c.Typed.scheme in
    print ~at_level:2 "@[<hov>%t@ >>@ @[fun %t@]@]"
      (print_computation ~max_level:0 c1)
      (print_abstraction ~expected_shape a)
  | Typed.LetIn (e, {Typed.term = (p, c)}) ->
    let expected_shape = shape_of_dirty_scheme c.Typed.scheme in
    print ~at_level:2 "let @[<hov>%t =@ %t@ in@]@ %t"
      (print_pattern p)
      (print_expression e)
      (print_computation ~expected_shape c)

and print_handler h ~expected_shape ppf =
  (* Print.debug "Printing handler of expected shape %t" (print_dirty_shape expected_shape); *)
  Print.print ppf
    "{@[<hov>
      value_clause = (@[fun %t@]);@ 
      effect_clauses = (fun (type a) (type b) (x : (a, b) effect) ->
        ((match x with %t) : a -> (b -> _ computation) -> _ computation))
    @]}"
    (print_abstraction ~expected_shape h.Typed.value_clause)
    (print_effect_clauses ~expected_shape h.Typed.effect_clauses)

and print_effect_clauses ~expected_shape eff_clauses ppf =
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
      (print_computation ~expected_shape c)
      (print_effect_clauses ~expected_shape cases)

and print_abstraction ~expected_shape {Typed.term = (p, c)} ppf =
  Format.fprintf ppf "%t ->@;<1 2> %t" (print_pattern p) (print_computation ~expected_shape c)

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
  let {Typed.term = (_, {Typed.scheme = sch})} = a in
  let expected_shape = shape_of_dirty_scheme sch in
  Format.fprintf ppf "%t = fun %t" (print_variable x) (print_abstraction ~expected_shape a)

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
