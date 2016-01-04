open PPrint

let (^+^) x y = x ^^ space ^^ y

let rec prettyE e =
  prettyE' e.Typed.term
and prettyE' e = match e with
  | Typed.Var x 
  -> pretty_var x
  | Typed.Const c 
  -> pretty_const c
  | Typed.Lambda a 
  -> parens (string "fun" ^+^ pretty_abstraction a)
  | Typed.PureLambda a 
  -> parens (string "fun" ^+^ pretty_pure_abstraction a)
  | Typed.Effect eff 
  -> parens (string "fun x -> apply_effect" ^+^ pretty_effect eff ^+^ string "x" ^+^ string "(fun y -> value y)")
  | Typed.Handler h 
  -> pretty_handler h
  | Typed.PureApply (e1,e2)
  -> parens (prettyE e1 ^+^ prettyE e2)
  | Typed.PureLetIn (e,pa) ->
      let (p, e2) = pa.Typed.term in
      group (string "let**" ^+^ pretty_pattern p.Typed.term ^+^ string "=" ^+^ prettyE e ^^ break 1 ^^ 
                         string "in" ^+^ prettyE e2)
and prettyC c = 
   prettyC' c.Typed.term
and prettyC' c = match c with
   | Typed.Value e -> string "value" ^+^ parens (prettyE e)
   | Typed.LetIn (e,a) ->
      let (p, c2) = a.Typed.term in
      group (string "let*" ^+^ pretty_pattern p.Typed.term ^+^ string "=" ^+^ prettyE e ^^ break 1 ^^ 
                         string "in" ^+^ prettyC c2)
   | Typed.Bind (c1,a) ->
      let (p, c2) = a.Typed.term in
      parens (prettyC c1) ^+^ string ">>" ^+^ parens (string "fun" ^+^ pretty_pattern p.Typed.term ^+^ string "->" ^+^ prettyC c2)
(*   | Typed.Conditional (e,c1,c2) 
                   -> group (string "if" ^+^ parens (prettyE e) ^^ break 1 ^^
                               nest 2 (string "then" ^+^ parens (prettyC c1) ^^ break 1 ^^
                                       string "else" ^+^ parens (prettyC c2))) *)
  | Typed.Apply (e1, e2) -> parens (prettyE e1 ^+^ prettyE e2)
  | Typed.Handle (e, c)  -> 
    prefix 2 1 (prefix 2 1 (string "handle") (parens (prettyE e))) (parens (prettyC c))
(*   | Typed.Call (eff,e1,e2) 
  -> string "apply_effect*" ^+^ pretty_effect eff ^+^ prettyE e1 ^+^ pretty_abstraction e2 *)
  | Typed.LetRec _ -> failwith "Not implemented"
  (* | Typed.LetEffectIn (eff, c) -> group (string "let effect" ^+^ pretty_effect eff ^+^ string "in" ^+^ prettyC c) *)

and pretty_var x = string (Common.to_string (Typed.Variable.print) x)

and pretty_const c = string (Common.to_string (Const.print) c)

and pretty_abstraction a =
  let (p, c) = a.Typed.term in
  pretty_pattern p.Typed.term ^+^ string "->" ^+^ prettyC c

and pretty_pure_abstraction a =
  let (p, e) = a.Typed.term in
  pretty_pattern p.Typed.term ^+^ string "->*" ^+^ prettyE e

and pretty_pattern p = match fst p with
  | Pattern.Var x -> pretty_var x
  (* Catch all case *)
  | _ -> string (Common.to_string Untyped.print_pattern p)

and pretty_h_effs cases  =  pretty_h_effs_aux cases
and pretty_h_effs_aux cases =
  match cases with
  | [] -> string "Nil"
  | (eff, a2) :: cases ->
    let (p, k, c) = a2.Typed.term in
    string "Cons" ^+^ 
       parens ( dquotes (string eff) ^^ comma ^+^ parens (string "fun" ^+^ pretty_pattern p.Typed.term ^+^ pretty_pattern k.Typed.term ^+^ string "->" ^+^ prettyC c) ^^ comma ^+^ pretty_h_effs_aux cases)

and pretty_effect eff = dquotes (string eff)

and pretty_handler h =
 braces (space ^^ prefix 3 1 (string "value = " ^^ parens (string "fun" ^+^ pretty_abstraction h.value_clause) ^^ semi) 
                             (string "effect_cases = " ^^ pretty_h_effs h.effect_clauses))      

let printE et chan =
   let document = prettyE et ^^ hardline in
   ToChannel.pretty 1. 60 chan document

let printC ct chan =
   let document = prettyC ct ^^ hardline in
   ToChannel.pretty 1. 60 chan document
