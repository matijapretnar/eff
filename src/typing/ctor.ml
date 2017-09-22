
(********************)
(* HELPER FUNCTIONS *)
(********************)

let backup_location loc locs =
  match loc with
  | None -> Location.union locs
  | Some loc -> loc

(**********************************)
(* ABSTRACTION SMART CONSTRUCTORS *)
(**********************************)

let abstraction ?loc p c : Typed.abstraction =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  {
    term = (p, c);
    scheme = Scheme.abstract ~loc p.scheme c.scheme;
    location = loc;
  }

let abstraction2 ?loc p1 p2 c : Typed.abstraction2 =
  let loc = backup_location loc [p1.Typed.location; p2.Typed.location; c.Typed.location] in
  {
    term = (p1, p2, c);
    scheme = Scheme.abstract2 ~loc p1.scheme p2.scheme c.scheme;
    location = loc;
  }

(*********************************)
(* EXPRESSION SMART CONSTRUCTORS *)
(*********************************)

let var ?loc x sch =
  let loc = backup_location loc [] in
  let term = Typed.Var x in
  Typed.annotate term sch loc

let const ?loc c =
  let loc = backup_location loc [] in
  let term = Typed.Const c in
  let sch = Scheme.const c in
  Typed.annotate term sch loc

let lambda ?loc p c =
  let loc = backup_location loc [p.Typed.location; c.Typed.location] in
  let param_ty = Scheme.get_type p.Typed.scheme in
  let term = Typed.Lambda (p, param_ty, c) in
  let sch = Scheme.lambda ~loc p.Typed.scheme c.Typed.scheme in
  Typed.annotate term sch loc

let tuple ?loc es =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) es) in
  let term = Typed.Tuple es in
  let sch = Scheme.tuple (List.map (fun e -> e.Typed.scheme) es) in
  Typed.annotate term sch loc

let effect ?loc ((eff_name, (ty_par, ty_res)) as eff) =
  let loc = backup_location loc [] in
  let sch = Scheme.effect ty_par ty_res eff_name in
  let term = Typed.Effect eff in
  Typed.annotate term sch loc

(* let handler ?loc value_clause effect_clauses =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) (effect_clauses :: value_clause)) in
  let term = Typed.Handler {
    effect_clauses=effect_clauses;
    value_clause=value_clause
  } in
  (* let sch = Scheme.handler effect_clauses value_clause in *)
  Typed.annotate term sch loc *)


(**********************************)
(* COMPUTATION SMART CONSTRUCTORS *)
(**********************************)

let value ?loc e =
  let loc = backup_location loc [e.Typed.location] in
  let term = Typed.Value e in
  let sch = Scheme.value e.Typed.scheme in
  Typed.annotate term sch loc

let apply ?loc e1 e2 =
  let loc = backup_location loc [e1.Typed.location; e2.Typed.location] in
  let term = Typed.Apply (e1, e2) in
  let sch = Scheme.apply e1.Typed.scheme e2.Typed.scheme in
  Typed.annotate term sch loc

let patmatch ?loc es cases =
  let loc = backup_location loc (List.map (fun e -> e.Typed.location) cases) in
  let term = Typed.Match (es, cases) in
  let sch = Scheme.patmatch es.Typed.scheme (List.map (fun e -> e.Typed.scheme) cases) in
  Typed.annotate term sch loc

(******************************)
(* PATTERN SMART CONSTRUCTORS *)
(******************************)

let pvar ?loc x =
  let loc = backup_location loc [] in
  let sch = Scheme.pvar x in
  let pattern = Typed.PVar x in
  Typed.annotate pattern sch loc

let pnonbinding ?loc =
  let loc = backup_location loc [] in
  let sch = Scheme.pnonbinding () in
  let pat = Typed.PNonbinding in
  Typed.annotate pat sch loc

let pconst ?loc const =
  let loc = backup_location loc [] in
  let sch = Scheme.pconst const in
  let pat = Typed.PConst const in
  Typed.annotate pat sch loc

let pas ?loc p x =
  let loc = backup_location loc [p.Typed.location] in
  let pat = Typed.PAs (p, x) in
  let sch = Scheme.pas p.Typed.scheme x in
  Typed.annotate pat sch loc

let ptuple ?loc ps =
  let loc = backup_location loc (List.map (fun p -> p.Typed.location) ps) in
  let sch = Scheme.ptuple (List.map (fun e -> e.Typed.scheme) ps) in
  let pat = Typed.PTuple ps in
  Typed.annotate pat sch loc
