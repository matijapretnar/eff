%{
  open SugaredSyntax

  type handler_clause =
    | EffectClause of OldUtils.effect * abstraction2
    | ReturnClause of abstraction
    | FinallyClause of abstraction

  let collect_handler_clauses clauses =
    let (eff_cs, val_c, fin_c) =
      List.fold_left
        (fun (eff_cs, val_c, fin_c) -> function
          | (EffectClause (eff, a2), _) ->  ((eff, a2) :: eff_cs, val_c, fin_c)
          | (ReturnClause a, loc) ->
            begin match val_c with
              | None -> (eff_cs, Some a, fin_c)
              | Some _ -> Error.syntax ~loc "Multiple value clauses in a handler."
            end
          | (FinallyClause a, loc) ->
            begin match fin_c with
            | None -> (eff_cs, val_c, Some a)
            | Some _ -> Error.syntax ~loc "Multiple finally clauses in a handler."
            end)
        ([], None, None)
        clauses
    in
    { effect_clauses = List.rev eff_cs;
      value_clause = val_c;
      finally_clause = fin_c }

%}

%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COLON COMMA SEMI SEMISEMI EQUAL CONS
%token BEGIN END
%token <string> LNAME
%token UNDERSCORE AS
%token <int> INT
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token <OldUtils.label> UNAME
%token <OldUtils.typaram> PARAM
%token TYPE ARROW HARROW OF EFFECT
%token EXTERNAL
%token MATCH WITH FUNCTION HASH
%token LET REC AND IN
%token FUN BAR BARBAR
%token IF THEN ELSE
%token HANDLER AT VAL FINALLY HANDLE
%token PLUS STAR MINUS MINUSDOT
%token LSL LSR ASR
%token MOD OR
%token AMPER AMPERAMPER
%token LAND LOR LXOR
%token <string> PREFIXOP INFIXOP0 INFIXOP1 INFIXOP2 INFIXOP3 INFIXOP4
%token CHECK
%token QUIT USE HELP RESET
%token EOF

%nonassoc HANDLE ARROW IN
%right SEMI
%nonassoc ELSE
%right OR BARBAR
%right AMPER AMPERAMPER
%left  INFIXOP0 EQUAL
%right INFIXOP1 AT
%right CONS
%left  INFIXOP2 PLUS MINUS MINUSDOT
%left  INFIXOP3 STAR MOD LAND LOR LXOR
%right INFIXOP4 LSL LSR ASR

%start <SugaredSyntax.command list> commands

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
commands:
  | lst = topdef_list
    { lst }
  | t = topterm EOF
     { [t] }
  | t = topterm SEMISEMI lst = commands
     { t :: lst }
  | dir = topdirective EOF
     { [dir] }
  | dir = topdirective SEMISEMI lst = commands
     { dir :: lst }

topdef_list:
  | EOF
     { [] }
  | def = topdef SEMISEMI lst = commands
     { def :: lst }
  | def = topdef lst = topdef_list
     { def :: lst }

commandline:
  | def = topdef SEMISEMI
    { def }
  | t = topterm SEMISEMI
    { t }
  | dir = topdirective SEMISEMI
    { dir }

topterm: mark_position(plain_topterm) { $1 }
plain_topterm:
  | t = term
    { Term t }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | TYPE defs = separated_nonempty_list(AND, ty_def)
    { Tydef defs }
  | LET defs = separated_nonempty_list(AND, let_def)
    { TopLet defs }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def)
    { TopLetRec defs }
  | EXTERNAL x = ident COLON t = ty EQUAL n = STRING
    { External (x, t, n) }
  | EFFECT eff = effect COLON t1 = prod_ty ARROW t2 = ty
    { DefEffect (eff, (t1, t2))}

(* Toplevel directive If you change these, make sure to update lname as well,
   or a directive might become a reserved word. *)
topdirective: mark_position(plain_topdirective) { $1 }
plain_topdirective:
  | HASH QUIT
    { Quit }
  | HASH HELP
    { Help }
  | HASH RESET
    { Reset }
  | HASH TYPE t = term
    { TypeOf t }
  | HASH USE fn = STRING
    { Use fn }

(* Main syntax tree *)

term: mark_position(plain_term) { $1 }
plain_term:
  | MATCH t = term WITH cases = cases0(match_case) (* END *)
    { Match (t, cases) }
  | FUNCTION cases = cases(match_case) (* END *)
    { Function cases }
  | HANDLER h = handler (* END *)
    { fst h }
  | HANDLE t = term WITH h = handler (* END *)
    { Handle (h, t) }
  | FUN t = lambdas1(ARROW)
    { fst t }
  | LET defs = separated_nonempty_list(AND, let_def) IN t = term
    { Let (defs, t) }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def) IN t = term
    { LetRec (defs, t) }
  | WITH h = term HANDLE t = term
    { Handle (h, t) }
  | t1 = term SEMI t2 = term
    { Let ([(PNonbinding, snd t1), t1], t2) }
  | IF t_cond = comma_term THEN t_true = term ELSE t_false = term
    { Conditional (t_cond, t_true, t_false) }
  | t = plain_comma_term
    { t }

comma_term: mark_position(plain_comma_term) { $1 }
plain_comma_term:
  | t = binop_term COMMA ts = separated_list(COMMA, binop_term)
    { Tuple (t :: ts) }
  | t = plain_binop_term
    { t }

binop_term: mark_position(plain_binop_term) { $1 }
plain_binop_term:
  | t1 = binop_term op = binop t2 = binop_term
    {
      let op_loc = Location.make $startpos(op) $endpos(op) in
      let partial = Apply ((Var op, op_loc), t1) in
      let partial_pos = Location.make $startpos(t1) $endpos(op) in
      Apply ((partial, partial_pos), t2)
    }
  | t1 = binop_term CONS t2 = binop_term
    { Variant (OldUtils.cons, Some (Tuple [t1; t2], Location.make $startpos $endpos)) }
  | t = plain_uminus_term 
    { t }

uminus_term: mark_position(plain_uminus_term) { $1 }
plain_uminus_term:
  | MINUS t = uminus_term
    { let op_loc = Location.make $startpos($1) $endpos($1) in
      Apply ((Var "~-", op_loc), t) }
  | MINUSDOT t = uminus_term
    { let op_loc = Location.make $startpos($1) $endpos($1) in
      Apply ((Var "~-.", op_loc), t) }
  | t = plain_app_term
    { t }

plain_app_term:
  | CHECK t = prefix_term
    { Check t }
  | t = prefix_term ts = prefix_term+
    {
      match fst t, ts with
      | Variant (lbl, None), [t] -> Variant (lbl, Some t)
      | Variant (lbl, _), _ -> Error.syntax ~loc:(snd t) "Label %s applied to too many argument" lbl
      | _, _ ->
        let apply ((_, loc1) as t1) ((_, loc2) as t2) = (Apply(t1, t2), Location.union [loc1; loc2]) in
        fst (List.fold_left apply t ts)
    }
  | t = plain_prefix_term
    { t }

prefix_term: mark_position(plain_prefix_term) { $1 }
plain_prefix_term:
  | op = prefixop t = simple_term
    {
      let op_loc = Location.make $startpos(op) $endpos(op) in
      Apply ((Var op, op_loc), t)
    }
  | t = plain_simple_term
    { t }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | x = ident
    { Var x }
  | lbl = UNAME
    { Variant (lbl, None) }
  | cst = const_term
    { Const cst }
  | HASH eff = effect
    { Effect eff }
  | LBRACK ts = separated_list(SEMI, comma_term) RBRACK
    {
      let nil = (Variant (OldUtils.nil, None), Location.make $endpos $endpos) in
      let cons ((_, loc_t) as t) ((_, loc_ts) as ts) =
        let loc = Location.union [loc_t; loc_ts] in
        (Variant (OldUtils.cons, Some (Tuple [t; ts], loc)), loc) in
      fst (List.fold_right cons ts nil)
    }
  | LBRACE flds = separated_nonempty_list(SEMI, separated_pair(field, EQUAL, comma_term)) RBRACE
    { Record flds }
  | LPAREN RPAREN
    { Tuple [] }
  | LPAREN t = plain_term RPAREN
    { t }
  | BEGIN t = plain_term END
    { t }

(* Auxilliary definitions *)

const_term:
  | n = INT
    { Const.of_integer n }
  | str = STRING
    { Const.of_string str }
  | b = BOOL
    { Const.of_boolean b }
  | f = FLOAT
    { Const.of_float f }

match_case:
  | p = pattern ARROW t = term
    { (p, t) }

lambdas0(SEP):
  | SEP t = term
    { t }
  | p = simple_pattern t = lambdas0(SEP)
    { (Lambda (p, t), Location.make $startpos $endpos) }

lambdas1(SEP):
  | p = simple_pattern t = lambdas0(SEP)
    { (Lambda (p, t), Location.make $startpos $endpos) }

let_def:
  | p = pattern EQUAL t = term
    { (p, t) }
  | x = mark_position(ident) t = lambdas1(EQUAL)
    { ((PVar (fst x), (snd x)), t) }

let_rec_def:
  | f = ident t = lambdas0(EQUAL)
    { (f, t) }

handler_clause: mark_position(plain_handler_clause) { $1 }
plain_handler_clause:
  | HASH eff = effect p = simple_pattern k = simple_pattern ARROW t2 = term
    { EffectClause (eff, (p, k, t2)) }
  | VAL c = match_case
    { ReturnClause c }
  | FINALLY c = match_case
    { FinallyClause c }

pattern: mark_position(plain_pattern) { $1 }
plain_pattern:
  | p = comma_pattern
    { fst p }
  | p = pattern AS x = lname
    { PAs (p, x) }

comma_pattern: mark_position(plain_comma_pattern) { $1 }
plain_comma_pattern:
  | ps = separated_nonempty_list(COMMA, cons_pattern)
    { match ps with [(p, _)] -> p | ps -> PTuple ps }

cons_pattern: mark_position(plain_cons_pattern) { $1 }
plain_cons_pattern:
  | p = variant_pattern
    { fst p }
  | p1 = variant_pattern CONS p2 = cons_pattern
    { PVariant (OldUtils.cons, Some (PTuple [p1; p2], Location.make $startpos $endpos)) }

variant_pattern: mark_position(plain_variant_pattern) { $1 }
plain_variant_pattern:
  | lbl = UNAME p = simple_pattern
    { PVariant (lbl, Some p) }
  | p = simple_pattern
    { fst p }

simple_pattern: mark_position(plain_simple_pattern) { $1 }
plain_simple_pattern:
  | x = ident
    { PVar x }
  | lbl = UNAME
    { PVariant (lbl, None) }
  | UNDERSCORE
    { PNonbinding }
  | cst = const_term
    { PConst cst }
  | LBRACE flds = separated_nonempty_list(SEMI, separated_pair(field, EQUAL, pattern)) RBRACE
    { PRecord flds }
  | LBRACK ts = separated_list(SEMI, pattern) RBRACK
    {
      let nil = (PVariant (OldUtils.nil, None), Location.make $endpos $endpos) in
      let cons ((_, loc_t) as t) ((_, loc_ts) as ts) =
        let loc = Location.union [loc_t; loc_ts] in
        (PVariant (OldUtils.cons, Some (PTuple [t; ts], loc)), loc)
      in
        fst (List.fold_right cons ts nil)
    }
  | LPAREN RPAREN
    { PTuple [] }
  | LPAREN p = pattern RPAREN
    { fst p }

handler: mark_position(plain_handler) { $1 }
plain_handler:
  | cs = cases(handler_clause)
    { Handler (collect_handler_clauses cs) }

lname:
  | x = LNAME
    { x }
  | QUIT
    { "quit" }
  | HELP
    { "help" }
  | USE
    { "use" }
  | RESET
    { "reset" }

field:
  | f = lname
    { f }

tyname:
  | t = lname
    { t }

ident:
  | x = lname
    { x }
  | LPAREN op = binop RPAREN
    { op }
  | LPAREN op = PREFIXOP RPAREN
    { op }

%inline binop:
  | OR
    { "or" }
  | BARBAR
    { "||" }
  | AMPER
    { "&" }
  | AMPERAMPER
    { "&&" }
  | AT
    { "@" }
  | op = INFIXOP0
    { op }
  | op = INFIXOP1
    { op }
  | op = INFIXOP2
    { op }
  | PLUS
    { "+" }
  | MINUSDOT
    { "-." }
  | MINUS
    { "-" }
  | EQUAL
    { "=" }
  | op = INFIXOP3
    { op }
  | STAR
    { "*" }
  | op = INFIXOP4
    { op }
  | MOD
    { "mod" }
  | LAND
    { "land" }
  | LOR
    { "lor" }
  | LXOR
    { "lxor" }
  | LSL
    { "lsl" }
  | LSR
    { "lsr" }
  | ASR
    { "asr" }

%inline prefixop:
  | op = PREFIXOP
    { op }

cases0(case):
  | BAR? cs = separated_list(BAR, case)
    { cs }

cases(case):
  | BAR? cs = separated_nonempty_list(BAR, case)
    { cs }

mark_position(X):
  x = X
  { x, Location.make $startpos $endpos}

params:
  |
    { [] }
  | p = PARAM
    { [p] }
  | LPAREN ps = separated_nonempty_list(COMMA, PARAM) RPAREN
    { ps }

ty_def:
  | ps = params t = tyname EQUAL x = defined_ty
    { (t, (ps, x)) }

defined_ty:
  | LBRACE lst = separated_nonempty_list(SEMI, separated_pair(field, COLON, ty)) RBRACE
    { TyRecord lst }
  | lst = cases(sum_case)
    { TySum lst }
  | t = ty
    { TyInline t }

ty: mark_position(plain_ty) { $1 }
plain_ty:
  | t1 = ty_apply ARROW t2 = ty
    { TyArrow (t1, t2) }
  | t1 = ty_apply HARROW t2 = ty
    { TyHandler (t1, t2) }
  | t = plain_prod_ty
    { t }

prod_ty: mark_position(plain_prod_ty) { $1 }
plain_prod_ty:
  | ts = separated_nonempty_list(STAR, ty_apply)
    {
      match ts with
      | [] -> assert false
      | [t] -> fst t
      | _ -> TyTuple ts
     }

ty_apply: mark_position(plain_ty_apply) { $1 }
plain_ty_apply:
  | LPAREN t = ty COMMA ts = separated_nonempty_list(COMMA, ty) RPAREN t2 = tyname
    { TyApply (t2, (t :: ts)) }
  | t = ty_apply t2 = tyname
    { TyApply (t2, [t]) }
  | t = plain_simple_ty
    { t }

plain_simple_ty:
  | t = tyname
    { TyApply (t, []) }
  | t = PARAM
    { TyParam t }
  | LPAREN t = ty RPAREN
    { fst t }

sum_case:
  | lbl = UNAME
    { (lbl, None) }
  | lbl = UNAME OF t = ty
    { (lbl, Some t) }

effect:
  | eff = UNAME
    { eff }

%%
