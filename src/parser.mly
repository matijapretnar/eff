%{
  open SyntaxSugared

  type handler_case =
    | OperationCase of operation * abstraction2
    | ReturnCase of abstraction
    | FinallyCase of abstraction

  let collect_handler_cases (lst : (handler_case * Common.position) list) =
    let (ops, ret, fin) =
      List.fold_left
        (fun (ops, ret, fin) -> function
          | (OperationCase (op, a2), _) ->  ((op, a2) :: ops, ret, fin)
          | (ReturnCase a, pos) ->
            begin match ret with
              | None -> (ops, Some a, fin)
              | Some _ -> Error.syntax ~pos "Multiple value cases in a handler."
            end
          | (FinallyCase a, pos) ->
            begin match fin with
            | None -> (ops, ret, Some a)
            | Some _ -> Error.syntax ~pos "Multiple finally cases in a handler."
            end)
        ([], None, None)
        lst
    in
    { operations = List.rev ops;
      value = ret;
      finally = fin }

%}

%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COLON COMMA SEMI SEMISEMI EQUAL CONS
%token BEGIN END
%token <Common.variable> LNAME
%token UNDERSCORE AS
%token <Big_int.big_int> INT
%token <string> STRING
%token <bool> BOOL
%token <float> FLOAT
%token <Common.label> UNAME
%token <Common.typaram> PARAM
%token TYPE ARROW HARROW OF EFFECT
%token EXTERNAL
%token MATCH WITH FUNCTION HASH
%token LET REC AND IN
%token FUN BAR BARBAR
%token IF THEN ELSE
%token WHILE DO DONE FOR TO DOWNTO
%token HANDLER NEW AT OPERATION VAL FINALLY HANDLE
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

%start <SyntaxSugared.toplevel list> file
%start <SyntaxSugared.toplevel> commandline

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
file:
  | lst = file_topdef
    { lst }
  | t = topterm EOF
     { [t] }
  | t = topterm SEMISEMI lst = file
     { t :: lst }
  | dir = topdirective EOF
     { [dir] }
  | dir = topdirective SEMISEMI lst = file
     { dir :: lst }

file_topdef:
  | EOF
     { [] }
  | def = topdef SEMISEMI lst = file
     { def :: lst }
  | def = topdef lst = file_topdef
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
    { Let ([(Pattern.Nonbinding, snd t1), t1], t2) }
  | IF t_cond = comma_term THEN t_true = term ELSE t_false = term
    { Conditional (t_cond, t_true, t_false) }
  | WHILE t1 = comma_term DO t2 = term DONE
    { While (t1, t2) }
  | FOR i = lname EQUAL x = comma_term TO y = comma_term DO t = term DONE
    { For (i, x, y, t, true) }
  | FOR i = lname EQUAL x = comma_term DOWNTO y = comma_term DO t = term DONE
    { For (i, x, y, t, false) }
  | t = plain_comma_term
    { t }

comma_term: mark_position(plain_comma_term) { $1 }
plain_comma_term:
  | t = binop_term COMMA ts = separated_list(COMMA, binop_term)
    { Tuple (t :: ts) }
  | t = plain_new_term
    { t }

plain_new_term:
  | NEW ty = tyname AT t = simple_term WITH lst = resource_case* END
    { New (ty, Some (t, lst)) }
  | NEW ty = tyname
    { New (ty, None) }
  | t = plain_binop_term
    { t }

binop_term: mark_position(plain_binop_term) { $1 }
plain_binop_term:
  | t1 = binop_term op = binop t2 = binop_term
    {
      let op_pos = Common.Position ($startpos(op), $endpos(op)) in
      let partial = Apply ((Var op, op_pos), t1) in
      let partial_pos = Common.Position ($startpos(t1), $endpos(op)) in
      Apply ((partial, partial_pos), t2)
    }
  | t1 = binop_term CONS t2 = binop_term
    { Variant (Common.cons, Some (Tuple [t1; t2], Common.Position ($startpos, $endpos))) }
  | t = plain_uminus_term 
    { t }

uminus_term: mark_position(plain_uminus_term) { $1 }
plain_uminus_term:
  | MINUS t = uminus_term
    { let op_pos = Common.Position ($startpos($1), $endpos($1)) in
      Apply ((Var "~-", op_pos), t) }
  | MINUSDOT t = uminus_term
    { let op_pos = Common.Position ($startpos($1), $endpos($1)) in
      Apply ((Var "~-.", op_pos), t) }
  | t = plain_app_term
    { t }

plain_app_term:
  | CHECK t = prefix_term
    { Check t }
  | t = prefix_term ts = prefix_term+
    {
      match fst t, ts with
      | Variant (lbl, None), [t] -> Variant (lbl, Some t)
      | Variant (lbl, _), _ -> Error.syntax ~pos:(snd t) "Label %s applied to too many argument" lbl
      | _, _ ->
        let apply ((_, pos1) as t1) ((_, pos2) as t2) = (Apply(t1, t2), Common.join_pos pos1 pos2) in
        fst (List.fold_left apply t ts)
    }
  | t = plain_prefix_term
    { t }

prefix_term: mark_position(plain_prefix_term) { $1 }
plain_prefix_term:
  | op = prefixop t = simple_term
    {
      let op_pos = Common.Position ($startpos(op), $endpos(op)) in
      Apply ((Var op, op_pos), t)
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
  | t = simple_term HASH op = ident
    { Operation (t, op) }
  | LBRACK ts = separated_list(SEMI, comma_term) RBRACK
    {
      let nil = (Variant (Common.nil, None), Common.Position ($endpos, $endpos)) in
      let cons ((_, post) as t) ((_, posts) as ts) =
        let pos = Common.join_pos post posts in
        (Variant (Common.cons, Some (Tuple [t; ts], pos)), pos) in
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
    { Common.Integer n }
  | str = STRING
    { Common.String str }
  | b = BOOL
    { Common.Boolean b }
  | f = FLOAT
    { Common.Float f }

match_case:
  | p = pattern ARROW t = term
    { (p, t) }

lambdas0(SEP):
  | SEP t = term
    { t }
  | p = simple_pattern t = lambdas0(SEP)
    { (Lambda (p, t), Common.Position ($startpos, $endpos)) }

lambdas1(SEP):
  | p = simple_pattern t = lambdas0(SEP)
    { (Lambda (p, t), Common.Position ($startpos, $endpos)) }

let_def:
  | p = pattern EQUAL t = term
    { (p, t) }
  | x = mark_position(ident) t = lambdas1(EQUAL)
    { ((Pattern.Var (fst x), (snd x)), t) }

let_rec_def:
  | f = ident t = lambdas0(EQUAL)
    { (f, t) }

handler_case: mark_position(plain_handler_case) { $1 }
plain_handler_case:
  | t1 = simple_term HASH op = ident p = simple_pattern k = simple_pattern ARROW t2 = term
    { OperationCase ((t1, op), (p, k, t2)) }
  | VAL c = match_case
    { ReturnCase c }
  | FINALLY c = match_case
    { FinallyCase c }

pattern: mark_position(plain_pattern) { $1 }
plain_pattern:
  | p = comma_pattern
    { fst p }
  | p = pattern AS x = lname
    { Pattern.As (p, x) }

comma_pattern: mark_position(plain_comma_pattern) { $1 }
plain_comma_pattern:
  | ps = separated_nonempty_list(COMMA, cons_pattern)
    { match ps with [(p, _)] -> p | ps -> Pattern.Tuple ps }

cons_pattern: mark_position(plain_cons_pattern) { $1 }
plain_cons_pattern:
  | p = variant_pattern
    { fst p }
  | p1 = variant_pattern CONS p2 = cons_pattern
    { Pattern.Variant (Common.cons, Some (Pattern.Tuple [p1; p2], Common.Position ($startpos, $endpos))) }

variant_pattern: mark_position(plain_variant_pattern) { $1 }
plain_variant_pattern:
  | lbl = UNAME p = simple_pattern
    { Pattern.Variant (lbl, Some p) }
  | p = simple_pattern
    { fst p }

simple_pattern: mark_position(plain_simple_pattern) { $1 }
plain_simple_pattern:
  | x = ident
    { Pattern.Var x }
  | lbl = UNAME
    { Pattern.Variant (lbl, None) }
  | UNDERSCORE
    { Pattern.Nonbinding }
  | cst = const_term
    { Pattern.Const cst }
  | LBRACE flds = separated_nonempty_list(SEMI, separated_pair(field, EQUAL, pattern)) RBRACE
    { Pattern.Record flds }
  | LBRACK ts = separated_list(SEMI, pattern) RBRACK
    {
      let nil = (Pattern.Variant (Common.nil, None), Common.Position ($endpos, $endpos)) in
      let cons ((_, post) as t) ((_, posts) as ts) =
        let pos = Common.join_pos post posts in
        (Pattern.Variant (Common.cons, Some (Pattern.Tuple [t; ts], pos)), pos)
      in
        fst (List.fold_right cons ts nil)
    }
  | LPAREN RPAREN
    { Pattern.Tuple [] }
  | LPAREN p = pattern RPAREN
    { fst p }

handler: mark_position(plain_handler) { $1 }
plain_handler:
  | cs = cases(handler_case)
    { Handler (collect_handler_cases cs) }

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
  { x, Common.Position ($startpos, $endpos)}

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
  | EFFECT lst = effect_case* END
    { TyEffect lst }
  | t = ty
    { TyInline t }

ty: mark_position(plain_ty) { $1 }
plain_ty:
  | t1 = ty_apply ARROW t2 = ty
    { TyArrow (t1, t2, None) }
  | t1 = ty_apply HARROW t2 = ty
    { TyHandler (t1, None, t2, None) }
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
    { TyApply (t2, (t :: ts), None, None) }
  | t = ty_apply t2 = tyname
    { TyApply (t2, [t], None, None) }
  | t = plain_simple_ty
    { t }

plain_simple_ty:
  | t = tyname
    { TyApply (t, [], None, None) }
  | t = PARAM
    { TyParam t }
  | LPAREN t = ty RPAREN
    { fst t }

sum_case:
  | lbl = UNAME
    { (lbl, None) }
  | lbl = UNAME OF t = ty
    { (lbl, Some t) }

effect_case:
   | OPERATION opsym = lname COLON t1 = prod_ty ARROW t2 = ty
     { (opsym, (t1, t2)) }

resource_case:
   | OPERATION opsym = lname p1 = simple_pattern AT p2 = simple_pattern ARROW t = term
     { (opsym, (p1, p2, t)) }

%%
