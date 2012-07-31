%{
  module C = Common
  module S = Syntax

  type handler_case =
    | OperationCase of S.operation * S.abstraction2
    | ReturnCase of S.abstraction
    | FinallyCase of S.abstraction

  let collect_handler_cases (lst : handler_case list) =
    let (ops, ret, fin) =
      List.fold_left
        (fun (ops, ret, fin) -> function
          | OperationCase (op, a2) ->  ((op, a2) :: ops, ret, fin)
          | ReturnCase a ->
            begin match ret with
            | None -> (ops, Some a, fin)
            | Some _ -> Error.syntax "Multiple value cases in a handler."
            end
          | FinallyCase a ->
            begin match fin with
            | None -> (ops, ret, Some a)
            | Some _ -> Error.syntax "Multiple finally cases in a handler."
            end)
        ([], None, None)
        lst
    in
    { S.operations = List.rev ops;
      S.value = ret;
      S.finally = fin }

%}

%token LPAREN RPAREN LBRACK RBRACK LBRACE RBRACE
%token COLON COMMA SEMI SEMISEMI EQUAL CONS
%token BEGIN END
%token <Common.variable> LNAME
%token UNDERSCORE AS
%token <int> INT
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

%start <Syntax.toplevel list> file
%start <Syntax.toplevel> commandline

%%

(* Toplevel syntax *)

(* If you're going to "optimize" this, please make sure we don't require;; at the
   end of the file. *)
file:
  | lst = file_topdef
    { lst }
  | t = term EOF
     { [S.Term t] }
  | t = term SEMISEMI lst = file
     { (S.Term t) :: lst }
  | dir = topdirective EOF
     { [dir] }
  | dir = topdirective SEMISEMI lst = file
     { dir :: lst }

file_topdef:
  | EOF
     { [] }
  | def = topdef SEMISEMI lst = file
     { (S.Topdef def) :: lst }
  | def = topdef lst = file_topdef
     { (S.Topdef def) :: lst }

commandline:
  | def = topdef SEMISEMI
    { S.Topdef def }
  | t = term SEMISEMI
    { S.Term t }
  | dir = topdirective SEMISEMI
    { dir }

(* Things that can be defined on toplevel. *)
topdef: mark_position(plain_topdef) { $1 }
plain_topdef:
  | TYPE defs = separated_nonempty_list(AND, ty_def)
    { S.Tydef defs }
  | LET defs = separated_nonempty_list(AND, let_def)
    { S.TopLet defs }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def)
    { S.TopLetRec defs }
  | EXTERNAL x = ident COLON t = ty EQUAL n = STRING
    { S.External (x, t, n) }

(* Toplevel directives. If you change these, make sure to update lname as well,
   or a directive might become a reserved word. *)
topdirective:
  | HASH QUIT
    { S.Quit }
  | HASH HELP
    { S.Help }
  | HASH RESET
    { S.Reset }
  | HASH TYPE t = term
    { S.TypeOf t }
  | HASH USE fn = STRING
    { S.Use fn }

(* Main syntax tree *)

term: mark_position(plain_term) { $1 }
plain_term:
  | MATCH t = term WITH cases = cases0(match_case) (* END *)
    { S.Match (t, cases) }
  | FUNCTION cases = cases(match_case) (* END *)
    { S.Function cases }
  | HANDLER h = handler (* END *)
    { fst h }
  | HANDLE t = term WITH h = handler (* END *)
    { S.Handle (h, t) }
  | FUN t = lambdas1(ARROW)
    { fst t }
  | LET defs = separated_nonempty_list(AND, let_def) IN t = term
    { S.Let (defs, t) }
  | LET REC defs = separated_nonempty_list(AND, let_rec_def) IN t = term
    { S.LetRec (defs, t) }
  | WITH h = term HANDLE t = term
    { S.Handle (h, t) }
  | t1 = term SEMI t2 = term
    { S.Let ([(Pattern.Nonbinding, Common.Nowhere), t1], t2) }
  | IF t_cond = comma_term THEN t_true = term ELSE t_false = term
    { S.Conditional (t_cond, t_true, t_false) }
  | WHILE t1 = comma_term DO t2 = term DONE
    { S.While (t1, t2) }
  | FOR i = lname EQUAL x = comma_term TO y = comma_term DO t = term DONE
    { S.For (i, x, y, t, true) }
  | FOR i = lname EQUAL x = comma_term DOWNTO y = comma_term DO t = term DONE
    { S.For (i, x, y, t, false) }
  | t = plain_comma_term
    { t }

comma_term: mark_position(plain_comma_term) { $1 }
plain_comma_term:
  | t = binop_term COMMA ts = separated_list(COMMA, binop_term)
    { S.Tuple (t :: ts) }
  | t = plain_new_term
    { t }

plain_new_term:
  | NEW ty = tyname AT t = simple_term WITH lst = resource_case* END
    { S.New (ty, Some (t, lst)) }
  | NEW ty = tyname
    { S.New (ty, None) }
  | t = plain_binop_term
    { t }

binop_term: mark_position(plain_binop_term) { $1 }
plain_binop_term:
  | t1 = binop_term op = binop t2 = binop_term
    {
      let op_pos = Common.Position ($startpos(op), $endpos(op)) in
      let partial = S.Apply ((S.Var op, op_pos), t1) in
      let partial_pos = Common.Position ($startpos(t1), $endpos(op)) in
      S.Apply ((partial, partial_pos), t2)
    }
  | t1 = binop_term CONS t2 = binop_term
    { S.Variant (Common.cons, Some (S.Tuple [t1; t2], C.Nowhere)) }
  | t = plain_uminus_term 
    { t }

uminus_term: mark_position(plain_uminus_term) { $1 }
plain_uminus_term:
  | MINUS t = uminus_term
    { let op_pos = Common.Position ($startpos($1), $endpos($1)) in
      S.Apply ((S.Var "~-", op_pos), t) }
  | MINUSDOT t = uminus_term
    { let op_pos = Common.Position ($startpos($1), $endpos($1)) in
      S.Apply ((S.Var "~-.", op_pos), t) }
  | t = plain_app_term
    { t }

plain_app_term:
  | CHECK t = prefix_term
    { S.Check t }
  | t = prefix_term ts = prefix_term+
    {
      match fst t, ts with
      | S.Variant (lbl, None), [t] -> S.Variant (lbl, Some t)
      | S.Variant (lbl, _), _ -> Error.syntax ~pos:(snd t) "Label %s applied to too many arguments." lbl
      | _, _ ->
        let apply t1 t2 = (S.Apply(t1, t2), Common.join_pos t1 t2) in
        fst (List.fold_left apply t ts)
    }
  | t = plain_prefix_term
    { t }

prefix_term: mark_position(plain_prefix_term) { $1 }
plain_prefix_term:
  | op = prefixop t = simple_term
    {
      let op_pos = Common.Position ($startpos(op), $endpos(op)) in
      S.Apply ((S.Var op, op_pos), t)
    }
  | t = plain_simple_term
    { t }

simple_term: mark_position(plain_simple_term) { $1 }
plain_simple_term:
  | x = ident
    { S.Var x }
  | lbl = UNAME
    { S.Variant (lbl, None) }
  | cst = const_term
    { S.Const cst }
  | t = simple_term HASH op = ident
    { S.Operation (t, op) }
  | LBRACK ts = separated_list(SEMI, comma_term) RBRACK
    {
      let nil = (S.Variant (Common.nil, None), Common.Position ($endpos, $endpos)) in
      let cons t ts = (S.Variant (Common.cons, Some (S.Tuple [t; ts], C.Nowhere)), Common.join_pos t ts) in
      fst (List.fold_right cons ts nil)
    }
  | LBRACE flds = separated_nonempty_list(SEMI, separated_pair(field, EQUAL, comma_term)) RBRACE
    { S.Record flds }
  | LPAREN RPAREN
    { S.Tuple [] }
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
    { (S.Lambda (p, t), Common.Position ($startpos, $endpos)) }

lambdas1(SEP):
  | p = simple_pattern t = lambdas0(SEP)
    { (S.Lambda (p, t), Common.Position ($startpos, $endpos)) }

let_def:
  | p = pattern EQUAL t = term
    { (p, t) }
  | x = mark_position(ident) t = lambdas1(EQUAL)
    { ((Pattern.Var (fst x), (snd x)), t) }

let_rec_def:
  | f = ident t = lambdas0(EQUAL)
    { (f, t) }

handler_case:
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
    { Pattern.Variant (Common.cons, Some (Pattern.Tuple [p1; p2], Common.Nowhere)) }

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
      let nil = (Pattern.Variant (Common.nil, None), Common.Nowhere) in
      let cons t ts =
        (Pattern.Variant (Common.cons, Some (Pattern.Tuple [t; ts], Common.Nowhere)), Common.Nowhere)
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
    { S.Handler (collect_handler_cases cs) }

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
    { S.TyRecord lst }
  | lst = cases(sum_case)
    { S.TySum lst }
  | EFFECT lst = effect_case* END
    { S.TyEffect lst }
  | t = ty
    { S.TyInline t }

ty:
  | t1 = ty_apply ARROW t2 = ty
    { S.TyArrow (t1, t2) }
  | t1 = ty_apply HARROW t2 = ty
    { S.TyHandler (t1, t2) }
  | t = prod_ty
    { t }

prod_ty:
  | ts = separated_nonempty_list(STAR, ty_apply)
    {
      match ts with
      | [] -> assert false
      | [t] -> t
      | _ -> S.TyTuple ts
     }

ty_apply:
  | LPAREN t = ty COMMA ts = separated_nonempty_list(COMMA, ty) RPAREN t2 = tyname
    { S.TyApply (t2, (t :: ts)) }
  | t = ty_apply t2 = tyname
    { S.TyApply (t2, [t]) }
  | t = simple_ty
    { t }

simple_ty:
  | t = tyname
    { S.TyApply (t, []) }
  | t = PARAM
    { S.TyParam t }
  | LPAREN t = ty RPAREN
    { t }

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
