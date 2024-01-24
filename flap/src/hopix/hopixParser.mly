%{ (* -*- tuareg -*- *)

  open HopixAST
  open Position


%}

%token<string> VAR_ID
%token<string> CONSTR_ID
%token<string> LABEL_ID
%token<string> TYPE_CON
%token<string> TYPE_VAR
%token<string> INT
%token<char> CHAR
%token<string> STRING
%token<string> COMMON_ID
%token LET FUN AND REF IF THEN ELSE FOR WHILE DO UNTIL FROM TO EXTERN MATCH
%token PO PF
%token CO CF
%token AO AF
%token LANGLE RANGLE
%token COMMA
%token ARROW
%token PIPE MARK SEMICOLON
%token EQUAL
%token DEQUAL
%token PLUS MINUS
%token STAR SLASH
%token ANTISLASH
%token LOR LAND LOE INFT HOE SUPT EQ
%token COLON
%token POINT
%token ECOM
%token TYPE
%token WILDCARD
%token DASH
%token EOF


%start<HopixAST.t> program

%left PLUS MINUS
%left STAR SLASH
%right ARROW
%nonassoc EQ
%left LOR LAND
%nonassoc LOE HOE INFT SUPT

%%

program: l = list(located(definition)) EOF { l }

definition:
| TYPE tc = located(TYPE_CON) tvl = tvarlist td = tdefinition
{
  let pos = Position.position tc in
  let value = Position.value tc in
  let tcon = TCon value in

  DefineType (Position.with_pos pos tcon, tvl, td)
}
| TYPE tc = located(TYPE_CON) tvl = tvarlist
{
  let pos = Position.position tc in
  let value = Position.value tc in
  let tcon = TCon value in

  DefineType (Position.with_pos pos tcon, tvl, Abstract)
}
| EXTERN cid = located(COMMON_ID) COLON ts = located(type_scheme)
{
  let pos = Position.position cid in
  let value = Position.value cid in
  let id = Id value in

  DeclareExtern (Position.with_pos pos id, ts)
}
| vd = vdefinition
{
  DefineValue vd
}
| error
{
  let pos = Position.lex_join $startpos $endpos in

  Error.error "parsing" pos "Syntax error."
}

tvarlist:
| LANGLE tv = located(TYPE_VAR) tvl = tvarlistalt RANGLE
{
  let pos = Position.position tv in
  let value = Position.value tv in
  let id = TId value in

  (Position.with_pos pos id) :: tvl
}
| { [] }

tvarlistalt:
| COMMA tv = located(TYPE_VAR) tvl = tvarlistalt
{
  let pos = Position.position tv in
  let value = Position.value tv in
  let id = TId value in

  (Position.with_pos pos id) :: tvl
}
| { [] }

tdefinition:
| PIPE? cl = constr_list
{
  DefineSumType (cl)
}

| AO ld = labeldef l = label_list AF
{
  DefineRecordType (ld :: l)
}

constr_list:
| ci = located(CONSTR_ID) tl = opt_type_list
{
  let pos = Position.position ci in
  let value = Position.value ci in
  let id = KId value in

  [(Position.with_pos pos id, tl)]
}
| ci = located(CONSTR_ID) tl = opt_type_list PIPE l = constr_list
{
  let pos = Position.position ci in
  let value = Position.value ci in
  let id = KId value in

  (Position.with_pos pos id, tl) :: l
}

opt_type_list:
| PO l = separated_nonempty_list(COMMA, located(datatype)) PF
{
  l
}
| { [] }

label_list:
| COMMA ld = labeldef l = label_list
{
  ld :: l
}
| { [] }

labeldef:
| cid = located(COMMON_ID) COLON dt = located(datatype)
{
  let pos = Position.position cid in
  let value = Position.value cid in
  let id = LId value in
  (Position.with_pos pos id, dt)
}

vdefinition:
| LET cid = located(COMMON_ID) COLON ts = located(type_scheme) EQUAL e = located(expr)
{
  let pos = Position.position cid in
  let value = Position.value cid in
  let id = Id value in
  SimpleValue (Position.with_pos pos id, Some ts, e)
}
| LET cid = located(COMMON_ID) EQUAL e = located(expr)
{
  let pos = Position.position cid in
  let value = Position.value cid in
  let id = Id value in
  SimpleValue (Position.with_pos pos id, None, e)
}
| FUN fd = fundef fdl = fundef_list
{
  RecFunctions (fd :: fdl)
}

fundef_list:
| AND fd = fundef fdl = fundef_list
{
  fd :: fdl
}
| { [] }

fundef:
| cid = located(COMMON_ID) p = located(pattern) EQUAL e = located(expr)
{
  let pos = Position.position cid in
  let value = Position.value cid in
  let id = Id value in
  let fd = FunctionDefinition (p, e) in

  (Position.with_pos pos id, None, fd)
}
| COLON ts = located(type_scheme) cid = located(COMMON_ID) p = located(pattern) EQUAL e = located(expr)
{
  let pos = Position.position cid in
  let value = Position.value cid in
  let id = Id value in
  let fd = FunctionDefinition (p, e) in

  (Position.with_pos pos id, Some ts, fd)
}

datatype:
| at = located(atomic_type) ARROW dt = located(datatype)
{
  TyArrow (at, dt)
}
| tt = tuple_type
{
  tt
}

tuple_type:
| at = located(atomic_type) STAR at2 = located(atomic_type) tl = tuple_list
{
  TyTuple (at :: at2 :: tl)
}
| at = atomic_type
{
  at
}

tuple_list:
| STAR at = located(atomic_type) tl = tuple_list
{
  at :: tl
}
| { [] }

atomic_type:
| tc = type_con LANGLE l = separated_nonempty_list(COMMA, located(datatype)) RANGLE
{
  TyCon (tc, l)
}
| tc = type_con
{
  TyCon (tc, [])
}
| tv = type_variable
{
  TyVar tv
}
| PO dt = datatype PF
{
  dt
}

type_con:
| cid = COMMON_ID
{
  TCon cid
}

type_variable:
| tv = TYPE_VAR
{
  TId tv
}

type_scheme:
| tsa = type_schemealt dt = located(datatype)
{
  ForallTy (tsa, dt)
}

type_schemealt:
| CO l = nonempty_list(located(type_variable)) CF
{
  l
}
| { [] }

expr:
| e = expr_app{ e }
| e = expr_seq { e }
| vdef = vdefinition SEMICOLON e = located(expr_app) { Define(vdef, e) }

expr_app:
| e = expr_atom { e }
| PO e = expr_with_par PF { e }
| exp1 = located(expr_app) b = located(binop) exp2 = located(expr_app) { let exp3 = Apply(b, exp1) in Apply((Position.unknown_pos exp3), exp2) }
| e = located(expr_app) POINT l = located(label_id) opt = option(delimited(LANGLE, separated_list(COMMA, located(datatype)), RANGLE)) { Field(e, l, opt) }
| e1=located(expr_app) DEQUAL e2=located(expr_app) { Assign (e1, e2) }
| exp1 = located(expr_app) exp2 = located(expr_app) { Apply(exp1, exp2) }

expr_with_par:
|e = expr { e }
|e = expr_tupl { e }
|e = located(expr_app) COLON t = located(datatype) { TypeAnnotation(e, t) }
|  { Tuple([]) } (*S'il n'y a rien dans la parenthèse, initialisation du tuple*)

expr_seq:
  exp1 = located(expr) exp2 = expr_seq_inf+ { Sequence(exp1 :: exp2) }

expr_seq_inf:
	SEMICOLON e = located(expr) { e }

expr_record:
	lid = located(label_id) EQUAL e = located(expr) { (lid, e) }

expr_tupl:
  exp1 = located(expr_app) exp2 = expr_tuple_inf+ { Tuple(exp1 :: exp2) }

expr_tuple_inf:
	COMMA e = located(expr_app) { e }

expr_atom:
| l = located(literal) { Literal l }
| vid = located(identifiant) opt = option(delimited(LANGLE, separated_list(COMMA, located(datatype)), RANGLE)) { Variable(vid, opt) }
| cid = located(const_id) opt1 = option(delimited(LANGLE, separated_list(COMMA, located(datatype)), RANGLE)) opt2 = option(delimited(PO, separated_list(COMMA, located(expr)), PF)) { let expressions = match opt2 with | Some exprs -> exprs | None -> [] in Tagged(cid, opt1, expressions) }
| REF e = located(expr_atom){ Ref e }
| MARK e = located(expr_atom) { Read e }
| WHILE PO exp1 = located(expr_app) PF AO exp2 = located(expr_app) AF { While(exp1, exp2) }
| FOR v = located(identifiant) FROM PO exp1 = located(expr_app) PF TO PO exp2 = located(expr_app) PF AO exp3 = located(expr_app) AF { For(v, exp1, exp2, exp3) }
| IF PO exp1 = located(expr_app) PF THEN AO exp2 = located(expr_app) AF expOpt = option(else_aux) { let expr = Tuple([]) in let exp3 = match expOpt with | None -> unknown_pos expr | Some x -> x in IfThenElse(exp1, exp2, exp3) }
| MATCH PO e = located(expr_app) PF AO m = branches AF { Case(e, m) }
| DO AO exp1 = located(expr_app) AF UNTIL PO exp2 = located(expr_app) PF { let exp = While(exp2, exp1) in Sequence(exp1 :: (Position.unknown_pos exp) :: []) }
| AO l = separated_nonempty_list(COMMA, expr_record) AF opt = option(delimited(LANGLE, separated_list(COMMA, located(datatype)), RANGLE)) { Record(l, opt) }
| f = expr_ano_fun { Fun(f) }

expr_ano_fun:
  ANTISLASH p = located(pattern) ARROW e = located(expr) { FunctionDefinition(p, e) }

else_aux:
	ELSE AO e = located(expr) AF { e }

branches:
| PIPE ? br = located(branch) brs = separated_list(PIPE, located(branch))
{
  br :: brs
}

branch:
p = located(pattern) ARROW e = located(expr)
{
  Branch(p, e)
}

binop: b = located(binope)
{
  let expr = Variable(b, None) in expr
}

binope:
| PLUS { Id "`+`" }
| MINUS { Id "`-`" }
| STAR { Id "`*`" }
| SLASH { Id "`/`" }
| LOR { Id "`||`" }
| LAND { Id "`&&`" }
| EQ { Id "`=?`" }
| LOE { Id "`<=?`" }
| HOE { Id "`>=?`" }
| INFT { Id "`<?`" }
| SUPT { Id "`>?`" }

pattern:
| ap = located(atomic_pattern) ECOM ap2 = located(atomic_pattern) el = ecom_list
{
  PAnd (ap :: ap2 :: el)
}
| pp = pattern_pipe
{
  pp
}

ecom_list:
| ECOM ap = located(atomic_pattern) el = ecom_list
{
  ap :: el
}
| { [] }

pattern_pipe:
| ap = located(atomic_pattern) PIPE ap2 = located(atomic_pattern) pl = pipe_list
{
  POr (ap :: ap2 :: pl)
}
| pa = pattern_anot
{
  pa
}

pipe_list:
| PIPE ap = located(atomic_pattern) pl = pipe_list
{
  ap :: pl
}
| { [] }

pattern_anot:
| ap = located(atomic_pattern) COLON dt = located(datatype)
{
  PTypeAnnotation (ap, dt)
}
| ap = atomic_pattern
{
  ap
}

atomic_pattern:
| p = located(identifiant)
{
  PVariable p
}
| WILDCARD
{
  PWildcard
}
| PO p = separated_list(COMMA, located(pattern)) PF
{
  PTuple (p)
}
| p = located(literal)
{
  PLiteral p
}
| c = located(const_id) opt1 = option(delimited(LANGLE, separated_list(COMMA, located(datatype)), RANGLE)) opt2 = loption(delimited(PO, separated_nonempty_list(COMMA, located(pattern)), PF))
{
  PTaggedValue(c, opt1, opt2)
}
| AO l = separated_nonempty_list(COMMA, pattern_record) AF opt = option(delimited(LANGLE, separated_list(COMMA, located(datatype)), RANGLE))
{
  PRecord(l,opt)
}

pattern_record:
| labelid = located(label_id) EQUAL p = located(pattern)
{
  (labelid, p)
}

identifiant: i = VAR_ID { Id i }
const_id: i = CONSTR_ID { KId i }
label_id: i = LABEL_ID { LId i }

%inline literal:
| x = INT { LInt (Mint.of_string x) }
| s = STRING { LString s }
| c = CHAR { LChar c }

%inline located(X): x=X {
  Position.with_poss $startpos $endpos x
}
