%{
open Ast

let loc (startpos:Lexing.position) (endpos:Lexing.position) (elt:'a) : 'a node =
  { elt ; loc=Range.mk_lex_range startpos endpos }

%}

/* Declare your tokens here. */
%token EOF

%token <int64>  INT
%token NULL     /* null */
%token <string> STRING
%token <string> IDENT

%token TINT     /* int */
%token TVOID    /* void */
%token TSTRING  /* string */
%token TBOOL    /* bool */

%token IF       /* if */
%token ELSE     /* else */
%token WHILE    /* while */
%token FOR      /* for */
%token RETURN   /* return */
%token VAR      /* var */
%token GLOBAL   /* global */
%token TRUE     /* true */
%token FALSE    /* false */
%token NEW      /* new */

%token SEMI     /* ; */
%token COMMA    /* , */
%token LBRACE   /* { */
%token RBRACE   /* } */

%token PLUS     /* + */
%token DASH     /* - */
%token STAR     /* * */
%token EQEQ     /* == */
%token EQ       /* = */
%token NEQ      /* != */
%token AND      /* & */
%token OR       /* | */
%token IAND     /* [&] */
%token IOR      /* [|] */
%token SHL      /* << */
%token SHR      /* >> */
%token SAR      /* >>> */
%token LT       /* < */
%token LTE      /* <= */
%token GT       /* > */
%token GTE      /* >= */

%token LPAREN   /* ( */
%token RPAREN   /* ) */
%token LBRACKET /* [ */
%token RBRACKET /* ] */

%token TILDE    /* ~ */
%token BANG     /* ! */


/* precedence */
%left IOR           /* 20  */
%left IAND          /* 30  */
%left OR            /* 40  */
%left AND           /* 50  */
%left EQEQ NEQ      /* 60  */
%left LT LTE GT GTE /* 70  */
%left SHL SHR SAR   /* 80  */
%left PLUS DASH     /* 90  */
%left STAR          /* 100 */

%nonassoc BANG
%nonassoc TILDE
%nonassoc LBRACKET
%nonassoc LPAREN

/* ---------------------------------------------------------------------- */

%start prog
%start exp_top
%start stmt_top
%type <Ast.exp Ast.node> exp_top
%type <Ast.stmt Ast.node> stmt_top

%type <Ast.prog> prog
%type <Ast.exp Ast.node> exp
%type <Ast.stmt Ast.node> stmt
%type <Ast.block> block
%type <Ast.ty> ty
%%

exp_top:
  | e=exp EOF { e }

stmt_top:
  | s=stmt EOF { s }

/* prog */
prog:
  | p=list(decl) EOF  { p }

/* global declarations */
decl:
  | GLOBAL name=IDENT EQ init=gexp SEMI /* global variable declarations*/
    { Gvdecl (loc $startpos $endpos { name; init }) }
  | frtyp=ret_ty fname=IDENT LPAREN args=arglist RPAREN body=block /* function declaration */
    { Gfdecl (loc $startpos $endpos { frtyp; fname; args; body }) }

/* args */
arglist:
  | l=separated_list(COMMA, pair(ty,IDENT)) { l }

/* types */
ty:
  | TINT   { TInt }
  | TBOOL  { TBool }
  | r=rtyp { TRef r }

/* return types */
%inline ret_ty:
  | TVOID  { RetVoid }
  | t=ty   { RetVal t }

/* reference types */
%inline rtyp:
  | TSTRING { RString }
  | t=ty LBRACKET RBRACKET { RArray t }

/* binary ops */
%inline bop:
  | STAR   { Mul }
  | PLUS   { Add }
  | DASH   { Sub }
  | SHL    { Shl }
  | SHR    { Shr }
  | SAR    { Sar }
  | LT     { Lt }
  | LTE    { Lte }
  | GT     { Gt }
  | GTE    { Gte }
  | EQEQ   { Eq }
  | NEQ    { Neq }
  | AND    { And }
  | OR     { Or }
  | IAND   { IAnd }
  | IOR    { IOr }

/* unary ops */
%inline uop:
  | DASH  { Neg }
  | BANG  { Lognot }
  | TILDE { Bitnot }

/* global initializers */
gexp:
  | i=INT        { loc $startpos $endpos @@ CInt i }
  | str=STRING   { loc $startpos $endpos @@ CStr str}
  | t=rtyp NULL  { loc $startpos $endpos @@ CNull t }
  | TRUE         { loc $startpos $endpos @@ CBool true}
  | FALSE        { loc $startpos $endpos @@ CBool false}
  | NEW t=ty LBRACKET RBRACKET LPAREN es=separated_list(COMMA, gexp) RPAREN
                 { loc $startpos $endpos @@ CArr (t, es)}

/* lhs expressions */
lhs:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | e=exp LBRACKET i=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e, i) }

/* expressions */
exp:
  | id=IDENT            { loc $startpos $endpos @@ Id id }
  | i=INT               { loc $startpos $endpos @@ CInt i }
  | str=STRING          { loc $startpos $endpos @@ CStr str}
  | t=rtyp NULL         { loc $startpos $endpos @@ CNull t }
  | TRUE                { loc $startpos $endpos @@ CBool true}
  | FALSE               { loc $startpos $endpos @@ CBool false}
  | e1=exp LBRACKET e2=exp RBRACKET
                        { loc $startpos $endpos @@ Index (e1, e2) }
  | NEW t=ty LBRACKET RBRACKET LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ CArr (t, es) }
  | NEW t=ty  LBRACKET e=exp RBRACKET
                        { loc $startpos $endpos @@ NewArr (t,e) }
  | e1=exp b=bop e2=exp { loc $startpos $endpos @@ Bop (b, e1, e2) }
  | u=uop e=exp         { loc $startpos $endpos @@ Uop (u, e) }
  | LPAREN e=exp RPAREN { e }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN
                        { loc $startpos $endpos @@ Call (e, es) }

/* local declarations */
vdecl:
  | VAR id=IDENT EQ init=exp { (id, init) }

/* decl list */
vdecls:
  | l = separated_list(COMMA, vdecl) { l }

/* statements */
stmt:
  | d=vdecl SEMI        { loc $startpos $endpos @@ Decl(d) }
  | p=lhs EQ e=exp SEMI { loc $startpos $endpos @@ Assn(p,e) }
  | e=exp LPAREN es=separated_list(COMMA, exp) RPAREN SEMI
                        { loc $startpos $endpos @@ SCall (e, es) }
  | ifs=if_stmt         { ifs }
  | RETURN SEMI         { loc $startpos $endpos @@ Ret(None) }
  | RETURN e=exp SEMI   { loc $startpos $endpos @@ Ret(Some e) }
  | FOR LPAREN vd=vdecls SEMI eo=option(exp) SEMI so=option(stmt) RPAREN b=block
                        { loc $startpos $endpos @@ For(vd, eo, so, b)}
  | WHILE LPAREN e=exp RPAREN b=block
                        { loc $startpos $endpos @@ While(e, b) }

block:
  | LBRACE stmts=list(stmt) RBRACE { stmts }

/* if statements */
if_stmt:
  | IF LPAREN e=exp RPAREN b1=block b2=else_stmt
    { loc $startpos $endpos @@ If(e,b1,b2) }

/* else statements */
else_stmt:
  | (* empty *)       { [] }
  | ELSE b=block      { b }
  | ELSE ifs=if_stmt  { [ ifs ] }
