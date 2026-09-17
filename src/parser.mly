%{
open Demo
open Program
%}

%token <string> ID
%token LPAREN "("
%token RPAREN ")"
%token LSQAREN "["
%token RSQAREN "]"
%token EOF

%token TYPE "type"
%token COLON ":"
%token ARROW "->"

%token PROVE "prove"
%token BY "by"


%token GIVEN "given"
%token VALID "valid"
%token COMMA ","
%token HOLE "?"
%token TYPETYPE "type-type"
%token TYPEOF "type-of"

%start <Program.surface_program> prog
%%

let prog :=
  | EOF; { Empty }
  | PROVE; t = term; BY; d = demo; p = prog; { Prove (t, d, p) }

let atom := 
  | x = ID; { Var x }
  | TYPE; { Typ }
  | LPAREN; t = term; RPAREN; { t }

let applicable := 
  | x = atom; { x }
  | t1 = applicable; t2 = atom; { Ap (t1, t2) }

let id_list := 
  | x = ID; { [x] }
  | x = ID; xs = id_list; { x :: xs }

let term :=
  | LPAREN; xs = id_list; COLON; t1 = term; RPAREN; ARROW; t2 = term; { Arrow (xs, t1, t2) }
  | t1 = term; ARROW; t2 = term; { SimpleArrow (t1, t2) }
  | x = applicable; { x }

let demo :=
  | _ = HOLE; { Hole }
  | GIVEN; x = ID; COLON; t = term; LSQAREN; VALID; BY; d1 = demo; RSQAREN; COMMA; d2 = demo; { Given (x, t, d1, d2) }
  | GIVEN; x = ID; COLON; t = term; COMMA; d = demo; { Given (x, t, Obvious, d) }
  | x = ID; { Hyp x }
  | TYPETYPE; { TypForm }
  | TYPEOF; x = ID; { HypTyp (x) }
  | LPAREN; d = demo; RPAREN; { d }