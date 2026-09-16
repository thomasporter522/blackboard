%{
open Program
%}

%token <string> ID
%token LPAREN "("
%token RPAREN ")"
%token EOF

%token TYPE "type"
%token COLON ":"
%token ARROW "->"

%token PROVE "prove"
%token BY "by"


%token ASSUME "assume"
%token HOLE "?"

%start <Program.alpha_program> prog
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

let term :=
  | LPAREN; x = ID; COLON; t1 = term; RPAREN; ARROW; t2 = term; { Arrow (x, t1, t2) }
  | x = applicable; { x }

let demo :=
  | x = HOLE; { Hole }
  | ASSUME; d = demo; { ArrowIntro d }
  | x = ID; { Hyp x }