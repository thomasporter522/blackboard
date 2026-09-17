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
%token OBVIOUS "obvious"

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

// let term_list := 
//   | t1 = term; t2 = term; { t1 :: t2 :: [] }
//   | t = term; ts = term_list; { t :: ts }

let demo_atom := 
  | _ = HOLE; { Hole }
  | x = ID; { Hyp x }
  | OBVIOUS; { Obvious }
  | TYPETYPE; { TypForm }
  | LPAREN; d = demo; RPAREN; { d }

// let tm_or_demo_list := 
//   | t = atom; { Tm(t) :: [] }
//   | d = demo_atom; { Demo(d) :: [] }
//   | t = atom; l = tm_or_demo_list; { Tm(t) :: l }
//   | d = demo_atom; l = tm_or_demo_list; { Demo(d) :: l }

let demo_list := 
  | d = demo_atom; { d :: [] }
  | d = demo_atom; ds = demo_list; { d :: ds }

let demo :=
  | d = demo_atom; { d }
  | x = ID; ds = demo_list; { Use(x, ds) }
  | GIVEN; x = ID; COLON; t = term; LSQAREN; VALID; BY; d1 = demo; RSQAREN; COMMA; d2 = demo; { Given (x, t, d1, d2) }
  | GIVEN; x = ID; COLON; t = term; COMMA; d = demo; { Given (x, t, Obvious, d) }
  | TYPEOF; x = ID; { HypTyp (x) }
