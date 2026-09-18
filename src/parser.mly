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
%token ASSUME "assume"
%token CONSTRUCT "construct"


%token GIVEN "given"
%token VALID "valid"
%token COMMA ","
%token HOLE "?"
%token TYPETYPE "type-type"
%token ARROWTYPE "arrow-type"
%token TYPEOF "type-of"
%token OBVIOUS "obvious"
%token CLAIM "claim"
%token SUFFICES "suffices"

%start <Program.surface_program> prog
%%

let prog :=
  | EOF; { Empty }
  | ASSUME; s = signature; VALID; BY; d = demo; p = prog; { Assume (s, d, p) }
  | CONSTRUCT; s = signature; BY; d = demo; p = prog; { Construct (s, d, p) }
  | PROVE; t = term; BY; d = demo; p = prog; { Prove (t, d, p) }

let signature := 
  | { [] }
  | x = ID; COLON; t = term; { (x, t) :: [] }
  | x = ID; COLON; t = term; COMMA; s = signature; { (x, t) :: s }

let atom := 
  | x = ID; { Var x }
  | TYPE; { Typ }
  | LPAREN; t = term; RPAREN; { t }

let atom_list := 
  | x = atom; { x }
  | t1 = atom_list; t2 = atom; { Ap (t1, t2) }

let id_list := 
  | x = ID; { [x] }
  | x = ID; xs = id_list; { x :: xs }

let term :=
  | LPAREN; xs = id_list; COLON; t1 = term; RPAREN; ARROW; t2 = term; { Arrow (xs, t1, t2) }
  | t1 = atom; ARROW; t2 = term; { SimpleArrow (t1, t2) }
  | x = atom_list; { x }

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
  // | t = atom; { Term(t) }
  | x = ID; ds = demo_list; { Use(x, ds) }
  | GIVEN; x = ID; COLON; t = term; VALID; BY; d1 = demo; COMMA; d2 = demo; { Given (x, t, d1, d2) }
  | GIVEN; x = ID; COLON; t = term; COMMA; d = demo; { Given (x, t, Obvious, d) }
  | CLAIM; x = ID; COLON; t = term; BY; d1 = demo; COMMA; d2 = demo; { Claim (x, t, d1, d2) }
  | CLAIM; x = ID; COLON; t = term; COMMA; d2 = demo; { Claim (x, t, Obvious, d2) }
  | SUFFICES; x = ID; COLON; t = term; BY; d1 = demo; COMMA; d2 = demo; { Suffices (x, t, d1, d2) }
  | SUFFICES; x = ID; COLON; t = term; COMMA; d2 = demo; { Suffices (x, t, Obvious, d2) }
  | TYPEOF; x = ID; { HypTyp (x) }
  | ARROWTYPE; x = ID; d1 = demo_atom; d2 = demo_atom; { ArrowForm (x, d1, d2) }
