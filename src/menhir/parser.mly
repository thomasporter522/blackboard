%{
open Lang.Term
open Lang.Demo
open Lang.Program
%}

%token <string> ID
%token LPAREN "("
%token RPAREN ")"
// %token LSQAREN "["
// %token RSQAREN "]"
%token EOF

%token PROP "prop"
%token TYPE "type"
%token PERIOD "."
%token COLON ":"
%token DOUBLECOLON "::"
%token ARROW "->"
%token LAMBDA "=>"

%token PROVE "prove"
%token BY "by"
%token ASSUME "assume"
%token CONSTRUCT "construct"


%token GIVEN "given"
%token VALID "valid"
%token COMMA ","
%token HOLE "?"
%token TYPETYPE "type-type"
%token PROPARROWTYPE "prop-arrow-type"
%token TYPARROWTYPE "type-arrow-type"
%token TYPEOF "type-of"
%token AP "ap"
%token AT "@"
%token OBVIOUS "obvious"
%token CLAIM "claim"
%token SUFFICES "suffices"

%token CHECK "check"
%token DEFINITION "definition"
%token DIRECT "direct"
%token WITNESS "witness"
%token GIVENALL "givenall"

%start <Lang.Program.surface_program> prog
%%

let prog :=
  | EOF; { SurfaceEmpty }
  | ASSUME; s = signature; VALID; BY; d = demo; p = prog; { SurfaceAssume ((-1, -1), true, s, d, p) }
  | CONSTRUCT; s = signature; BY; d = demo; p = prog; { SurfaceConstruct ((-1, -1), true, s, d, p) }
  | PROVE; t = term; BY; d = demo; p = prog; { SurfaceProve ((-1, -1), true, t, d, p) }

let id_list := 
  | x = ID; { [x] }
  | x = ID; xs = id_list; { x :: xs }

let sigarg := 
  | LPAREN; xs = id_list; COLON; t = term; RPAREN; { (xs, t) }

let sigargs := 
  | s = sigarg; { s :: [] }
  | s = sigarg; ss = sigargs; { s :: ss }

let signature := 
  | { [] }
  | x = ID; COLON; t = term; { (x, [], t) :: [] }
  | x = ID; COLON; t = term; COMMA; s = signature; { (x, [], t) :: s }
  | x = ID; a = sigargs; COLON; t = term; { (x, a, t) :: [] }
  | x = ID; a = sigargs; COLON; t = term; COMMA; s = signature; { (x, a, t) :: s }

let atom := 
  | x = ID; { SurfaceVar((-1, -1), x) }
  | PROP; { SurfaceProp((-1, -1)) }
  | TYPE; { SurfaceTyp((-1, -1)) }
  | LPAREN; t = term; RPAREN; { t }

let atom_list := 
  | x = atom; { x }
  | t = atom_list; PERIOD; { SurfaceUnguard(t) }
  | t1 = atom_list; t2 = atom; { SurfaceAp (t1, t2) }

let term :=
  | LPAREN; xs = id_list; COLON; t1 = term; RPAREN; ARROW; t2 = term; { SurfaceArrow (Weak, xs, t1, t2) }
  | LPAREN; xs = id_list; COLON; t1 = term; RPAREN; LAMBDA; t2 = term; { SurfaceLambda (xs, t1, t2) }
  | t1 = atom; DOUBLECOLON; t2 = atom; { SurfaceIn(t1, t2) }
  | t1 = atom; ARROW; t2 = term; { SimpleArrow (t1, t2) }
  | x = atom_list; { x }

let demo_atom := 
  | _ = HOLE; { Hole((-1, -1)) }
  | x = ID; { HypProp ((-1, -1), x, Obvious((-1, -1))) }
  | LPAREN; x = ID; VALID; BY; d = demo; RPAREN; { HypProp ((-1, -1), x, d) }
  | OBVIOUS; { Obvious((-1, -1)) }
  | TYPETYPE; { TypForm((-1, -1)) }
  | LPAREN; d = demo; RPAREN; { d }
  | CHECK; { Tactic ((-1, -1), Check, []) }
  | DEFINITION; { Tactic ((-1, -1), Schema(Definition), []) }

// let demo_list := 
//   | d = demo_atom; { d :: [] }
//   | d = demo_atom; ds = demo_list; { d :: ds }

let chain_demo := 
  | d = demo_atom; { d }
  | d1 = chain_demo; d2 = demo_atom; { Use((-1, -1), d1, d2) }
  | d1 = chain_demo; AT; t = atom; VALID; BY; d2 = demo_atom; { At((-1, -1), d1, t, d2) }
  | d1 = chain_demo; AT; t = atom; { At((-1, -1), d1, t, Obvious((-1, -1))) }

let demo :=
  | d = chain_demo; { d }
  | GIVEN; x = ID; COLON; t = term; VALID; BY; d1 = demo; COMMA; d2 = demo; { Given ((-1, -1), x, t, d1, d2) }
  | GIVEN; x = ID; COLON; t = term; COMMA; d = demo; { Given ((-1, -1), x, t, Obvious((-1, -1)), d) }
  | CLAIM; x = ID; COLON; t = term; BY; d1 = demo; COMMA; d2 = demo; { Claim ((-1, -1), x, t, d1, d2) }
  | CLAIM; x = ID; COLON; t = term; COMMA; d2 = demo; { Claim ((-1, -1), x, t, Obvious((-1, -1)), d2) }
  | SUFFICES; x = ID; COLON; t = term; BY; d1 = demo; COMMA; d2 = demo; { Suffices ((-1, -1), x, t, d1, d2) }
  | SUFFICES; x = ID; COLON; t = term; COMMA; d2 = demo; { Suffices ((-1, -1), x, t, Obvious((-1, -1)), d2) }
  | AP; x = ID; t1 = atom; t2 = atom; d1 = demo_atom; d2 = demo_atom; { ApTyp ((-1, -1), x, t1, t2, d1, d2) }
  | TYPEOF; x = ID; { HypTyp ((-1, -1), x, Obvious((-1, -1))) }
  | PROPARROWTYPE; x = ID; d1 = demo_atom; d2 = demo_atom; { PropArrowForm ((-1, -1), x, d1, d2) }
  | TYPARROWTYPE; x = ID; d1 = demo_atom; d2 = demo_atom; { TypArrowForm ((-1, -1), x, d1, d2) }
  | DIRECT; d1 = demo_atom; d2 = demo; { Tactic ((-1, -1), Direct, d1 :: d2 :: []) }
  | DIRECT; d = demo_atom; { Tactic ((-1, -1), Direct, d :: []) }
  | WITNESS; t = atom; COMMA; d = demo; { Tactic ((-1, -1), Witness(t), Obvious((-1, -1)) :: d :: []) }
  | WITNESS; t = atom; VALID; BY; d1 = demo; COMMA; d2 = demo; { Tactic ((-1, -1), Witness(t), d1 :: d2 :: []) }
  | GIVENALL; d = demo; { Tactic ((-1, -1), GivenAll, d :: []) }
