{
open Parser
}

let white = [' ' '\t' '\n']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let inner_letter = ['a'-'z' 'A'-'Z' '-']
let id = letter inner_letter*

rule read = 
  parse
  | white { read lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "[" { LSQAREN }
  | "]" { RSQAREN }
  | "type" { TYPE }
  | ":" { COLON }
  | "->" { ARROW }
  | "prove" { PROVE }
  | "by" { BY }
  | "?" { HOLE }
  | "given" { GIVEN }
  | "valid" { VALID }
  | "," { COMMA }
  | "type-type" { TYPETYPE }
  | "type-of" { TYPEOF }
  | "obvious" { OBVIOUS }
  | "MP" { MP }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }