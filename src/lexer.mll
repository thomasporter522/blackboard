{
open Parser
}

let white = [' ' '\t' '\n']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let id = letter+

rule read = 
  parse
  | white { read lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  | "type" { TYPE }
  | ":" { COLON }
  | "->" { ARROW }
  | "prove" { PROVE }
  | "by" { BY }
  | "?" { HOLE }
  | "given" { GIVEN }
  | "," { COMMA }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }