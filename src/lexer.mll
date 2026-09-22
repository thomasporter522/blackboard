{
open Parser
}

let white = [' ' '\t' '\n']+
let digit = ['0'-'9']
let int = '-'? digit+
let letter = ['a'-'z' 'A'-'Z']
let inner_letter = ['a'-'z' 'A'-'Z' '-' '0'-'9']
let id = letter inner_letter*

rule read = 
  parse
  | white { read lexbuf }
  | "(" { LPAREN }
  | ")" { RPAREN }
  (* | "[" { LSQAREN }
  | "]" { RSQAREN } *)
  | "type" { TYPE }
  | ":" { COLON }
  | "->" { ARROW }
  | "prove" { PROVE }
  | "by" { BY }
  | "assume" { ASSUME }
  | "construct" { CONSTRUCT }
  | "?" { HOLE }
  | "given" { GIVEN }
  | "valid" { VALID }
  | "," { COMMA }
  | "type-type" { TYPETYPE }
  | "arrow-type" { ARROWTYPE }
  | "type-of" { TYPEOF }
  | "ap" { AP }
  | "obvious" { OBVIOUS }
  | "claim" { CLAIM }
  | "suffices" { SUFFICES }
  | "check" { CHECK }
  | id { ID (Lexing.lexeme lexbuf) }
  | eof { EOF }