
open Program

let parse_program(s : string) : program = {
    let lexbuf = Lexing.from_string(s);
    let p = Parser.prog(Lexer.read, lexbuf);
    program_of_surface(p)
}

let program_of_file(filename : string) = {
    let ch = Stdlib.open_in(filename);
    let s = Stdlib.really_input_string(ch, Stdlib.in_channel_length(ch))
    parse_program(s)
}