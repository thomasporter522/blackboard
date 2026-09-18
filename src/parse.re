
open Program

let parse_program(s : string) : program = {
    let lexbuf = Lexing.from_string(s);
    let p = Parser.prog(Lexer.read, lexbuf);
    // print_endline(":"  ++ string_of_int(lexbuf.lex_start_p.pos_lnum) ++ "," ++ string_of_int(lexbuf.lex_start_p.pos_cnum));
    program_of_surface(Empty, p)
}

let program_of_file(filename : string) = {
    let ch = Stdlib.open_in(filename);
    let s = Stdlib.really_input_string(ch, Stdlib.in_channel_length(ch))
    parse_program(s)
}