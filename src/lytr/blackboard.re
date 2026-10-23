open Language
open Parser 

module BlackboardLanguage : Language = {

    type context = Exp
    
    let is_whitespace_character(c : char) = {
        (c == ' ' || c == '\n' || c == '\t')
    }

    let is_alpha(c : char) = Str.string_match(Str.regexp("[a-z]\|[A-Z]"), String.make(1, c), 0)

    let is_identifier_char (is_start : bool, c : char) : bool = {
        // print_endline(String.make(1, c));
        // print_endline(string_of_bool(c == '1'));
        is_start ? is_alpha(c) : (is_alpha(c) || c == '-')
    }

    let form_of_string(s : string) : Option.t(mixfix_form) = {
        let split = String.split_on_char('_', s);
        let (left_tip : tip, rest : list(string)) = switch(int_of_string_opt(List.hd(split))) {
            | Some(p1) => (Precedence(Precedence(p1)), List.tl(split))
            | None => (Uninterested, split)
        };
        let rec middle_and_end(strings : list(string)) : Option.t((mixfix_interior, tip)) = switch(strings) {
            | [] => None
            | [h] => switch(int_of_string_opt(h)) {
                | Some(p2) => Some(([], Precedence(Precedence(p2))))
                | None =>  Some(([h], Uninterested))
            }
            | [h,...rest] => switch(middle_and_end(rest)) {
                | Some((interior, tip)) => Some(([h,...interior], tip))
                | None => None
            }
        }
        switch(middle_and_end(rest)) {
            | Some((interior, right_tip)) => Some({left_tip, interior, right_tip})
            | None => None
        }
    }

    let form_strings = 
        ["(_)",
        "100_:_0",
        "11_->_10", 
        "11_=>_10", 
        "20_::_21",
        "construct_by_"];

    let forms : list(mixfix_form) = List.map(s => Option.get(form_of_string(s)), form_strings);
    let initial_context(): context = Exp;
}

module BlackboardGrammar = GrammarOfLanguage(BlackboardLanguage);

module BlackboardLexer = Lexer(BlackboardGrammar);

let lex_test(s : string) : BlackboardLexer.lex_info = {
    let (_, es) = BlackboardLexer.lex(s);
    es
}