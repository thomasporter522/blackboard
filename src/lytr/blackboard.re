open Language
open Parser 

module BlackboardLanguage : Language = {

    type context = 
        | Term
        | Domain
        | Ident
        | Default
        | Sig
        | Demo
        | Program

    type mixfix_form = mixfix_form_of(context);
    
    let is_whitespace_character(c : char) = {
        (c == ' ' || c == '\n' || c == '\t')
    }

    let is_alpha(c : char) = Str.string_match(Str.regexp("[a-z]\|[A-Z]"), String.make(1, c), 0)

    let is_identifier_char (is_start : bool, c : char) : bool = {
        // print_endline(String.make(1, c));
        // print_endline(string_of_bool(c == '1'));
        is_start ? is_alpha(c) : (is_alpha(c) || c == '-')
    }

    let form_of_string(s : string, (arity, head)) : Option.t(mixfix_form) = {
        let split = String.split_on_char('_', s);
        let (left_tip : tip, rest : list(string)) = switch(int_of_string_opt(List.hd(split))) {
            | Some(p1) => (Precedence(Need, Precedence(p1)), List.tl(split))
            | None => (Uninterested, split)
        };
        let check(h : string) = if(h == "") { failwith("bad language specification syntax: " ++ s) } else ();
        let rec middle_and_end(strings : list(string)) : Option.t((mixfix_interior, tip)) = switch(strings) {
            | [] => None
            | [h] => switch(int_of_string_opt(h)) {
                | Some(p2) => Some(([], Precedence(Need, Precedence(p2))))
                | None => {
                    check(h);
                    Some(([h], Uninterested))
                }
            }
            | [h,...rest] => switch(middle_and_end(rest)) {
                | Some((interior, tip)) => {
                    check(h);
                    Some(([h,...interior], tip))
                }
                | None => None
            }
        }
        switch(middle_and_end(rest)) {
            | Some((interior, right_tip)) => Some({left_tip, interior, right_tip, arity, head})
            | None => None
        }
    }

    let form_summaries = 
        [("(_)", (c => (Default, [c], Default), _c => Parens)),
        ("100_:_0", (_c => (Ident, [], Term), _c => Colon)),
        ("11_->_10", (_c => (Domain, [], Term), _c => Arrow)),
        ("11_=>_10", (_c => (Domain, [], Term), _c => Lambda)),
        ("20_::_21", (_c => (Term, [], Term), _c => In)),
        ("construct_by_0", (_c => (Default, [Sig], Demo), _c => Construct)),];
    let ap_precs = (31, 30);

    let forms : list(mixfix_form) = 
        List.map(s => Option.get(form_of_string(fst(s), snd(s))), form_summaries);

    let white_precs : Option.t((precedence, precedence)) = 
        Some((Precedence(fst(ap_precs)), Precedence(snd(ap_precs))));

    let white_arity(_c : context) : (context, context) = (Term, Term);
    let white_head(_c : context) : term_head = Ap;

    let initial_context(): context = Program;
}

module BlackboardGrammar = GrammarOfLanguage(BlackboardLanguage);

module BlackboardLexer = Lexer(BlackboardGrammar);
module BlackboardParser = Parser(BlackboardGrammar);

let lex_test(s : string) : BlackboardLexer.lex_info = {
    let (_, es) = BlackboardLexer.lex(s);
    es
}

let parse(s : string) = {
    let (tokens, li) = BlackboardLexer.lex(s);
    let (_, pi) = BlackboardParser.parse(tokens);
    (li, pi)
}