open Language
open Grammar
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

    type form = form_of(context);
    
    let is_whitespace_character(c : char) = {
        (c == ' ' || c == '\n' || c == '\t')
    }

    let is_alpha(c : char) = Str.string_match(Str.regexp("[a-z]\|[A-Z]"), String.make(1, c), 0)

    let is_identifier_char (is_start : bool, c : char) : bool = {
        // print_endline(String.make(1, c));
        // print_endline(string_of_bool(c == '1'));
        is_start ? is_alpha(c) : (is_alpha(c) || c == '-')
    }

    let mixfix_form_of_string(s : string, (arity, head)) : Option.t(form) = {
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
            | Some((interior, right_tip)) => Some(Mixfix({left_tip, interior, right_tip, arity, head}))
            | None => None
        }
    }

    let repeater_form_of_string(s : string, (arity, head)) : Option.t(form) = {
        let split = String.split_on_char('_', s);
        let (left_tip : tip, rest : list(string)) = switch(int_of_string_opt(List.hd(split))) {
            | Some(p1) => (Precedence(Need, Precedence(p1)), List.tl(split))
            | None => (Uninterested, split)
        };
        let (delim, right_tip) = switch(rest) {
        | [d] => (d, Uninterested)
        | [d, p2] => (d, Precedence(Need, Precedence(int_of_string(p2))))
        | _ => failwith("incorrect formatting: repeater_form_of_string")
        };
        Some(Repeater({left_tip, delim, right_tip, arity, head}))
    }

    let mixfix_form_summaries = 
        [("(_)", (c => (Default, [c], Default), _c => Parens)),
        ("?", (_c => (Default, [], Default), _c => Interaction)),
        ("100_:_0", (_c => (Ident, [], Term), _c => Colon)),
        ("11_->_10", (_c => (Domain, [], Term), _c => Arrow)),
        ("11_=>_10", (_c => (Domain, [], Term), _c => Lambda)),
        ("20_::_21", (_c => (Term, [], Term), _c => In)),
        ("if_then_else_6", (_c => (Default, [Term, Term], Term), _c => ITE)),
        ("construct_by_0", (_c => (Default, [Sig], Demo), _c => Construct)),];
    let repeater_form_summaries = 
        [("5_,_5", (_c => Domain, _c => Commas)),];
    let ap_precs = (31, 30);

    let forms : list(form) = 
        List.map(s => Option.get(mixfix_form_of_string(fst(s), snd(s))), mixfix_form_summaries)
        @ List.map(s => Option.get(repeater_form_of_string(fst(s), snd(s))), repeater_form_summaries)
;

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
    let (_, es) = BlackboardLexer.lex(s, 0);
    es
}

let parse(s : string, cursor_position : int) = {
    let (tokens, li) = BlackboardLexer.lex(s, cursor_position);
    let (_, pi) = BlackboardParser.parse(tokens);
    (li, pi)
}