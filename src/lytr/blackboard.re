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
        is_start ? is_alpha(c) : (is_alpha(c) || c == '-')
    }

    // let old_mixfix_form_of_string(s : string, (arity, head)) : Option.t(form) = {
    //     let split = String.split_on_char('_', s);
    //     let (left_tip : tip, rest : list(string)) = switch(int_of_string_opt(List.hd(split))) {
    //         | Some(p1) => (Precedence(Need, Precedence(p1)), List.tl(split))
    //         | None => (Uninterested, split)
    //     };
    //     let check(h : string) = if(h == "") { failwith("bad language specification syntax: " ++ s) } else ();
    //     let rec middle_and_end(strings : list(string)) : (mixfix_interior, tip) = switch(strings) {
    //         | [] => failwith("bad language specification syntax")
    //         | [h] => 
    //             check(h);
    //             (Just(h), Uninterested)
    //         | [t1, t2] => switch(int_of_string_opt(t2)) {
    //             | Some(p2) => 
    //                 check(t1);
    //                 (Just(t1), Precedence(Need, Precedence(p2)))
    //             | None => {
    //                 check(t1);
    //                 check(t2);
    //                 (Child(t1, Just(t2)), Uninterested)
    //             }
    //         }
    //         | [h,...rest] => 
    //             let (form, right_tip) = middle_and_end(rest);
    //             check(h);
    //             (Child(h, form), right_tip)
    //     }
    //     let (interior, right_tip) = middle_and_end(rest);
    //     Some(Mixfix({left_tip, interior, right_tip, arity, head}))
    // }

    let rec munch_int(s : string) : (string, string) = {
        let s0 = String.sub(s, 0, 1);
        switch(int_of_string_opt(s0)) {
        | Some(_) => 
            let (s1, s2) = munch_int(String.sub(s, 1, String.length(s)-1));
            (s0 ++ s1, s2)
        | None => 
            ("", s)
        }
    }

    let tail = s => String.sub(s, 1, String.length(s)-1);

    let rec munch_delim(s : string) : Option.t((string, string, string)) = {
        if (s == "") None else {
            let s0 = String.sub(s, 0, 1);
            let s1 = tail(s);
            switch(s0) {
            | "" => None
            | "_" => Some(("", "_", s1))
            | "$" => Some(("", "$", s1))
            | _ => switch(munch_delim(s1)) {
                | Some((s1, s2, s3)) => Some((s0 ++ s1, s2, s3))
                | None => None
                }
            }
        }
    }

    let mixfix_form_of_string(s : string, (arity, builder)) : Option.t(form) = {
        let (p1, s) = munch_int(s);
        let (left_tip, s) = 
            if(p1 == "") { (Uninterested, s) } 
            else if (String.sub(s, 0, 2) == "?_") {
                (Precedence(Want, Precedence(int_of_string(p1))), String.sub(s, 2, String.length(s)-2))
            } else if (String.sub(s, 0, 1) == "_") {
                (Precedence(Need, Precedence(int_of_string(p1))), tail(s))
            } else failwith("ill formed language spec");
        let rec build_middle(s : string) : (Option.t(mixfix_interior), tip) = switch(munch_delim(s)) {
            | Some((s1, sep, s2)) => 
                let (i, t) = build_middle(s2);
                switch(i) {
                | None => (Some(Just(s1)), t)
                | Some(i) => (Some(sep == "_" ? Child(s1, i) : sep == "$" ? Secondary(s1, i) : failwith("ill formed language spec")), t)
                }
            | None => {
                let (q, s') = String.sub(s, 0, 1) == "?" ? ("?", tail(s)) : ("", s);
                let thing = switch(int_of_string_opt(s')) {
                | Some(p2) => q == "?" ? (None, Precedence(Want, Precedence(p2))) : (None, Precedence(Need, Precedence(p2)));
                | None => (Some(Just(s)), Uninterested)
                };
                thing
            }
        };
        let (interior, right_tip) = build_middle(s);
        Some(Mixfix({left_tip, interior: Option.get(interior), right_tip, arity, builder}))
    }


    let repeater_form_of_string(s : string, (arity, builder)) : Option.t(form) = {
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
        Some(Repeater({left_tip, delim, right_tip, arity, builder}))
    }

    let infix_of( head, _, first, _, last, _) = {
        let (c1, ss1) = Option.get(first);
        let (ss2, c2) = Option.get(last);
        let r = (snd(range_of_some_lc(first)), fst(range_of_some_rc(last)));
        Infix(head, r, c1, ss1, ss2, c2)
    }

    let atom_of(head, _, _, _, _, r) = Atom(head,r);

    let mixfix_form_summaries : list((string, (context => (context, list(context), context), builder_type(context)))) = 
        [
        ("(_)", (c => (Default, [c], Default), 
            (_, _, m, _, r) => Parens(r, List.hd(m)))),
        ("?", (_c => (Default, [], Default), atom_of(Hole))),
        ("prop", (_c => (Default, [], Default), atom_of(Prop))),
        ("type", (_c => (Default, [], Default), atom_of(Type))),
        ("check", (_c => (Default, [], Default), atom_of(Check))),
        ("11_:_10", (_c => (Ident, [], Term), infix_of(Colon))),
        ("20_::_21", (_c => (Term, [], Term), infix_of(In))),
        ("11_->_10", (_c => (Domain, [], Term), infix_of(Arrow))),
        ("11_=>_10", (_c => (Domain, [], Term), infix_of(Lambda))),
        ("30_@_31", (_c => (Domain, [], Term), infix_of(At))),
        ("given_:_,_0", (_c => (Default, [Ident, Term], Demo), 
            (_, _, middle, last, r) => {
                let (x, t) = switch(middle) {
                | [x, t] => (x, t)
                | _ => failwith("given missing args")
                };
                let (ss, rest) = Option.get(last);
                let r' = (fst(r), fst(range_of_some_rc(last)));
                Given(r', x, t, ss, rest)
            })),
        ("construct_by_end_0", (_c => (Default, [Sig, Demo], Program), 
            (_, _, middle, last, r) => {
                let (sg, d) = switch(middle) {
                | [sg, d] => (sg, d)
                | _ => failwith("construction missing args")
                };
                let (ss, rest) = Option.get(last);
                let r' = (fst(r), fst(r) + String.length("construct"));
                Construct(r', sg, d, ss, rest)
            })),
        ("assume_valid$by_end_0", (_c => (Default, [Sig, Default, Demo], Program), 
            (_, _, middle, last, r) => {
                let (sg, d) = switch(middle) {
                | [sg, _, d] => (sg, d)
                | _ => failwith("assumption missing args")
                };
                let (ss, rest) = Option.get(last);
                let r' = (fst(r), fst(r) + String.length("assume"));
                Assume(r', sg, d, ss, rest)
            })),
        ];
    let repeater_form_summaries = 
        [("5_,_5", (_c => Domain, 
            (_, first, middle, last, _) => {
                let (c1, ss1) = Option.get(first);
                let (ss2, c2) = Option.get(last);
                let r = (snd(range_of_some_lc(first)), fst(range_of_some_rc(last)));
                Commas(r, c1, ss1, middle, ss2, c2)
            }))];
    let ap_precs = (30, 31);

    let forms : list(form) = 
        List.map(s => Option.get(mixfix_form_of_string(fst(s), snd(s))), mixfix_form_summaries)
        @ List.map(s => Option.get(repeater_form_of_string(fst(s), snd(s))), repeater_form_summaries)
;

    let white_precs : Option.t((precedence, precedence)) = 
        Some((Precedence(fst(ap_precs)), Precedence(snd(ap_precs))));

    let white_arity(_c : context) : (context, context) = (Term, Term);
    let white_builder(_c : context, lc : abstract_term, ss : list(secondary), rc : abstract_term) : abstract_term = {
        let r = (snd(whole_range(lc)), fst(whole_range(rc)));
        Ap(r, lc, ss, rc);
    }

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
    let (a, pi) = BlackboardParser.parse(tokens);
    (li, pi, a)
}