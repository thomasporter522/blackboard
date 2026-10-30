open Js_of_ocaml

type jsarray('a) = Js.t(Js.js_array('a));

let jsarray_of(l : list('a)) = Js.array(Array.of_list(l));

type range = jsarray(Js.number_t);

type lex_result = Js.t({. errors: Js.readonly_prop(jsarray(range)), delimiters : Js.readonly_prop(jsarray(range))});

let js_lexer(s : string) : lex_result = {
    let li = Lytr.Blackboard.lex_test(s);
    let f(x : (int, int)) : Js.t(Js.js_array(Js.number_t)) = {
        let(a, b) = x;
        let l = [Js.int32(Int32.of_int(a)), Js.int32(Int32.of_int(b))];
        jsarray_of(l)
    };
    let result = [%js {as _; val errors = Js.array(Array.of_list(List.map(f, li.lex_errors))); val delimiters = Js.array(Array.of_list(List.map(f, li.delimiters)))}];
    result
}

type error = Js.t({.
    message: Js.readonly_prop(Js.t(Js.js_string)), 
    range: Js.readonly_prop(range),
    underline : Js.readonly_prop(Js.t(bool)),
});

type goal = Js.t({. 
    statement: Js.readonly_prop(Js.t(Js.js_string)), 
    context: Js.readonly_prop(jsarray(Js.t(Js.js_string))), 
    range: Js.readonly_prop(range),
});

type parse_result = Js.t({. 
    runes: Js.readonly_prop(jsarray(range)), 
    delimiters : Js.readonly_prop(jsarray(range)),
    parseerrors : Js.readonly_prop(jsarray(error)),
    elaberrors : Js.readonly_prop(jsarray(error)),
    checkerrors : Js.readonly_prop(jsarray(error)),
    completions : Js.readonly_prop(jsarray(Js.t(Js.js_string))),
    victories : Js.readonly_prop(jsarray(range)),
    goals : Js.readonly_prop(jsarray(goal))
});

let js_parser(s : string, cursor_position : int) : parse_result = {
    let (li, pi, a) = Lytr.Blackboard.parse(s, cursor_position);
    let (sp, elab_errors) =  Lytr.Elab.elab(a);
    let pp = Lang.Program.check_surface_program(sp);
    let f1(x : (int, int)) : Js.t(Js.js_array(Js.number_t)) = {
        let(a, b) = x;
        let l = [Js.int32(Int32.of_int(a)), Js.int32(Int32.of_int(b))];
        jsarray_of(l)
    };
    let message_f(k: Lytr.Blackboard.BlackboardParser.error_kind) = switch(k) {
        | UnmatchedDelimiter => "unmatched delimiter"
        | MissingLeftChild => "missing left constituent"
        | MissingRightChild => "missing right constituent"
        | MissingInnerChild => "missing constituent"
        | ExtraneousChild => "this is no place for text"
        | Multiple => "multiple terms"
    }
    let f2(x : Lytr.Blackboard.BlackboardParser.error) : error = [%js {as _; 
        val message = Js.string(message_f(x.kind));
        val range = f1(x.range);
        val underline = if (Lytr.Blackboard.BlackboardParser.format_of_error_kind(x.kind) == Underline) {Js.bool(true)} else {Js.bool(false)};
    }];
    let f3(x : list(string)) : list(Js.t(Js.js_string)) = List.map(s => Js.string(s), x);
    let f5(r : (Lang.Term.judgment, (int, int))) : goal = {
        let (cs, g) = Lang.Lang_printing.strings_of_judgment(fst(r));
        [%js {as _; 
            val statement = Js.string(g); 
            val context = Js.array(Array.of_list(List.map(Js.string, cs)));
            val range = f1(snd(r)); 
        }]
    };
    let f4(r : Lang.Demo.report) : list(goal) = {
        List.map(f5, r.open_goals);
    };
    let f7(e : Lang.Term.ranged_error) : error = [%js {as _; 
        val message = Js.string(e.message);
        val range = f1(e.range);
        val underline = Js.bool(true);
    }];
    let f6(r : Lang.Demo.report) : list(error) = List.map(f7, r.errors);
    let f8(r : Lang.Demo.report) : list(range) = List.map(f1, r.completes);
    let result = [%js {as _; 
        val runes = Js.array(Array.of_list(List.map(f1, li.lex_errors))); 
        val delimiters = Js.array(Array.of_list(List.map(f1, li.delimiters)));
        val parseerrors = Js.array(Array.of_list(List.map(f2, pi.errors)));
        val elaberrors = Js.array(Array.of_list(List.map(f7, elab_errors)));
        val checkerrors = Js.array(Array.of_list(List.concat_map(f6, pp)));
        val completions = Js.array(Array.of_list(f3(pi.completions)));
        val victories = Js.array(Array.of_list(List.concat_map(f8, pp)));
        val goals = Js.array(Array.of_list(List.concat_map(f4, pp)));
    }];
    result
};

[@deriving enum]
type dia_option_case = 
    | End
    | PlayerTurn 
    | PuterTurn;

let js_dia_init() = Dialex.Example.myinit(); 

let js_dia_case(s : Dialex.Example.mystate) : int = {
    switch(Dialex.Dialogue.options(s)) {
    | End => dia_option_case_to_enum(End)
    | PlayerTurn(_) => dia_option_case_to_enum(PlayerTurn)
    | PuterTurn(_) => dia_option_case_to_enum(PuterTurn)
    }
}

let js_dia_opt_player(s : Dialex.Example.mystate) : jsarray(jsarray(Js.t(Js.js_string))) = {
    let js_opt((o, _) : (Dialex.Dialogue.text, Dialex.Example.mystate)) : Js.t(Js.js_string) = switch(o) {
        | S(s) => Js.string(s) 
    };
    switch( Dialex.Dialogue.options(s)) {
    | PlayerTurn(options1, options2) => 
        let js_options1 = List.map(js_opt, options1);
        let js_options2 = List.map(js_opt, options2);
        Js.array(Array.of_list([Js.array(Array.of_list(js_options1)), Js.array(Array.of_list(js_options2))]))
    | _ => failwith("wrong dialogue case")
    }
}

type select_type = Js.t({. 
    state:  Js.readonly_prop(Dialex.Example.mystate), 
    choice : Js.readonly_prop(int),
});

type hidden_select_type = Js.t({. 
    state:  Js.readonly_prop(Dialex.Example.mystate), 
    choice : Js.readonly_prop(Js.t(Js.js_string)),
});

type enaction_type = Js.t({. 
    state:  Js.readonly_prop(Dialex.Example.mystate), 
    signal : Js.readonly_prop(Js.t(Js.js_string)),
});

let js_dia_opt_player_select(s : select_type) : Dialex.Example.mystate = {
    switch(Dialex.Dialogue.options(s##.state)) {
    | PlayerTurn(options, _) => 
        let (_, s') = List.nth(options, s##.choice);
        s'
    | _ => failwith("wrong dialogue case")
    }
}

let js_dia_opt_player_can_select_hidden(s : hidden_select_type) : Js.t(bool) = {
    switch(Dialex.Dialogue.options(s##.state)) {
    | PlayerTurn(_, options) => 
        switch(List.find_index(x => fst(x) == Dialex.Dialogue.S(Js.to_string(s##.choice)), options)) {
        | None => Js.bool(false)
        | Some(_) => Js.bool(true)
        }
    | _ => Js.bool(false)
    }
}

let js_dia_opt_player_select_hidden(s : hidden_select_type) : Dialex.Example.mystate = {
    switch(Dialex.Dialogue.options(s##.state)) {
    | PlayerTurn(_, options) => 
        switch(List.find_index(x => fst(x) == Dialex.Dialogue.S(Js.to_string(s##.choice)), options)) {
        | None => s##.state
        | Some(n) => snd(List.nth(options, n))
        }
    | PuterTurn(_) => print_endline("It's the computer's turn."); s##.state
    | End => print_endline("It's the end."); s##.state
    }
}

let js_dia_enact(s : enaction_type) : Dialex.Example.mystate = {
    switch(Js.to_string(s##.signal)) {
    | "solved" => Dialex.Dialogue.enact(s##.state, s => {count: s.count, solved: true})
    | _ => s##.state
    }
}

let js_dia_opt_puter(s : Dialex.Example.mystate) : (string, Dialex.Example.mystate) = {
    switch( Dialex.Dialogue.options(s)) {
    | PuterTurn(S(t), s') => (t, s')
    | _ => failwith("wrong dialogue case")
    }
}


let () = {
    Js.export("lex_test", js_lexer);
    Js.export("parse_test", js_parser);
    Js.export("dia_test_init", js_dia_init);
    Js.export("dia_test_case", js_dia_case);
    Js.export("dia_opt_player", js_dia_opt_player);
    Js.export("dia_opt_player_select", js_dia_opt_player_select);
    Js.export("dia_opt_player_can_select_hidden", js_dia_opt_player_can_select_hidden);
    Js.export("dia_opt_player_select_hidden", js_dia_opt_player_select_hidden);
    Js.export("dia_enact", js_dia_enact);
    Js.export("dia_opt_puter", js_dia_opt_puter);
}