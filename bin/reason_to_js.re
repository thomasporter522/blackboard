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

let () = {
    Js.export("lex_test", js_lexer);
}