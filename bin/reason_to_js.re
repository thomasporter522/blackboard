open Js_of_ocaml

let js_lexer(s : string) : Js.t(Js.js_array(Js.t(Js.js_array(Js.number_t)))) = {
    let thing = Lytr.Blackboard.lex_test(s);
    let f(x : (int, int, string)) : Js.t(Js.js_array(Js.number_t)) = {
        let(a, b, _) = x;
        let ar = Array.of_list([Js.int32(Int32.of_int(a)), Js.int32(Int32.of_int(b))]);
        Js.array(ar)
    };
    Js.array(Array.of_list(List.map(f, thing)))
}

let () = Js.export("lex_test", js_lexer);