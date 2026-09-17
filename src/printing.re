open Core
open Demo

let show_indices = false;


let rec text_of_var(c : ctx, x : int) : string = switch(c) {
    | Cons(_, y, _) when x == 0 => y
    | Cons(c, y, _) when x > 0 => {
        let y' = text_of_var(c, x-1);
        if (y' == y) { y ++ " (shadowed)"} else y'
    }
    | _ => failwith("impossible: string of var")
}

let string_of_var(c : ctx, x : int) : string = {
    text_of_var(c, x) ++ (show_indices ? "." ++ string_of_int(x) : "")
}

let rec string_of_term(c : ctx, a : tm) : string = {
    switch(a) {
    | Typ => "type"
    | In(a, ty) => string_of_term(c, a) ++ " : " ++ string_of_term(c, ty)
    | Arrow(x, ty1, ty2) => 
        ((x == "_") ? string_of_term(c, ty1) : "(" ++ x ++ " : " ++ string_of_term(c, ty1) ++ ")")
        ++ " -> " ++ string_of_term(Cons(c, x, ty1), ty2)
    | Var(x) => string_of_var(c, x)
    | Ap(a1, a2) => string_of_term(c, a1) ++ " " ++ string_of_term(c, a2)
    }
}

let rec string_of_ctx(c : ctx) : string = switch(c) {
    | Empty => ""
    | Cons(Empty, x, ty) => x ++ " : " ++ string_of_term(c, ty)
    | Cons(c, x, ty) => string_of_ctx(c) ++ ", " ++ x ++ " : " ++ string_of_term(c, ty)
}

let string_of_judgment_short(j : judgment) : string = {
    switch(j) {
    | J(c, a) =>  string_of_ctx(c) ++ " |- " ++string_of_term(c, a)
    }
}

let string_of_report(r : demo_check_report) : string = {
    if (r.open_goals == [] && r.errors == []) "Proven!" else
    "Goals:\n\n" ++ String.concat("\n", List.map(string_of_judgment_short, r.open_goals))
    ++ "\n\nErrors:\n\n" ++ String.concat("\n", r.errors)
}
