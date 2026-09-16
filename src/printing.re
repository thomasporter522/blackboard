open Core
open Demo

// todo: use names
let rec string_of_term(a : tm) : string = {
    switch(a) {
    | Typ => "type"
    | In(a, ty) => string_of_term(a) ++ " : " ++ string_of_term(ty)
    | Arrow(x, ty1, ty2) => "(" ++ x ++ " : " ++ string_of_term(ty1) ++ ") -> " ++ string_of_term(ty2)
    | Var(x) => "v" ++ string_of_int(x)
    | Ap(a1, a2) => string_of_term(a1) ++ " " ++ string_of_term(a2)
    }
}

let string_of_judgment_short(j : judgment) : string = {
    switch(j) {
    | J(_c, a) => string_of_term(a) //++ " -| " ++ string_of_ctx(c)
    }
}

let string_of_report(r : demo_check_report) : string = {
    if (r.open_goals == [] && r.errors == []) "Proven!" else
    "Goals:\n\n" ++ String.concat("\n", List.map(string_of_judgment_short, r.open_goals))
    ++ "\n\nErrors:\n\n" ++ String.concat("\n", r.errors)
}
