open Lang

let rec text_of_var(c : ctx, x : int, original : int) : string = switch(c) {
    | Cons(_, y, _, _) when x == 0 => y
    | Cons(c, y, _, _) when x > 0 => {
        let y' = text_of_var(c, x-1, original);
        if (y' == y) { y ++ " (shadowed)"} else y'
    }
    | _ => "!!" ++ string_of_int(original)
}

let show_indices = false;
// let show_indices = true;

let string_of_var(c : ctx, x : int) : string = {
    text_of_var(c, x, x) ++ (show_indices ? "." ++ string_of_int(x) : "")
}

// precedences:
let colon_prec = (5, 5)
let arrow_prec = (11, 10)
let lam_prec = (-1, 15)
let strictap_prec = (20, -1)
let ap_prec = (20, 21)

let rec prec_string_of_term(lp: int, rp : int, c : ctx, outer_a : tm) : string = {
    switch(outer_a) {
    | Prop => "prop"
    | Typ => "type"
    | In(a, ty) => {
        if (lp >= fst(colon_prec) || rp >= 5) { wrap(c, outer_a) } else {
            prec_string_of_term(lp, fst(colon_prec), c, a) ++ " : " ++ prec_string_of_term(snd(colon_prec), rp,c, ty)
        }
    }
    | Arrow(x, ty1, ty2) => 
        if (lp >= fst(arrow_prec) || rp >= snd(arrow_prec)) { wrap(c, outer_a) } else {
            ((x == "_") ? prec_string_of_term(lp, fst(arrow_prec), c, ty1) : "(" ++ x ++ " : " ++ prec_string_of_term(fst(colon_prec), 0, c, ty1) ++ ")")
            ++ " -> " ++ prec_string_of_term(snd(arrow_prec), rp, Cons(c, x, ty1, Typ), ty2) 
        }
    | Lam(x, ty, a) => 
        if (rp >= snd(lam_prec)) { wrap(c, outer_a) } else {
            ((x == "_") ? prec_string_of_term(lp, fst(lam_prec), c, ty) : "(" ++ x ++ " : " ++ prec_string_of_term(fst(colon_prec), 0, c, ty) ++ ")")
            ++ " => " ++ prec_string_of_term(snd(lam_prec), rp, Cons(c, x, ty, Typ), a) 
        }
    // | Unlam(x, a) => 
    //     if (lp >= fst(unlam_prec)) { wrap(c, outer_a) } else {
    //         prec_string_of_term(lp, fst(unlam_prec), tail_of_ctx(c), a) ++ "[" ++ x ++ "]"
    //     }
    | Var(x) => string_of_var(c, x)
    | Ap(Strict, a1, a2) => 
        if (lp >= fst(strictap_prec)) { wrap(c, outer_a) } else {
            prec_string_of_term(lp, fst(ap_prec), c, a1) ++ "[" ++ prec_string_of_term(snd(ap_prec), rp, c, a2) ++ "]"
        }
    | Ap(Lax, a1, a2) => 
        if (lp >= fst(ap_prec) || rp >= snd(ap_prec)) { wrap(c, outer_a) } else {
            prec_string_of_term(lp, fst(ap_prec), c, a1) ++ " " ++ prec_string_of_term(snd(ap_prec), rp, c, a2)
        }
    }

} and wrap(c : ctx, a : tm) : string = {
    "(" ++ string_of_term(c, a) ++ ")"
} and string_of_term(c : ctx, a : tm) : string = {
    prec_string_of_term(0, 0, c, a)
}

let ctx_prefix_of_assumption(x : name, a : assumption) : string = switch(a) {
    | Prop => "(" ++ x ++ ") "
    | Typ => x ++ " : "
}

let rec string_of_ctx_short(c : ctx) : string = switch(c) {
    | Empty => ""
    | Cons(Empty, x, ty, a) => ctx_prefix_of_assumption(x, a) ++ string_of_term(Empty, ty)
    | Cons(c, x, ty, a) => string_of_ctx_short(c) ++ ", " ++ ctx_prefix_of_assumption(x, a) ++ string_of_term(c, ty)
}

let string_of_judgment_short(j : judgment) : string = {
    switch(j) {
    | J(c, a, _) =>  string_of_ctx_short(c) ++ " |- " ++ string_of_term(c, a)
    }
}

let rec string_of_ctx(c : ctx) : string = switch(c) {
    | Empty => ""
    | Cons(Empty, x, ty, a) => ctx_prefix_of_assumption(x, a) ++ string_of_term(Empty, ty)
    | Cons(c, x, ty, a) => ctx_prefix_of_assumption(x, a) ++ string_of_term(c, ty) ++ ",\n" ++ string_of_ctx(c)
}

let string_of_judgment(j : judgment) : string = {
    switch(j) {
    | J(c, a, _) => 
        let s = string_of_term(c, a);
        let bar = String.make(String.length(s), '-');
        s ++ "\n" ++ bar ++ "\n" ++ string_of_ctx(c)
    }
}
