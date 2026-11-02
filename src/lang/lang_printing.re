open Term

let string_of_index(Index(x, y) : index) = "!!" ++ string_of_int(x) ++ "." ++ string_of_int(y)

let rec text_of_var_tele(te : tele, y : int, original : index) : string = switch(te) {
    | ConsP(_, Name(z), _) when y == 0 => z
    | ConsP(te, _, _) when y > 0 => text_of_var_tele(te, y-1, original)
    | ConsT(_, Name(z), _, _) when y == 0 => z
    | ConsT(te, _, _, _) when y > 0 => text_of_var_tele(te, y-1, original)
    | _ => "!!" ++ string_of_index(original)
}

let rec text_of_index(c : ctx, i : index, original : index) : string = switch(c, i) {
    | (Cons(_, te), Index(0, y)) => text_of_var_tele(te, y, original)
    | (Cons(c, _), Index(x, y)) when x > 0 => text_of_index(c, Index(x-1, y), original)
    | _ => "!!" ++ string_of_index(original)
}

let show_indices = false;
// let show_indices = true;

let string_of_var(c : ctx, i : index) : string = {
    text_of_index(c, i, i) ++ (show_indices ? "." ++ string_of_index(i) : "")
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
            prec_string_of_term(lp, fst(colon_prec), c, a) ++ " :: " ++ prec_string_of_term(snd(colon_prec), rp,c, ty)
        }
    }
    | Arrow(te, t) => 
        if (lp >= fst(arrow_prec) || rp >= snd(arrow_prec)) { wrap(c, outer_a) } else {
            string_of_tele(Cons(c, te), te) ++ " -> " ++ prec_string_of_term(snd(arrow_prec), rp, Cons(c, te), t) 
        }
    | Ap(i, Empty) => string_of_var(c, i)
    | Ap(i, s) => 
        if (lp >= fst(ap_prec) || rp >= snd(ap_prec)) { wrap(c, outer_a) } else {
            string_of_var(c, i) ++ " " ++ string_of_subst(c, s)
        }
    | Nonsense => "<some nonsense>"
    }

} and wrap(c : ctx, a : tm) : string = {
    "(" ++ string_of_term(c, a) ++ ")"
} and string_of_term(c : ctx, a : tm) : string = {
    prec_string_of_term(0, 0, c, a)
}

and string_of_tele(c : ctx, te : tele) : string = switch(te) {
    | Empty => ""
    | ConsP(te, Name(z), p) => string_of_tele(c, te) ++ (te == Empty ? "" : " ")  ++ "(" ++ z ++ " : " ++ string_of_term(c, p) ++ ")"
    | ConsT(te, Name(z), te1, ty) => string_of_tele(c, te) ++ (te == Empty ? "" : " ") ++ "(" ++ z ++ string_of_tele(Cons(c, te1), te1) ++ " : " ++ string_of_term(c, ty) ++ ")"
}

and string_of_subst(c : ctx, s : subst) : string = switch(s) {
    | Empty => ""
    | Cons(s', Name(z), te, t) => string_of_subst(c, s') ++ (te == Empty ? "" : " ") ++ "("  ++ z ++ " := " ++ string_of_term(c, t) ++ ")"
}

let rec string_of_ctx(c : ctx) : string = switch(c) {
    | Empty => ""
    | Cons(c', te) => string_of_ctx(c') ++ (c' == Empty ? "" : ",\n")  ++ string_of_tele(Cons(c', te), te)
}

let rec strings_of_ctx(c : ctx) : list(string) = switch(c) {
    | Empty => []
    | Cons(c', te) => strings_of_ctx(c') @ [string_of_tele(Cons(c', te), te)]
}

let strings_of_judgment(j : judgment) : (list(string), string) = {
    switch(j) {
    | J(c, a) => 
        let s = string_of_term(c, a);
        (strings_of_ctx(c), s)
    }
}

let string_of_judgment(j : judgment) : string = {
    let (c, s) = strings_of_judgment(j);
    let bar = String.make(String.length(s), '-');
    String.concat(",\n", c) ++ "\n" ++ bar ++ "\n" ++ s
}

let string_of_error(e : ranged_error) : string = e.message