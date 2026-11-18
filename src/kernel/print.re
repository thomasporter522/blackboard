open Meta
open Term


let string_of_index(Index(x, y) : term_index) = "!!" ++ string_of_int(x) ++ "." ++ string_of_int(y)

let rec text_of_var_tele(te : tele, y : int, original : term_index) : string = switch(te) {
    | ConsP(te, _, _) => text_of_var_tele(te, y, original)
    | ConsT(_, Name(z), _, _) when y == 0 => z
    | ConsT(te, Name(z'), _, _) when y > 0 => 
        let z = text_of_var_tele(te, y-1, original);
        z ++ (z == z' ? " (shadowed)" : "")
    | _ => "!!" ++ string_of_index(original)
}

let rec shadowed(z : string, te) = switch(te) {
    | EmptyTele => false 
    | ConsP(te, _, _) => shadowed(z, te)
    | ConsT(te, Name(z'), _, _) => z == z' || shadowed(z, te)
}

let rec text_of_index(c : ctx, i : term_index, original : term_index) : string = switch(c, i) {
    | (Cons(_, te), Index(0, y)) => text_of_var_tele(te, y, original)
    | (Cons(c, te), Index(x, y)) when x > 0 => 
        let z = text_of_index(c, Index(x-1, y), original);
        z ++ (shadowed(z, te) ? " (shadowed)" : "")
    | _ => "!!" ++ string_of_index(original)
}

let show_indices = false;
// let show_indices = true;

let string_of_name(Name(x)) = x;

let string_of_var(c : ctx, i : term_index) : string = {
    text_of_index(c, i, i) ++ (show_indices ? "." ++ string_of_index(i) : "")
}

// precedences:
let colon_prec = (11, 10)
let semicolon_prec = (11, 10)
let in_prec = (20, 21)
let arrow_prec = (11, 10)
let ap_prec = (20, 21)
let comma_prec = (5, 5)

let rec prec_string_of_term(lp: int, rp : int, c : ctx, outer_a : tm) : string = {
    switch(outer_a) {
    | Prop => "prop"
    | Typ => "type"
    | In(_) when lp >= fst(in_prec) || rp >= snd(in_prec) =>  wrap(c, outer_a)
    | In(a, ty) => prec_string_of_term(lp, fst(in_prec), c, a) ++ " :: " ++ prec_string_of_term(snd(in_prec), rp,c, ty)
    | Arrow(_) when (lp >= fst(arrow_prec) || rp >= snd(arrow_prec)) => wrap(c, outer_a)
    | Arrow(te, t) => string_of_tele(lp, fst(arrow_prec), Cons(c, te), te) ++ " -> " ++ prec_string_of_term(snd(arrow_prec), rp, Cons(c, te), t) 
    | Ap(i, EmptySubst) => string_of_var(c, i)
    | Ap(_) when lp >= fst(ap_prec) || rp >= snd(ap_prec) => wrap(c, outer_a)
    | Ap(i, s) => string_of_var(c, i) ++ " " ++ string_of_subst(c, s)
    | Meta(_, m) => "{" ++ Meta.string_of_meta(m) ++ "}"
    | Nonsense => "<some nonsense>"
    }

} and wrap(c : ctx, a : tm) : string = {
    "(" ++ string_of_term(c, a) ++ ")"
} and string_of_term(c : ctx, a : tm) : string = {
    prec_string_of_term(0, 0, c, a)
}

and string_of_tele_p(lp, rp, z, c, p) = {
    if(z == "_") { 
        if(lp >= snd(ap_prec)) { wrap_tele_p(z, c, p) } else
        prec_string_of_term(lp, rp, c, p)
    } 
    else if(lp >= fst(semicolon_prec) || rp >= snd(semicolon_prec)) { wrap_tele_p(z, c, p) }
    else { 
        z ++ " ; " ++ prec_string_of_term(snd(semicolon_prec), rp, c, p)
    }
}
and wrap_tele_p(z, c, p) =
    "(" ++ string_of_tele_p(0, 0, z, c, p) ++ ")"

and string_of_tele_t(lp: int, rp : int, z, te1, c, ty) = {
    if(lp >= fst(colon_prec) || rp >= snd(colon_prec)) { wrap_tele_t(z, te1, c, ty) } else
    z ++ (te1 == EmptyTele ? "" : " ") ++ string_of_tele(snd(ap_prec), fst(colon_prec), Cons(c, te1), te1) ++ " : " ++ prec_string_of_term(snd(colon_prec), rp, Cons(c, te1), ty)
}

and wrap_tele_t(z, te1, c, ty) =
    "(" ++ string_of_tele_t(0, 0, z, te1, c, ty) ++ ")"

and string_of_tele(lp: int, rp : int, c : ctx, te : tele) : string = switch(te) {
    | EmptyTele => ""
    | ConsP(EmptyTele, Name(z), p) => string_of_tele_p(lp, rp, z, c, p)
    | ConsP(te', Name(z), p) => 
        if(lp >= fst(comma_prec) || rp >= snd(comma_prec)) { wrap_tele(c, te) } else
        string_of_tele(lp, fst(comma_prec), c, te') ++ ", "  ++ string_of_tele_p(snd(comma_prec), rp, z, c, p)
    | ConsT(EmptyTele, Name(z), te1, ty) => string_of_tele_t(lp, rp, z, te1, c, ty)
    | ConsT(te', Name(z), te1, ty) => 
        if(lp >= fst(comma_prec) || rp >= snd(comma_prec)) { wrap_tele(c, te) } else
        string_of_tele(lp, fst(comma_prec), c, te') ++ ", " ++ string_of_tele_t(snd(comma_prec), rp, z, te1, c, ty)
}

and wrap_tele(c : ctx, te : tele) : string = "(" ++ string_of_tele(0, 0, c, te) ++ ")"

and string_of_subst_args(xs : subst_args) = switch(xs) {
    | EmptySubstArgs => ""
    | ConsSubstArgs(xs', x) => string_of_subst_args(xs') ++ " " ++ string_of_name(x)
}

and string_of_sub(z, c, args : subst_args, t) = {
    let te = tele_of_subst_args(args);
    if(z == "_") { 
        string_of_term(Cons(c, te), t)
    } else { 
        "("  ++ z
        ++ string_of_subst_args(args)
        ++ " := " 
        ++ string_of_term(Cons(c, te), t) 
        ++ ")"
    }
}

and string_of_subst(c : ctx, s : subst) : string = switch(s) {
    | EmptySubst => ""
    | ConsSubst(s', Name(z), args, t) => 
        string_of_subst(c, s') 
        ++ (s' == EmptySubst ? "" : " ") 
        ++ string_of_sub(z, c, args, t)
}

let rec string_of_ctx(c : ctx) : string = switch(c) {
    | Empty => ""
    | Cons(c', te) => string_of_ctx(c') ++ (c' == Empty ? "" : ",\n")  ++ string_of_tele(0, 0, Cons(c', te), te)
}

let rec strings_of_ctx(c : ctx) : list(string) = switch(c) {
    | Empty => []
    | Cons(c', te) => strings_of_ctx(c') @ [string_of_tele(0, 0, Cons(c', te), te)]
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