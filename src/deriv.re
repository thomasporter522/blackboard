open Lang
open Lang_printing

module PartialDerivation : {
    type t; 
    let init : judgment => t;
    let verify : (t, judgment) => bool;
    let focused : t => result(judgment, error);
    let skip : t => result(t, error);
    let swap : t => result(t, error);
    let weaken : (t, tm) => result(t, error);
    let hyp_prop : (t, int) => result(t, error);
    let hyp_typ : t => result(t, error);
    let in_formation : (t, tm) => result(t, error);
    let cut : (t, name, tm) => result(t, error);
    let prop_formation : t => result(t, error);
    let typ_formation : t => result(t, error);
    let prop_arrow_formation : (t, name) => result(t, error);
    let typ_arrow_formation : (t, name) => result(t, error);
    let implies_introduction : (t, name) => result(t, error);
    let implies_elimination : (t, tm) => result(t, error);
    let forall_introduction : (t, name) => result(t, error);
    let forall_elimination : (t, name, tm, tm, tm) => result(t, error);
    let pi_introduction : t => result(t, error);
    let ap : (t, name, tm, tm) => result(t, error);
    let guard_elimination : (t, name, tm) => result(t, error);

} = {
    type t = {
        skipped : list(judgment),
        focused : list(judgment),
        root : judgment
    }

    let init (j : judgment) : t = {
        skipped : [],
        focused : [j],
        root : j
    }

    let verify (s : t, j : judgment) = {
        s.focused == [] && s.root == j
    }

    let focused (s : t) : result(judgment, error) = {
        switch(s.focused) {
            | [h, ..._] => Ok(h)
            | [] => Error("nothing focused")
        }
    }

    let skip (s : t) : result(t, error) = {
        switch(s.focused) {
            | [h, ... t] => Ok({
                skipped: [h, ...s.skipped],
                focused: t,
                root: s.root
            })
            | [] => Error("nothing to skip")
        }
    }

    let swap (s : t) : result(t, error) = {
        switch(s.focused) {
            | [h1, h2, ... t] => Ok({
                skipped: s.skipped,
                focused: [h2, h1, ... t],
                root: s.root
            })
            | _ => Error("nothing to swap")
        }
    }


    let refine (s : t, f : judgment => result(list(judgment), error)) : result(t, error) = {
        switch(s.focused) {
            | [h, ... t] => 
                Result.map(fh => {
                    skipped: s.skipped,
                    focused: fh @ t,
                    root: s.root
                }, f(h))
            | [] => Error("nothing to refine")
        }
    }

    let weaken (s : t, ty : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(Cons(c, _, _), ty_goal, mode) when equiv(ty_goal, wk(ty)) => 
            Ok([J(c, ty, mode)])
        | _ => Error("weaken failure")
        }
    })

    let hyp_prop (s : t, x : int) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, p, _) =>
            let* found = lookup_index(c, x);
            if (equiv(found, p)) Ok([J(c, In(p, Prop), Red)]) else Error(
                "hyp failure: " 
                ++ string_of_term(c, normalize(found))
                ++ " ≠ "
                ++ string_of_term(c, normalize(p))
            )
        }
    })

    let hyp_typ (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Var(x), ty), _) => 
            let* found = lookup_index(c, x);
            if (equiv(found, ty)) Ok([J(c, In(ty, Typ), Red)]) else Error(
                "hyp failure: " 
                ++ text_of_var(c, x, x) 
                ++ ") : "
                ++ string_of_term(c, found)
                ++ " ≠ "
                ++ string_of_term(c, ty)
            )
        | _ => Error("hyp failure: goal not of the form `x : _`")
        }
    })


    let in_formation (s : t, ty2 : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(In(a, ty1), Prop), mode) => {
            Ok([J(c, In(ty1, Typ), mode), J(c, In(a, ty2), mode)])
        }
        | J(_, In(In(_), _), _) => Error("in_formation failure: not inhabiting prop")
        | J(_, In(_, _), _) => Error("in_formation failure: not membership of (_ : _)")
        | _ => Error("in_formation failure")
        }
    })

    let cut (s : t, x : name, ty1 : tm)  : result(t, error) = refine(s, j => {
        let (c, ty2, mode) = tuple_of_judgment(j);
        Ok([J(c, ty1, mode), J(Cons(c, x, ty1), wk(ty2), mode)])
    })

    let prop_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Prop, Typ), _) => Ok([])
        | _ => Error("prop_formation failure")
        }
    })

    let typ_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Typ, Typ), _) => Ok([])
        | _ => Error("typ_formation failure")
        }
    })

    let prop_arrow_formation (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Arrow(_, _, ty1, ty2), a2), mode) => Ok([J(c, In(ty1, Prop), Red), J(Cons(c, x, ty1), In(ty2, a2), mode)])
        | _ => Error("prop_arrow_formation failure")
        }
    })

    let typ_arrow_formation (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Arrow(_, _, ty1, ty2), a2), mode) => Ok([J(c, In(ty1, Typ), Red), J(Cons(c, x, ty1), In(ty2, a2), mode)])
        | _ => Error("typ_arrow_formation failure")
        }
    })

    let implies_introduction (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(_, _, p1, p2), mode) => Ok([J(c, In(p1, Prop), Red), J(Cons(c, x, p1), p2, mode)])
        | _ => Error("implies_introduction failure")
        }
    })

    let implies_elimination (s : t, p1 : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, p2, mode) => 
            Ok([J(c, Arrow(Weak, "_", p1, wk(p2)), mode), J(c, p1, mode)])
        }
    })

    let forall_introduction (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(_, _, t1, p2), mode) => Ok([J(c, In(t1, Typ), Red), J(Cons(c, x, t1), p2, mode)])
        | _ => Error("forall_introduction failure")
        }
    })

    let forall_elimination (s : t, x : name, t1 : tm, p2 : tm, a : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, goal, mode) when equiv(subst(a, p2), goal)  => 
            Ok([J(c, Arrow(Weak, x, t1, p2), mode), J(c, In(a, t1), mode)])
        | J(c, goal, _) => 
            Error("forall_elimination failure: found = " 
                ++ string_of_term(c, subst(a, p2))
                ++ " ≠ "
                ++ string_of_term(c, goal))
        }
    })

    let pi_introduction (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Lam(x, ty1, a), Arrow(_, _, ty1', ty2)), mode) when equiv(ty1, ty1') => 
            Ok([J(c, In(ty1, Typ), Red), J(Cons(c, x, ty1), In(a, ty2), mode)])
        | J(c, In(Lam(_, ty1, _), Arrow(_, _, ty1', _)), _) => 
            Error("pi_introduction failure: found = " 
                ++ string_of_term(c, ty1)
                ++ " ≠ "
                ++ string_of_term(c, ty1'))
        | _ => Error("pi_introduction failure")
        }
    })

    // let arrow_elimination (s : t)  : result(t, error) = refine(s, j => {
    //     switch(j) {
    //     | J(Cons(c, x, ty_a), In(Unlam(x', t), ty_b)) when x == x' => Ok([J(c, In(t, Arrow(x, ty_a, ty_b)))])
    //     | _ => Error("arrow_elimination failure")
    //     }
    // })

    // strict application in blue mode demands a strong arrow
    let ap_strength(st : strictness, m : mode) : strength = switch(st, m) {
        | (Lax, _) => Weak
        | (Strict, Red) => Weak 
        | (Strict, Blue) => Strong
    }

    let ap (s : t, x : name, ty1 : tm, ty2 : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Ap(st, a1, a2), ty_expected), mode) when (mode == Red || st == Lax) => {
            let ty_found = subst(a2, ty2);
            if (equiv(ty_found, ty_expected))
                Ok([J(c, In(a1, Arrow(ap_strength(st, mode), x, ty1, ty2)), mode), J(c, In(a2, ty1), mode)])
            else Error(
                "ap failure: found = " 
                ++ string_of_term(c, ty_found)
                ++ " ≠ "
                ++ string_of_term(c, ty_expected)
            )
        } 
        | J(_, In(Ap(st, _, _), _), mode) when !(mode == Red || st == Lax) => 
            Error("no strict applications except in assumptions!")
        | J(c, ty, _) => Error(
            "ap failure: goal = " 
            ++ string_of_term(c, ty)
            ++ " ≠ `_ _ : _`"
        )
        }
    })

    let guard_elimination (s : t, x : name, p : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Unguard(a), t), mode) => 
            Ok([J(c, p, mode), J(c, In(a, Arrow(Weak, x, p, wk(t))), mode)])
        | J(_) => 
            Error("guard_elimination failure")
        }
    })
}

let goal(s : PartialDerivation.t) : judgment = Result.get_ok(PartialDerivation.focused(s));
let goal_tuple(s : PartialDerivation.t) : (ctx, tm, mode) = tuple_of_judgment(goal(s));
let goal_ctx(s : PartialDerivation.t) : ctx = ctx_of_judgment(goal(s));
let goal_type(s : PartialDerivation.t) : tm = type_of_judgment(goal(s));
let goal_mode(s : PartialDerivation.t) : mode = mode_of_judgment(goal(s));

let string_of_goal_ctx(s : PartialDerivation.t) = string_of_ctx(goal_ctx(s));
let string_of_goal_type(s : PartialDerivation.t) = string_of_term(goal_ctx(s), goal_type(s));
