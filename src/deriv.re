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
    let arrow_formation : (t, name) => result(t, error);
    let implies_introduction : (t, name) => result(t, error);
    let implies_elimination : (t, tm) => result(t, error);
    let forall_introduction : (t, name) => result(t, error);
    let forall_elimination : (t, name, tm, tm, tm) => result(t, error);
    let pi_introduction : t => result(t, error);
    let ap : (t, name, tm, tm) => result(t, error);

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
        | J(Cons(c, _, _, _), ty_goal) when equiv(ty_goal, wk(ty)) => 
            Ok([J(c, ty)])
        | _ => Error("weaken failure")
        }
    })

    let hyp_prop (s : t, x : int) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, ty) => 
            let* found = lookup_index_prop(c, x);
            if (equiv(found, ty)) Ok([]) else Error(
                "hyp failure: " 
                ++ string_of_term(c, found)
                ++ " ≠ "
                ++ string_of_term(c, ty)
            )
        }
    })

    let hyp_typ (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Var(x), ty)) => 
            let* found = lookup_index_typ(c, x);
            if (equiv(found, ty)) Ok([]) else Error(
                "hyp failure: " 
                ++ text_of_var(c, x, x) 
                ++ " : "
                ++ string_of_term(c, found)
                ++ " ≠ "
                ++ string_of_term(c, ty)
            )
        | _ => Error("hyp failure: goal not of the form `x : _`")
        }
    })


    let in_formation (s : t, ty2 : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(In(a, ty1), Typ)) => {
            Ok([J(c, In(ty1, Typ)), J(c, In(a, ty2))])
        }
        | _ => Error("in_formation failure")
        }
    })

    let cut (s : t, x : name, ty1 : tm)  : result(t, error) = refine(s, j => {
        let (c, ty2) = pair_of_judgment(j);
        Ok([J(c, ty1), J(Cons(c, x, ty1, Prop), wk(ty2))])
    })

    let prop_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Prop, Typ)) => Ok([])
        | _ => Error("prop_formation failure")
        }
    })

    let typ_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Typ, Typ)) => Ok([])
        | _ => Error("typ_formation failure")
        }
    })

    let arrow_formation (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Arrow(Implies, _, ty1, ty2), Typ)) => Ok([J(c, In(ty1, Prop)), J(Cons(c, x, ty1, Prop), In(ty2, Prop))])
        | J(c, In(Arrow(Forall, _, ty1, ty2), Typ)) => Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1, Typ), In(ty2, Prop))])
        | J(c, In(Arrow(Pi, _, ty1, ty2), Typ)) => Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1, Typ), In(ty2, Typ))])
        | J(c, In(Arrow(Guard, _, ty1, ty2), Typ)) => Ok([J(c, In(ty1, Prop)), J(Cons(c, x, ty1, Prop), In(ty2, Typ))])
        | _ => Error("arrow_formation failure")
        }
    })

    let implies_introduction (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(Implies, _, p1, p2)) => Ok([J(c, In(p1, Prop)), J(Cons(c, x, p1, Prop), p2)])
        | _ => Error("implies_introduction failure")
        }
    })

    let implies_elimination (s : t, p1 : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, p2) => 
            Ok([J(c, Arrow(Implies, "_", p1, wk(p2))), J(c, p1)])
        }
    })

    let forall_introduction (s : t, x : name) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(Forall, _, t1, p2)) => Ok([J(c, In(t1, Typ)), J(Cons(c, x, t1, Typ), p2)])
        | _ => Error("forall_introduction failure")
        }
    })

    let forall_elimination (s : t, x : name, t1 : tm, p2 : tm, a : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, m) when equiv(subst(a, p2), m)  => 
            Ok([J(c, Arrow(Forall, x, t1, p2)), J(c, In(a, t1))])
        | _ => failwith("forall_elimination failure")
        }
    })

    let pi_introduction (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Lam(x, ty1, a), Arrow(Pi, _, ty1', ty2))) when equiv(ty1, ty1') => 
            Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1, Typ), In(a, ty2))])
        | _ => Error("pi_introduction failure")
        }
    })

    // let arrow_elimination (s : t)  : result(t, error) = refine(s, j => {
    //     switch(j) {
    //     | J(Cons(c, x, ty_a), In(Unlam(x', t), ty_b)) when x == x' => Ok([J(c, In(t, Arrow(x, ty_a, ty_b)))])
    //     | _ => Error("arrow_elimination failure")
    //     }
    // })

    let ap (s : t, x : name, ty1 : tm, ty2 : tm) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Ap(_st, a1, a2), ty_expected)) => {
            let ty_found = subst(a2, ty2);
            if (equiv(ty_found, ty_expected))
                Ok([J(c, In(a1, Arrow(Pi, x, ty1, ty2))), J(c, In(a2, ty1))])
            else Error(
                "ap failure: found = " 
                ++ string_of_term(c, ty_found)
                ++ " ≠ "
                ++ string_of_term(c, ty_expected)
            )
        } 
        | J(c, ty) => Error(
            "ap failure: goal = " 
            ++ string_of_term(c, ty)
            ++ " ≠ `_ _ : _`"
        )
        }
    })
}

let goal(s : PartialDerivation.t) : (ctx, tm) = pair_of_judgment(Result.get_ok(PartialDerivation.focused(s)));