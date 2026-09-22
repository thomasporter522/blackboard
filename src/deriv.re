open Lang
open Lang_printing

module PartialDerivation : {
    type t; 
    let init : judgment => t;
    let verify : (t, judgment) => bool;
    let focused : t => result(judgment, error);
    let skip : t => result(t, error);
    let swap : t => result(t, error);
    let weaken : t => result(t, error);
    let hyp : t => result(t, error);
    let in_formation : (t, tm) => result(t, error);
    let in_elimination : (t, tm) => result(t, error);
    let cut : (t, name, tm) => result(t, error);
    let typ_formation : t => result(t, error);
    let arrow_formation : (t, name) => result(t, error);
    let ap : (t, name, tm, tm) => result(t, error);
    let arrow_introduction : (name, t) => result(t, error);

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

    let weaken (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(Cons(c, _, _), ty) when no_x(ty, 0) => 
            Ok([J(c, downshift(ty, 0))])
        | _ => Error("weaken failure")
        }
    })

    let hyp (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Var(x), ty)) => 
            let found = lookup_index(c, x);
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

    let in_elimination (s : t, a : tm)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, ty) => Ok([J(c, In(a, ty))])
        }
    })

    let cut (s : t, x : name, ty1 : tm)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, ty2) => Ok([J(c, ty1), J(Cons(c, x, ty1), shift(ty2, 0))])
        }
    })

    let typ_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(_, In(Typ, Typ)) => Ok([])
        | _ => Error("typ_formation failure")
        }
    })

    let arrow_formation (s : t, x : name)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Arrow(_x, ty1, ty2), Typ)) => Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1), In(ty2, Typ))])
        | _ => Error("arrow_formation failure")
        }
    })

    let ap (s : t, x : name, ty1 : tm, ty2 : tm)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Ap(a1, a2), ty_expected)) => {
            let ty_found = subst(ty2, a2, 0);
            if (equiv(ty_found, ty_expected))
                Ok([J(c, In(a1, Arrow(x, ty1, ty2))), J(c, In(a2, ty1))])
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

    let arrow_introduction (x : name, s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(_, ty1, ty2)) => Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1), ty2)])
        | _ => Error("arrow_introduction failure")
        }
    })
}