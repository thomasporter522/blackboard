
type name = string;

type tm = 
    | Typ 
    | In(tm, tm)
    | Arrow(name, tm, tm)
    | Var(int)
    | Ap(tm, tm);

type ctx = 
    | Empty 
    | Cons(ctx, name, tm);

type error = string;

let rec index_of_name(c : ctx, x : name) : result(int, error) = {
    switch(c, x) {
    | (Cons(_, y, _), x) when y == x => Ok(0)
    | (Cons(c, _, _), x) => Result.map(i => 1+i, index_of_name(c, x))
    | _ => Error("Context lookup unbound name")
    }
}

// alpha equivalence
let rec equiv(a1 : tm, a2 : tm) : bool = {
    switch(a1, a2) {
    | (Typ, Typ) => true 
    | (In(a1, a2), In(a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
    | (Arrow(_, a1, a2), Arrow(_, a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
    | (Var(x1), Var(x2)) => x1 == x2
    | (Ap(a1, a2), Ap(a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
    | _ => false
    }
}

// increments each variable in [a] greater than or equal to [n]
let rec shift (a : tm, x : int) : tm = {
    switch(a) {
    | Typ => Typ
    | In(a, ty) => In(shift(a, x), shift(ty, x))
    | Arrow(y, ty1, ty2) => Arrow(y, shift(ty1, x), shift(ty2, x+1))
    | Var(y) when y >= x => Var(y+1)
    | Var(y) => Var(y)
    | Ap(a1, a2) => Ap(shift(a1, x), shift(a2, x))
    }
}

// replaces all occurrences of [x] with [a]
let rec subst (a1 : tm, a : tm, x : int) : tm = {
    switch(a1) {
    | Typ => Typ
    | In(a1, ty) => In(subst(a1, a, x), subst(ty, a, x))
    | Arrow(y, ty1, ty2) => Arrow(y, subst(ty1, a, x), subst(ty2, shift(a, 0), x+1))
    | Var(y) when x == y => a 
    | Var(y) => Var(y)
    | Ap(a1, a2) => Ap(subst(a1, a, x), subst(a2, a, x))
    }
}

let rec lookup_index (c : ctx, x : int) : tm = {
    switch(c, x) {
    | (Cons(_, _, t), 0) => shift(t, 0)
    | (Cons(c, _, _), x) when x > 0 => shift(lookup_index(c, x-1), 0)
    | _ => failwith("Context lookup out of bounds")
    }
}

// let rec lookup_name (c : ctx, x : name) : tm = {
//     switch(c, x) {
//     | (Cons(c, y, t), x) when y == x => shift(t, 0)
//     | (Cons(c, _, _), x) => shift(lookup_name(c, x), 0)
//     | _ => failwith("Context lookup unbound name")
//     }
// }

type judgment = J(ctx, tm);

let ctx_of_judgment (j : judgment) : ctx = switch(j) {
    | J(c, _) => c
}

module PartialDerivation : {
    type t; 
    let init : judgment => t;
    let verify : (t, judgment) => bool;
    let focused : t => result(judgment, error);
    let skip : t => result(t, error);
    let hyp : (t, int) => result(t, error);
    let in_formation : (t, tm) => result(t, error);
    let in_elimination : (t, tm) => result(t, error);
    let cut : (t, name, tm) => result(t, error);
    let typ_formation : t => result(t, error);
    let arrow_formation : t => result(t, error);
    let ap : (t, name, tm, tm) => result(t, error);
    let arrow_introduction : t => result(t, error);

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

    let hyp (s : t, x : int) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, ty) => 
            let found = lookup_index(c, x);
            if (equiv(found, ty)) Ok([]) else Error("hyp failure")
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

    let arrow_formation (s : t)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Arrow(x, ty1, ty2), Typ)) => Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1), In(ty2, Typ))])
        | _ => Error("arrow_formation failure")
        }
    })

    let ap (s : t, x : name, ty1 : tm, ty2 : tm)  : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, In(Ap(a1, a2), ty2_sub)) when subst(ty2, a2, 0) == ty2_sub => 
            Ok([J(c, In(a1, Arrow(x, ty1, ty2))), J(c, In(a2, ty1))])
        | _ => Error("ap failure")
        }
    })

    let arrow_introduction (s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(x, ty1, ty2)) => Ok([J(Cons(c, x, ty1), ty2)])
        | _ => Error("arrow_introduction failure")
        }
    })
}