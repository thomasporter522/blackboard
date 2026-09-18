
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

// applies f to each variable in [a] greater than or equal to [n]
let rec varmap (a : tm, x : int, f : int => int) : tm = {
    switch(a) {
    | Typ => Typ
    | In(a, ty) => In(varmap(a, x, f), varmap(ty, x, f))
    | Arrow(y, ty1, ty2) => Arrow(y, varmap(ty1, x, f), varmap(ty2, x+1, f))
    | Var(y) when y >= x => Var(f(y))
    | Var(y) => Var(y)
    | Ap(a1, a2) => Ap(varmap(a1, x, f), varmap(a2, x, f))
    }
}

// smartapplies f to each variable in [a] greater than or equal to [n]
let rec smartvarmap (a : tm, x : int, f : int => int) : tm = {
    switch(a) {
    | Typ => Typ
    | In(a, ty) => In(varmap(a, x, f), varmap(ty, x, f))
    | Arrow(y, ty1, ty2) => Arrow(y, varmap(ty1, x, f), varmap(ty2, x+1, y => f(y-1)+1))
    | Var(y) when y >= x => Var(f(y))
    | Var(y) => Var(y)
    | Ap(a1, a2) => Ap(varmap(a1, x, f), varmap(a2, x, f))
    }
}

// increments each variable in [a] greater than or equal to [n]
let shift (a : tm, x : int) : tm = varmap(a, x, n => n+1)

// decrements each variable in [a] greater than or equal to [n]
let downshift (a : tm, x : int) : tm = varmap(a, x, n => n-1)

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

let rec no_x (a : tm, x : int) : bool = {
    switch(a) {
    | Typ => true
    | In(a, ty) => no_x(a, x) && no_x(ty, x)
    | Arrow(_, ty1, ty2) => no_x(ty1, x) && no_x(ty2, x+1) 
    | Var(y) => y != x
    | Ap(a1, a2) => no_x(a1, x) && no_x(a2, x)
    }
}

type judgment = J(ctx, tm);

let pair_of_judgment (j : judgment) : (ctx, tm) = switch(j) {
    | J(c, ty) => (c, ty)
}

let ctx_of_judgment (j : judgment) : ctx = fst(pair_of_judgment(j))
let typ_of_judgment (j : judgment) : tm = snd(pair_of_judgment(j))

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
            if (equiv(found, ty)) Ok([]) else Error("hyp failure")
        | _ => Error("hyp failure")
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
        | J(c, In(Ap(a1, a2), ty2_sub)) when subst(ty2, a2, 0) == shift(ty2_sub,0) => 
            Ok([J(c, In(a1, Arrow(x, ty1, ty2))), J(c, In(a2, ty1))])
        | _ => Error("ap failure")
        }
    })

    let arrow_introduction (x : name, s : t) : result(t, error) = refine(s, j => {
        switch(j) {
        | J(c, Arrow(_, ty1, ty2)) => Ok([J(c, In(ty1, Typ)), J(Cons(c, x, ty1), ty2)])
        | _ => Error("arrow_introduction failure")
        }
    })
}