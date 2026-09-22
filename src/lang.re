
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
let smartvarmap (a : tm, x : int, f : int => int) : tm = {
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

// replaces all occurrences of [x] with [a], downshifting all vars > x.
let rec subst (a1 : tm, a : tm, x : int) : tm = {
    switch(a1) {
    | Typ => Typ
    | In(a1, ty) => In(subst(a1, a, x), subst(ty, a, x))
    | Arrow(y, ty1, ty2) => Arrow(y, subst(ty1, a, x), subst(ty2, shift(a, 0), x+1))
    | Var(y) when y == x => a 
    | Var(y) when y > x => Var(y-1)
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
