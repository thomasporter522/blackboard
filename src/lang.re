
type name = string;

type arrow = 
    | Implies
    | Forall 
    | Pi 
    | Guard

type strictness = 
    | Strict 
    | Lax

type tm = 
    | Prop
    | Typ 
    | In(tm, tm)
    | Arrow(arrow, name, tm, tm)
    | Lam(name, tm, tm)
    // | Unlam(name, tm)
    | Var(int)
    | Ap(strictness, tm, tm);

type assumption = 
    | Prop 
    | Typ

type ctx = 
    | Empty 
    | Cons(ctx, name, tm, assumption);

type error = string;

let ( let* ) = (x: result('a, 'b), f: 'a => result('c, 'b)): result('c, 'b) =>
  switch (x) {
  | Ok(x) => f(x)
  | Error(e) => Error(e)
  };

let ( let! ) = (x: result('a, 'b), f: 'b => result('a, 'b)): result('a, 'b) =>
  switch (x) {
  | Ok(x) => Ok(x)
  | Error(e) => f(e)
  };

let rec index_of_name(c : ctx, x : name) : result(int, error) = {
    switch(c, x) {
    | (Cons(_, y, _, _), x) when y == x => Ok(0)
    | (Cons(c, _, _, _), x) => Result.map(i => 1+i, index_of_name(c, x))
    | _ => Error("Context lookup unbound name")
    }
}

let tail_of_ctx(c : ctx) : ctx = switch(c) {
    | Empty => failwith("tail of empty context")
    | Cons(c', _, _, _) => c'
}

let assumption_of_arrow(a : arrow) : assumption = switch(a) {
    | Implies => Prop
    | Forall => Typ
    | Pi => Typ
    | Guard => Prop
}

// alpha equivalence
let rec equiv(a1 : tm, a2 : tm) : bool = {
    switch(a1, a2) {
    | (Prop, Prop) => true 
    | (Typ, Typ) => true 
    | (In(a1, a2), In(a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
    | (Arrow(a, _, a1, a2), Arrow(a', _, a3, a4)) => a == a' && equiv(a1, a3) && equiv(a2, a4)
    | (Lam(_, a1, a2), Lam(_, a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
    // | (Unlam(_, a1), Unlam(_, a3)) => equiv(a1, a3)
    | (Var(x1), Var(x2)) => x1 == x2
    | (Ap(s1, a1, a2), Ap(s2, a3, a4)) => s1 == s2 && equiv(a1, a3) && equiv(a2, a4)
    | (Prop, _) => false
    | (Typ, _) => false
    | (In(_), _) => false
    | (Arrow(_), _) => false
    | (Lam(_), _) => false
    // | (Unlam(_), _) => false
    | (Var(_), _) => false
    | (Ap(_), _) => false
    }
}

let rec wknvar(n : int, m : int) : int = {
    if (n == 0) { m+1 } else
    if (n > 0 && m == 0) { 0 } else 
    { wknvar(0, wknvar(n-1, m-1))}
}

let rec wkn(n : int, a : tm) : tm = switch(a) {
    | Prop => Prop
    | Typ => Typ
    | In(a, ty) => In(wkn(n, a), wkn(n, ty))
    | Arrow(a, y, ty1, ty2) => Arrow(a, y, wkn(n, ty1), wkn(n+1, ty2))
    | Lam(y, ty, a) => Lam(y, wkn(n, ty), wkn(n+1, a))
    | Var(y) => Var(wknvar(n, y))
    | Ap(s, a1, a2) => Ap(s, wkn(n, a1), wkn(n, a2))
}

let wk(a : tm) : tm = wkn(0, a)

let rec substnvar(n : int, s : tm, m : int) : tm = {
    if (n == 0 && m == 0) { s } else
    if (n == 0 && m > 0) { Var(m-1) } else 
    if (n > 0 && m == 0) { Var(0) } else 
    { wkn(0, substnvar(n-1, s, m-1))}
}

let rec substn(n : int, s : tm, t : tm) : tm = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(a, ty) => In(substn(n, s, a), substn(n, s, ty))
    | Arrow(a, y, ty1, ty2) => Arrow(a, y, substn(n, s, ty1), substn(n+1, s, ty2))
    | Lam(y, ty, a) => Lam(y, substn(n, s, ty), substn(n+1, s, a))
    | Var(y) => substnvar(n, s, y)
    | Ap(r, a1, a2) => Ap(r, substn(n, s, a1), substn(n, s, a2))
}

let subst(s : tm, t : tm) : tm = substn(0, s, t)

// // applies f to each variable in [a] greater than or equal to [n]
// let rec varmap (a : tm, x : int, f : int => int) : tm = {
//     switch(a) {
//     | Typ => Typ
//     | In(a, ty) => In(varmap(a, x, f), varmap(ty, x, f))
//     | Arrow(y, ty1, ty2) => Arrow(y, varmap(ty1, x, f), varmap(ty2, x+1, f))
//     | Var(y) when y >= x => Var(f(y))
//     | Var(y) => Var(y)
//     | Ap(a1, a2) => Ap(varmap(a1, x, f), varmap(a2, x, f))
//     }
// }

// // smartapplies f to each variable in [a] greater than or equal to [n]
// let smartvarmap (a : tm, x : int, f : int => int) : tm = {
//     switch(a) {
//     | Typ => Typ
//     | In(a, ty) => In(varmap(a, x, f), varmap(ty, x, f))
//     | Arrow(y, ty1, ty2) => Arrow(y, varmap(ty1, x, f), varmap(ty2, x+1, y => f(y-1)+1))
//     | Var(y) when y >= x => Var(f(y))
//     | Var(y) => Var(y)
//     | Ap(a1, a2) => Ap(varmap(a1, x, f), varmap(a2, x, f))
//     }
// }

// // increments each variable in [a] greater than or equal to [n]
// let shift (a : tm, x : int) : tm = varmap(a, x, n => n+1)

// // decrements each variable in [a] greater than or equal to [n]
// let downshift (a : tm, x : int) : tm = varmap(a, x, n => n-1)

// // replaces all occurrences of [x] with [a], downshifting all vars > x.
// let rec subst (a1 : tm, a : tm, x : int) : tm = {
//     switch(a1) {
//     | Typ => Typ
//     | In(a1, ty) => In(subst(a1, a, x), subst(ty, a, x))
//     | Arrow(y, ty1, ty2) => Arrow(y, subst(ty1, a, x), subst(ty2, shift(a, 0), x+1))
//     | Var(y) when y == x => a 
//     | Var(y) when y > x => Var(y-1)
//     | Var(y) => Var(y)
//     | Ap(a1, a2) => Ap(subst(a1, a, x), subst(a2, a, x))
//     }
// }

let rec get_lookup_index(c : ctx, x : int, a : assumption) : tm = {
    switch(c, x) {
    | (Cons(_, _, t, a'), 0) when a' == a => wk(t)
    | (Cons(_, _, _, _), 0) => failwith("Variable is the wrong kind of assumption")
    | (Cons(c, _, _, _), x) when x > 0 => wk(get_lookup_index(c, x-1, a))
    | _ => failwith("Context lookup out of bounds")
    }
}

let lookup_index_prop(c : ctx, x : int) : result(tm, error) = 
    try { Ok(get_lookup_index(c, x, Prop)) } {
    | _ => Error("lookup index prop failed")
    }

let lookup_index_typ(c : ctx, x : int) : result(tm, error) = 
    try { Ok(get_lookup_index(c, x, Typ)) } {
    | _ => Error("lookup index type failed")
    }

// let rec get_lookup_index(c : ctx, x : int) : tm = {
//     switch(c, x) {
//     | (Cons(_, _, t, _), 0) => getwk(t)
//     | (Cons(c, _, _, _), x) when x > 0 => getwk(get_lookup_index(c, x-1))
//     | _ => failwith("Context lookup out of bounds")
//     }
// }

// let lookup_index(c : ctx, x : int) : result(tm, error) = 
//     try { Ok(get_lookup_index(c, x)) } {
//     | _ => Error("lookup index failed")
//     }

// let rec no_x (a : tm, x : int) : bool = {
//     switch(a) {
//     | Typ => true
//     | In(a, ty) => no_x(a, x) && no_x(ty, x)
//     | Arrow(_, ty1, ty2) => no_x(ty1, x) && no_x(ty2, x+1) 
//     | Var(y) => y != x
//     | Ap(a1, a2) => no_x(a1, x) && no_x(a2, x)
//     }
// }

type judgment = J(ctx, tm);

let pair_of_judgment (j : judgment) : (ctx, tm) = switch(j) {
    | J(c, ty) => (c, ty)
}

let ctx_of_judgment (j : judgment) : ctx = fst(pair_of_judgment(j))
let typ_of_judgment (j : judgment) : tm = snd(pair_of_judgment(j))
