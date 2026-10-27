
type name = string;

type arrow = 
    | Implies
    | Forall 
    | Pi 
    | Guard

type strength = 
    | Strong 
    | Weak

type surface_tm = 
    | SurfaceProp 
    | SurfaceTyp 
    | SurfaceIn(surface_tm, surface_tm)
    | SurfaceArrow(strength, list(name), surface_tm, surface_tm)
    | SurfaceLambda(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | SurfaceVar(name)
    | SurfaceAp(surface_tm, surface_tm)
    | SurfaceUnguard(surface_tm)
    | SurfaceNonsense;

type tm = 
    | Prop
    | Typ 
    | In(tm, tm)
    | Arrow(strength, name, tm, tm)
    | Lam(name, tm, tm)
    | Var(int)
    | Ap(tm, tm)
    | Unguard(tm)
    | FreeVar(string)
    | Nonsense;

type ctx = 
    | Empty 
    | Cons(ctx, name, tm);

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
    | (Cons(_, y, _), x) when y == x => Ok(0)
    | (Cons(c, _, _), x) => Result.map(i => 1+i, index_of_name(c, x))
    | _ => Error("Context lookup unbound name")
    }
}

let tail_of_ctx(c : ctx) : ctx = switch(c) {
    | Empty => failwith("tail of empty context")
    | Cons(c', _, _) => c'
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
    | Arrow(st, y, ty1, ty2) => Arrow(st, y, wkn(n, ty1), wkn(n+1, ty2))
    | Lam(y, ty, a) => Lam(y, wkn(n, ty), wkn(n+1, a))
    | Var(y) => Var(wknvar(n, y))
    | Ap(a1, a2) => Ap(wkn(n, a1), wkn(n, a2))
    | Unguard(a) => Unguard(wkn(n, a))
    | FreeVar(x) => FreeVar(x)
    | Nonsense => Nonsense
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
    | Arrow(st, y, ty1, ty2) => Arrow(st, y, substn(n, s, ty1), substn(n+1, s, ty2))
    | Lam(y, ty, a) => Lam(y, substn(n, s, ty), substn(n+1, s, a))
    | Var(y) => substnvar(n, s, y)
    | Ap(a1, a2) => Ap(substn(n, s, a1), substn(n, s, a2))
    | Unguard(a) => Unguard(substn(n, s, a))
    | FreeVar(x) => FreeVar(x)
    | Nonsense => Nonsense
}

let subst(s : tm, t : tm) : tm = substn(0, s, t)


let rec headnormalize(t : tm) : tm = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(t1, t2) => In(t1, t2)
    | Arrow(st, x, t1, t2) => Arrow(st, x, t1, t2)
    | Lam(x, t1, t2) => Lam(x, t1, t2)
    | Var(x) => Var(x)
    | Ap(t1, t2) => {
        switch(headnormalize(t1)) {
        | Lam(_, _, body) => headnormalize(subst(t2, body))
        | _ => Ap(t1, t2)
        }
    }
    | Unguard(t) => Unguard(t)
    | FreeVar(x) => FreeVar(x)
    | Nonsense => Nonsense
}

let rec normalize(t : tm) : tm = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(t1, t2) => In(normalize(t1), normalize(t2))
    | Arrow(st, x, t1, t2) => Arrow(st, x, normalize(t1), normalize(t2))
    | Lam(x, t1, t2) => Lam(x, normalize(t1), normalize(t2))
    | Var(x) => Var(x)
    | Ap(t1, t2) => {
        switch(normalize(t1)) {
        | Lam(_, _, body) => normalize(subst(t2, body))
        | t1' => Ap(t1', normalize(t2))
        }
    }
    | Unguard(t) => Unguard(normalize(t))
    | FreeVar(x) => FreeVar(x)
    | Nonsense => Nonsense
}

let rec alphaequiv(a1 : tm, a2 : tm) : bool = {
    switch(a1, a2) {
    | (Prop, Prop) => true 
    | (Typ, Typ) => true 
    | (In(a1, a2), In(a3, a4)) => alphaequiv(a1, a3) && alphaequiv(a2, a4)
    | (Arrow(_st1, _, a1, a2), Arrow(_st2, _, a3, a4)) => alphaequiv(a1, a3) && alphaequiv(a2, a4) // && st1 == st2
    | (Lam(_, a1, a2), Lam(_, a3, a4)) => alphaequiv(a1, a3) && alphaequiv(a2, a4)
    | (Var(x1), Var(x2)) => x1 == x2
    | (Ap(a1, a2), Ap(a3, a4)) => alphaequiv(a1, a3) && alphaequiv(a2, a4)
    | (Unguard(a1), Unguard(a2)) => alphaequiv(a1, a2)
    | (FreeVar(x), FreeVar(y)) => x == y
    | (Nonsense, Nonsense) => false
    | (Prop, _) => false
    | (Typ, _) => false
    | (In(_), _) => false
    | (Arrow(_), _) => false
    | (Lam(_), _) => false
    | (Var(_), _) => false
    | (Ap(_), _) => false
    | (Unguard(_), _) => false
    | (FreeVar(_), _) => false
    | (Nonsense, _) => false
    }
}

// definitional equality
// let rec equiv(a1 : tm, a2 : tm) : bool = alphaequiv(normalize(a1), normalize(a2))
let rec equiv(a1 : tm, a2 : tm) : bool = {
    if (alphaequiv(a1, a2)) { true } else {
        switch(headnormalize(a1), headnormalize(a2)) {
        | (Prop, Prop) => true 
        | (Typ, Typ) => true 
        | (In(a1, a2), In(a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
        | (Arrow(_st1, _, a1, a2), Arrow(_st2, _, a3, a4)) => equiv(a1, a3) && equiv(a2, a4) // && st1 == st2
        | (Lam(_, a1, a2), Lam(_, a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
        | (Var(x1), Var(x2)) => x1 == x2
        | (Ap(a1, a2), Ap(a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
        | (Unguard(a1), Unguard(a2)) => equiv(a1, a2)
        | (FreeVar(x), FreeVar(y)) => x == y
        | (Nonsense, Nonsense) => false
        | (Prop, _) => false
        | (Typ, _) => false
        | (In(_), _) => false
        | (Arrow(_), _) => false
        | (Lam(_), _) => false
        | (Var(_), _) => false
        | (Ap(_), _) => false
        | (Unguard(_), _) => false
        | (FreeVar(_), _) => false
        | (Nonsense, _) => false
        }
    }
}


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

type lookup_index_result = 
    | Ok(tm)
    | WrongKind
    | OutOfBounds

let rec lookup_index(c : ctx, x : int) : result(tm, error) = {
    switch(c, x) {
    | (Cons(_, _, t), 0) => Ok(wk(t))
    | (Cons(c, _, _), x) when x > 0 => 
        let* t = lookup_index(c, x-1); 
        Ok(wk(t))
    | _ => Error("lookup_index out of bounds")
    }
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

type mode = 
    | Blue 
    | Red

type judgment = J(ctx, tm, mode);

let tuple_of_judgment (j : judgment) : (ctx, tm, mode) = switch(j) {
    | J(c, ty, m) => (c, ty, m)
}

let ctx_of_judgment (j : judgment) : ctx = {
    let (c, _, _) = tuple_of_judgment(j);
    c
}

let type_of_judgment (j : judgment) : tm = {
    let (_, p, _) = tuple_of_judgment(j);
    p
}

let mode_of_judgment (j : judgment) : mode = {
    let (_, _, m) = tuple_of_judgment(j);
    m
}