
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

type judgment = J(ctx, tm);

module Theorem : {
    type t; 
    let hyp : ctx => int => t;
} = {
    type t = judgment;

    let rec lookup_index (c : ctx, x : int) : tm = {
        switch(c, x) {
        | (Cons(c, _, t), 0) => t
        | (Cons(c, _, _), x) when x > 0 => lookup_index(c, x-1)
        | _ => failwith("Context lookup out of bounds")
        }
    }

    let rec lookup_name (c : ctx, x : name) : tm = {
        switch(c, x) {
        | (Cons(c, y, t), x) when y == x => t
        | (Cons(c, _, _), x) => lookup_name(c, x)
        | _ => failwith("Context lookup unbound name")
        }
    }

    let hyp (c : ctx, x : int) : t = {
        J(c, lookup_index(c, x))
    };

    let in_formation (ty2 : tm, d1 : t, d2 : t) : t = {
        switch(d1, d2) {
        | (J(c, In(ty1, Typ)), J(c', In(a, ty2))) 
            when c' == c
        => J(c, In(In(a, ty1),Typ))
        | _ => failwith("invalid premises: in_formation")
        }
    }

    let in_elimination (d : t) : t = {
        switch(d) {
        | J(c, In(a, ty))  
        => J(c, ty)
        | _ => failwith("invalid premises: in_elimination")
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

    let cut (d1 : t, d2 : t) : t = {
        switch(d1, d2) {
        | (J(c, ty1), J(Cons(c', x, ty1'), ty2)) 
            when ty1' == ty1 && c' == c && no_x(ty2, 0)
        => J(c, ty2)
        | _ => failwith("invalid premises: cut")
        }
    }

    let typ_formation (c: ctx) : t = {
        J(c, In(Typ, Typ))
    }

    let arrow_formation (d1 : t, d2 : t) : t = {
        switch(d1, d2) {
        | (J(c, In(ty1, Typ)), J(Cons(c', x, ty1'), In(ty2, Typ)))
            when c' == c && ty1' == ty1
        => J(c, In(Arrow(x, ty1, ty2), Typ))
        | _ => failwith("invalid premises: arrow_formation")
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

    let ap (d1 : t, d2 : t) : t = {
        switch(d1, d2) {
        | (J(c, In(a1, Arrow(x, ty1, ty2))), J(c', In(a2, ty1')))
            when c' == c && ty1' == ty1
        => J(c, subst(ty2, a2, 0))
        | _ => failwith("invalid premises: ap")
        }
    }

    let arrow_introduction (d : t) : t = {
        switch(d) {
        | J(Cons(c, x, ty1), ty2) 
        => J(c, Arrow(x, ty1, ty2))
        | _ => failwith("invalid premises: arrow_introduction")
        }
    }
};