
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

let rec index_of_name(c : ctx, x : name) : int = {
    switch(c, x) {
    | (Cons(_, y, _), x) when y == x => 0
    | (Cons(c, _, _), x) => 1+index_of_name(c, x)
    | _ => failwith("Context lookup unbound name")
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

module Theorem : {
    type t; 
    let hyp : (ctx, int) => t;
    let in_formation : (t, t) => t;
    let in_elimination : t => t;
    let cut : (t, t) => t;
    let typ_formation : ctx => t;
    let arrow_formation : (t, t) => t;
    let ap : (t, t) => t;
    let arrow_introduction : t => t;
} = {
    type t = judgment;

    let hyp (c : ctx, x : int) : t = {
        J(c, lookup_index(c, x))
    };

    let in_formation (d1 : t, d2 : t) : t = {
        switch(d1, d2) {
        | (J(c, In(ty1, Typ)), J(c', In(a, _))) 
            when c' == c
        => J(c, In(In(a, ty1),Typ))
        | _ => failwith("invalid premises: in_formation")
        }
    }

    let in_elimination (d : t) : t = {
        switch(d) {
        | J(c, In(_, ty))  
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
        | (J(c, ty1), J(Cons(c', _, ty1'), ty2)) 
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

    let ap (d1 : t, d2 : t) : t = {
        switch(d1, d2) {
        | (J(c, In(_, Arrow(_, ty1, ty2))), J(c', In(a2, ty1')))
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

module PartialDerivation : {
    type t; 
    let init : judgment => t;
    let focused : t => judgment;
    let skip : t => t; 
    let hyp : (t, int) => t;
    let in_formation : (t, tm) => t;
    let in_elimination : (t, tm) => t;
    let cut : (t, name, tm) => t;
    let typ_formation : t => t;
    let arrow_formation : t => t;
    let ap : (t, name, tm, tm) => t;
    let arrow_introduction : t => t;

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

    let focused (s : t) : judgment = {
        switch(s.focused) {
            | [h, ..._] => h
            | [] => failwith("nothing focused")
        }
    }

    let skip (s : t) : t = {
        switch(s.focused) {
            | [h, ... t] => {
                skipped: [h, ...s.skipped],
                focused: t,
                root: s.root
            }
            | [] => failwith("nothing to skip")
        }
    }

    let refine (s : t, f : judgment => list(judgment)) : t = {
        switch(s.focused) {
            | [h, ... t] => {
                skipped: s.skipped,
                focused: f(h) @ t,
                root: s.root
            }
            | [] => failwith("nothing to refine")
        }
    }

    let hyp (s : t, x : int) : t = refine(s, j => {
        switch(j) {
        | J(c, ty) => 
            let found = lookup_index(c, x);
            if (equiv(found, ty)) [] else failwith("hyp failure")
        }
    })

    let in_formation (s : t, ty2 : tm) : t = refine(s, j => {
        switch(j) {
        | J(c, In(In(a, ty1), Typ)) => {
            [J(c, In(ty1, Typ)), J(c, In(a, ty2))]
        }
        | _ => failwith("in_formation failure")
        }
    })

    let in_elimination (s : t, a : tm)  : t = refine(s, j => {
        switch(j) {
        | J(c, ty) => [J(c, In(a, ty))]
        }
    })

    let cut (s : t, x : name, ty1 : tm)  : t = refine(s, j => {
        switch(j) {
        | J(c, ty2) => [J(c, ty1), J(Cons(c, x, ty1), shift(ty2, 0))]
        }
    })

    let typ_formation (s : t)  : t = refine(s, j => {
        switch(j) {
        | J(_, In(Typ, Typ)) => []
        | _ => failwith("typ_formation failure")
        }
    })

    let arrow_formation (s : t)  : t = refine(s, j => {
        switch(j) {
        | J(c, In(Arrow(x, ty1, ty2), Typ)) => [J(c, In(ty1, Typ)), J(Cons(c, x, ty1), In(ty2, Typ))]
        | _ => failwith("arrow_formation failure")
        }
    })

    let ap (s : t, x : name, ty1 : tm, ty2 : tm)  : t = refine(s, j => {
        switch(j) {
        | J(c, In(Ap(a1, a2), ty2_sub)) when subst(ty2, a2, 0) == ty2_sub => 
            [J(c, In(a1, Arrow(x, ty1, ty2))), J(c, In(a2, ty1))]
        | _ => failwith("ap failure")
        }
    })

    let arrow_introduction (s : t)  : t = refine(s, j => {
        switch(j) {
        | J(c, Arrow(x, ty1, ty2)) => [J(Cons(c, x, ty1), ty2)]
        | _ => failwith("arrow_introduction failure")
        }
    })
}