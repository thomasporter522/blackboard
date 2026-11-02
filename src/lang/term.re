
type name = Name(string);

type range = (int, int)

type index = Index(int, int)

type surface_tm = 
    | SurfaceProp(range)
    | SurfaceTyp(range)
    | SurfaceIn(surface_tm, surface_tm)
    | SurfaceArrow(list(name), surface_tm, surface_tm)
    | SurfaceLambda(list(name), surface_tm, surface_tm)
    | SimpleArrow(surface_tm, surface_tm)
    | SurfaceVar(range, name)
    | SurfaceAp(surface_tm, surface_tm)
    | SurfaceUnguard(surface_tm)
    | SurfaceNonsense;

type tm = 
    | Prop
    | Typ 
    | In(tm, tm)
    | Arrow(tele, tm)
    | Ap(index, subst)
    | Nonsense

and tele = 
    | Empty 
    | ConsP(tele, name, tm)
    | ConsT(tele, name, tele, tm)
    
and subst =
    | Empty
    | Cons(subst, name, tele, tm);

type ctx = 
    | Empty 
    | Cons(ctx, tele)


let rec wk(n : int, t : tm) = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(t1, t2) => In(wk(n, t1), wk(n, t2))
    | Arrow(te, t1) => Arrow(wk_tele(n+1, te), wk(n+1, t1))
    | Ap(Index(x, y), s1) when x >= n => Ap(Index(x+1, y), wk_subst(n, s1))
    | Ap(Index(x, y), s1) => Ap(Index(x, y), wk_subst(n, s1))
    | Nonsense => Nonsense
}

and wk_tele(n : int, te : tele) = switch(te) {
    | Empty => Empty 
    | ConsP(te1, y, p) => ConsP(wk_tele(n, te1), y, wk(n, p))
    | ConsT(te1, y, te2, t) => ConsT(wk_tele(n, te1), y, wk_tele(n+1, te2), wk(n+1, t))
}

and wk_subst(n : int, s : subst) = switch(s) {
    | Empty => Empty 
    | Cons(s', y, te, t) => Cons(wk_subst(n, s'), y, wk_tele(n+1, te), wk(n+1, t))
}

let rec sub(n : int, s : subst, t : tm) = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(t1, t2) => In(sub(n, s, t1), sub(n, s, t2))
    | Arrow(te, t1) => 
        let s' = wk_subst(0, s);
        Arrow(sub_tele(n+1, s', te), sub(n+1, s', t1))
    | Ap(Index(x, y), s1) when x > n => Ap(Index(x-1, y), sub_subst(n, s, s1))
    | Ap(Index(x, y), s1) when x < n => Ap(Index(x, y), sub_subst(n, s, s1))
    | Ap(Index(_n, y), s1) => 
        let s1' = sub_subst(n, s, s1);
        sub_ap(s, y, s1')
    | Nonsense => Nonsense
}

and sub_ap(s : subst, y : int, s1' : subst) = switch(y, s) {
    | (0, Cons(_, _y, _, t)) => sub(0, s1', t)
    | (y, Cons(s', _, _, _)) => sub_ap(s', y-1, s1')
    | (_, Empty) => failwith("Misaligned sub_ap")
}

and sub_tele(n : int, s : subst, te : tele) = switch(te) {
    | Empty => Empty 
    | ConsP(te1, y, p) => ConsP(sub_tele(n, s, te1), y, sub(n, s, p))
    | ConsT(te1, y, te2, t) => 
        let s' = wk_subst(0, s);
        ConsT(sub_tele(n, s, te1), y, sub_tele(n+1, s', te2), sub(n+1, s', t))
}

and sub_subst(n : int, s : subst, s1 : subst) = switch(s1) {
    | Empty => Empty 
    | Cons(s1', y, te, t) => 
        let s' = wk_subst(0, s);
        Cons(sub_subst(n, s, s1'), y, sub_tele(n+1, s', te), sub(n+1, s', t))
}

type error = string;

type ranged_error = {
    message : error, 
    range : range
}

let err(message, range) : ranged_error = {message, range}

let arrange(a, r) = 
    switch(a) {
    | Ok(n) => Ok(n)
    | Error(e) => Error(err(e, r))
    }

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

let rec index_of_name_tele(te : tele, z : name) : result(int, error) = {
    switch(te) {
    | ConsP(te', _, _) => index_of_name_tele(te', z)
    | ConsT(_, z', _, _) when z' == z => Ok(0)
    | ConsT(te', _, _, _) => 
        let* i = index_of_name_tele(te', z);
        Ok(i+1)
    | _ => Error("Unrecognized name")
    }
}

let rec index_of_name(c : ctx, z : name) : result(index, error) = {
    switch(c) {
    | Cons(c', te) => 
        switch(index_of_name_tele(te, z)) {
        | Ok(y) => Ok(Index(0, y))
        | Error(_) => 
            let* Index(x, y) = index_of_name(c', z);
            Ok(Index(x+1, y))
        }
    | _ => Error("Unrecognized name")
    }
}

let tail_of_ctx(c : ctx) : ctx = switch(c) {
    | Empty => failwith("tail of empty context")
    | Cons(c', _) => c'
}

let rec equiv(a1 : tm, a2 : tm) : bool = {
    switch(a1, a2) {
    | (Prop, Prop) => true 
    | (Typ, Typ) => true 
    | (In(a1, a2), In(a3, a4)) => equiv(a1, a3) && equiv(a2, a4)
    | (Arrow(a1, a2), Arrow(a3, a4)) => equiv_tele(a1, a3) && equiv(a2, a4)
    | (Ap(a1, a2), Ap(a3, a4)) => a1 == a3 && equiv_subst(a2, a4)
    | (Prop, _) => false
    | (Typ, _) => false
    | (In(_), _) => false
    | (Arrow(_), _) => false
    | (Ap(_), _) => false
    | (Nonsense, _) => false
    }
}

and equiv_tele(a1 : tele, a2 : tele) : bool = switch(a1, a2) {
    | (Empty, Empty) => true 
    | (ConsP(a1, _, a2), ConsP(a3, _, a4)) => equiv_tele(a1, a3) && equiv(a2, a4)
    | (ConsT(a1, _, a2, a3), ConsT(a4, _, a5, a6)) => equiv_tele(a1, a4) && equiv_tele(a2, a5) && equiv(a3, a6)
    | (Empty, _)
    | (ConsP(_), _)
    | (ConsT(_), _) => false
}
and equiv_subst(a1 : subst, a2 : subst) : bool = switch(a1, a2) {
    | (Empty, Empty) => true 
    | (Cons(a1, _, a2, a3), Cons(a4, _, a5, a6)) => equiv_subst(a1, a4) && equiv_tele(a2, a5) && equiv(a3, a6)
    | (Empty, _)
    | (Cons(_), _) => false
}

type judgment = J(ctx, tm);

let tuple_of_judgment (j : judgment) : (ctx, tm) = switch(j) {
    | J(c, ty) => (c, ty)
}

let ctx_of_judgment (j : judgment) : ctx = {
    let (c, _) = tuple_of_judgment(j);
    c
}

let type_of_judgment (j : judgment) : tm = {
    let (_, p) = tuple_of_judgment(j);
    p
}