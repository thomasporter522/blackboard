
type name = Name(string);

type range = (int, int)

type hyp_index = HypIndex(int, int)
type term_index = Index(int, int)

type surface_tele_entry = 
    | SurfaceTeleEntryP(name, surface_tm)
    | SurfaceTeleEntryT(list(name), list(surface_tele_entry), surface_tm)

and surface_subst_entry = 
    | SurfaceSubstEntry(list(name), list(surface_tele_entry), surface_tm)

and surface_tm =
    | SurfaceProp(range)
    | SurfaceTyp(range)
    | SurfaceIn(surface_tm, surface_tm)
    | SurfaceArrow(list(surface_tele_entry), surface_tm)
    | SurfaceAp(range, name, list(surface_subst_entry))
    | SurfaceNonsense;

type tm = 
    | Prop
    | Typ 
    | In(tm, tm)
    | Arrow(tele, tm)
    | Ap(term_index, subst)
    | Nonsense

and tele = 
    | EmptyTele
    | ConsP(tele, name, tm)
    | ConsT(tele, name, tele, tm)
    
and subst =
    | EmptySubst
    | ConsSubst(subst, name, tele, tm);

type ctx = 
    | Empty 
    | Cons(ctx, tele)

let var(x, y) = Ap(Index(x, y), EmptySubst)

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
    | (EmptyTele, EmptyTele) => true 
    | (ConsP(a1, _, a2), ConsP(a3, _, a4)) => equiv_tele(a1, a3) && equiv(a2, a4)
    | (ConsT(a1, _, a2, a3), ConsT(a4, _, a5, a6)) => equiv_tele(a1, a4) && equiv_tele(a2, a5) && equiv(a3, a6)
    | (EmptyTele, _)
    | (ConsP(_), _)
    | (ConsT(_), _) => false
}
and equiv_subst(a1 : subst, a2 : subst) : bool = switch(a1, a2) {
    | (EmptySubst, EmptySubst) => true 
    | (ConsSubst(a1, _, a2, a3), ConsSubst(a4, _, a5, a6)) => equiv_subst(a1, a4) && equiv_tele(a2, a5) && equiv(a3, a6)
    | (EmptySubst, _)
    | (ConsSubst(_), _) => false
}

let rec wkn(n : int, t : tm) = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(t1, t2) => In(wkn(n, t1), wkn(n, t2))
    | Arrow(te, t1) => Arrow(wkn_tele(n+1, te), wkn(n+1, t1))
    | Ap(Index(x, y), s1) when x >= n => Ap(Index(x+1, y), wk_subst(n, s1))
    | Ap(Index(x, y), s1) => Ap(Index(x, y), wk_subst(n, s1))
    | Nonsense => Nonsense
}

and wkn_tele(n : int, te : tele) = switch(te) {
    | EmptyTele => EmptyTele 
    | ConsP(te1, y, p) => ConsP(wkn_tele(n, te1), y, wkn(n, p))
    | ConsT(te1, y, te2, t) => ConsT(wkn_tele(n, te1), y, wkn_tele(n+1, te2), wkn(n+1, t))
}

and wk_subst(n : int, s : subst) = switch(s) {
    | EmptySubst => EmptySubst 
    | ConsSubst(s', y, te, t) => ConsSubst(wk_subst(n, s'), y, wkn_tele(n+1, te), wkn(n+1, t))
}

let wk = wkn(0)
let wk_tele = wkn_tele(0)

// let rec sub_shape(s : subst, te : tele) = switch(s, te) {
//     | (Empty, Empty) => true 
//     | (s, ConsP(te', _, _)) => sub_shape(s, te')
//     | (Cons(s', _, te1, _), ConsT(te', _, te2, _)) => sub_shape(s', te') && equiv_tele(te1, te2)
//     | (Empty, _) | (Cons(_), _) => false
// }

let rec subn(n : int, s : subst, t : tm) = switch(t) {
    | Prop => Prop
    | Typ => Typ
    | In(t1, t2) => In(subn(n, s, t1), subn(n, s, t2))
    | Arrow(te, t1) => 
        let s' = wk_subst(0, s);
        Arrow(subn_tele(n+1, s', te), subn(n+1, s', t1))
    | Ap(Index(x, y), s1) when x > n => Ap(Index(x-1, y), sub_subst(n, s, s1))
    | Ap(Index(x, y), s1) when x < n => Ap(Index(x, y), sub_subst(n, s, s1))
    | Ap(Index(_n, y), s1) => 
        let s1' = sub_subst(n, s, s1);
        sub_ap(s, y, s1')
    | Nonsense => Nonsense
}

and sub_ap(s : subst, y : int, s1' : subst) = switch(y, s) {
    | (0, ConsSubst(_, _y, _, t)) => subn(0, s1', t)
    | (y, ConsSubst(s', _, _, _)) => sub_ap(s', y-1, s1')
    | (_, EmptySubst) => failwith("Misaligned sub_ap")
}

and subn_tele(n : int, s : subst, te : tele) = switch(te) {
    | EmptyTele => EmptyTele 
    | ConsP(te1, y, p) => ConsP(subn_tele(n, s, te1), y, subn(n, s, p))
    | ConsT(te1, y, te2, t) => 
        let s' = wk_subst(0, s);
        ConsT(subn_tele(n, s, te1), y, subn_tele(n+1, s', te2), subn(n+1, s', t))
}

and sub_subst(n : int, s : subst, s1 : subst) = switch(s1) {
    | EmptySubst => EmptySubst 
    | ConsSubst(s1', y, te, t) => 
        let s' = wk_subst(0, s);
        ConsSubst(sub_subst(n, s, s1'), y, subn_tele(n+1, s', te), subn(n+1, s', t))
}

let sub = subn(0)
let sub_tele = subn_tele(0)

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

let rec index_of_name(c : ctx, z : name) : result(term_index, error) = {
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

let rec lookup_index_prop_tele(te : tele, y : int) : result(tm, error) = switch(te) {
    | ConsP(_, _, p) when y == 0 => Ok(p)
    | ConsT(_) when y == 0 => Error("Wrong kind")
    | ConsP(te', _, _) when y > 0 => lookup_index_prop_tele(te', y-1)
    | ConsT(te', _, _, _) when y > 0 => lookup_index_prop_tele(te', y-1)
    | _ => Error("Out of bounds")
    }

let rec lookup_index_prop(c : ctx, HypIndex(x, y) : hyp_index) : result(tm, error) = {
    switch(c) {
    | Cons(_, te) when x == 0 => lookup_index_prop_tele(te, y)
    | Cons(c', _) when x > 0 => 
        let* p = lookup_index_prop(c', HypIndex(x-1, y));
        Ok(wk(p))
    | _ => Error("Out of bounds")
    }
}

let rec lookup_index_term_tele(te : tele, y : int) : result((tele, tm), error) =  switch(te) {
    | ConsT(_, _, te, t) when y == 0 => Ok((te, t))
    | ConsP(_) when y == 0 => Error("Wrong kind")
    | ConsT(te', _, _, _) when y > 0 => lookup_index_term_tele(te', y-1)
    | ConsP(te', _, _) when y > 0 => lookup_index_term_tele(te', y)
    | _ => Error("Out of bounds")
    }

let rec lookup_index_term(c : ctx, Index(x, y) : term_index) : result((tele, tm), error) = {
    switch(c) {
    | Cons(_, te) when x == 0 => lookup_index_term_tele(te, y)
    | Cons(c', _) when x > 0 => 
        let* (te, t) = lookup_index_term(c', Index(x-1, y));
        Ok((wkn_tele(1, te), wkn(1, t)))
    | _ => Error("Out of bounds")
    }
}

let tail_of_ctx(c : ctx) : ctx = switch(c) {
    | Empty => failwith("tail of empty context")
    | Cons(c', _) => c'
}

type judgment = J(ctx, tm);

let ctx_of_judgment (j : judgment) : ctx = {
    let J(c, _) = j;
    c
}

let type_of_judgment (j : judgment) : tm = {
    let J(_, p) = j;
    p
}