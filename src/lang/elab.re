open Term 

let (let**) (f : ('a, list('b)), b : 'a => ('c, list('b))) : ('c, list('b)) = {
    let (a, l1) = f;
    let (c, l2) = b(a);
    (c, l1 @ l2)
}

let rec tm_of_surface (c : ctx, t : surface_tm) : (tm, list(ranged_error)) = switch(t) {
    | SurfaceProp(_) => (Prop, [])
    | SurfaceTyp(_) => (Typ, [])
    | SurfaceIn(t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(c, t2);
        (In(t1', t2'), [])
    | SurfaceArrow(te, p) => 
        let (te', _) = tele_of_surface(c, te);
        let** te' = tele_of_surface(Cons(c, te'), te);
        let** p' = tm_of_surface(Cons(c, te'), p);
        (Arrow(te', p'), [])
    | SurfaceAp(r, z, s) => 
        let** s' = subst_of_surface(c, List.rev(s));
        switch(index_of_name(c, z)) {
        | Ok(n) =>  (Ap(n, s'), [])
        | Error(_) => (Nonsense, [err("Unrecognized name", r)])
        }
    | SurfaceVar(r, z) => 
        switch(index_of_name(c, z)) {
        | Ok(n) =>  (Ap(n, Empty), [])
        | Error(_) => (Nonsense, [err("Unrecognized name", r)])
        }
    | SurfaceNonsense => (Nonsense, []);
}
and tele_of_surface (c : ctx, te : list(surface_tele_entry)) : (tele, list(ranged_error)) = failwith("todo")
and subst_of_surface (c : ctx, s : list(surface_subst_entry)) : (subst, list(ranged_error)) = failwith("todo")
