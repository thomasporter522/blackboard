open Term 

let (let**) (f : ('a, list('b)), b : 'a => ('c, list('b))) : ('c, list('b)) = {
    let (a, l1) = f;
    let (c, l2) = b(a);
    (c, l1 @ l2)
}

let consTs (te : tele, zs : list(name), args : tele, t : tm) : tele = {
    let f(acc : tele, z : name) : tele = ConsT(acc, z, args, t);
    List.fold_left(f, te, zs)
}

let names_of_tele(te : list(surface_tele_entry)) = {
    let f (acc : tele, e : surface_tele_entry) : tele = switch(e) {
    | SurfaceTeleEntryP(z, _) => ConsP(acc, z, Prop) // Prop is a placeholder
    | SurfaceTeleEntryT(zs, _, _) => consTs(acc, zs, EmptyTele, Prop) // Empty, Prop are placeholders
    }
    List.fold_left(f, EmptyTele, te)
}

let rec tm_of_surface (c : ctx, t : surface_tm) : (tm, list(ranged_error)) = switch(t) {
    | SurfaceProp(_) => (Prop, [])
    | SurfaceTyp(_) => (Typ, [])
    | SurfaceIn(t1, t2) => 
        let** t1' = tm_of_surface(c, t1);
        let** t2' = tm_of_surface(c, t2);
        (In(t1', t2'), [])
    | SurfaceArrow(te, p) => 
        let** te' = contained_tele_of_surface(c, te);
        let** p' = tm_of_surface(Cons(c, te'), p);
        (Arrow(te', p'), [])
    | SurfaceAp(r, z, s) => 
        let** s' = subst_of_surface(c, s);
        switch(index_of_name(c, z)) {
        | Ok(n) =>  (Ap(n, s'), [])
        | Error(_) => (Nonsense, [err("Unrecognized name", r)])
        }
    | SurfaceVar(r, z) => 
        switch(index_of_name(c, z)) {
        | Ok(n) =>  (Ap(n, EmptySubst), [])
        | Error(_) => (Nonsense, [err("Unrecognized name", r)])
        }
    | SurfaceNonsense => (Nonsense, []);
}
and contained_tele_of_surface(c, te) : (tele, list(ranged_error)) = {
    let cte = names_of_tele(te);
    tele_of_surface(Cons(c, cte), te)
}
and tele_of_surface (c : ctx, te : list(surface_tele_entry)) : (tele, list(ranged_error)) = {
    let f (acc : (tele, list(ranged_error)), e : surface_tele_entry) : (tele, list(ranged_error)) = switch(e) {
    | SurfaceTeleEntryP(z, t) => 
        let** acc' = acc;
        let** t' = tm_of_surface(c, t);
        (ConsP(acc', z, t'), [])
    | SurfaceTeleEntryT(zs, te, t) =>
        let** acc' = acc;
        let** te' = contained_tele_of_surface(c, te);
        let** t' = tm_of_surface(Cons(c, te'), t);
        (consTs(acc', zs, te', t'), [])
    };
    List.fold_left(f, (EmptyTele, []), te)
}

and subst_of_surface (c : ctx, s : list(surface_subst_entry)) : (subst, list(ranged_error)) = {
    let f (acc : (subst, list(ranged_error)), SurfaceSubstEntry(z, te, t) : surface_subst_entry) : (subst, list(ranged_error)) = {
        let** acc' = acc;
        let** te' = contained_tele_of_surface(c, te);
        let** t' = tm_of_surface(Cons(c, te'), t);
        (ConsSubst(acc', z, te', t'), [])
    };
    List.fold_left(f, (EmptySubst, []), s)
}
