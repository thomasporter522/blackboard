open Term 
open Program 

let (let**) (f : ('a, list('b)), b : 'a => ('c, list('b))) : ('c, list('b)) = {
    let (a, l1) = f;
    let (c, l2) = b(a);
    (c, l1 @ l2)
}

let consTs (te : tele, zs : list(name), args : tele, t : tm) : tele = {
    let f(acc : tele, z : name) : tele = ConsT(acc, z, args, t);
    List.fold_left(f, te, zs)
}

let consSubsts (s : subst, zs : list(name), args : tele, t : tm) : subst = {
    let f(acc : subst, z : name) : subst = ConsSubst(acc, z, args, t);
    List.fold_left(f, s, zs)
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
    let f (acc : (subst, list(ranged_error)), SurfaceSubstEntry(zs, te, t) : surface_subst_entry) : (subst, list(ranged_error)) = {
        let** acc' = acc;
        let** te' = contained_tele_of_surface(c, te);
        let** t' = tm_of_surface(Cons(c, te'), t);
        (consSubsts(acc', zs, te', t'), [])
    };
    List.fold_left(f, (EmptySubst, []), s)
}

let goal_of_surface_signature(c : ctx, te : list(surface_tele_entry)) : tm = {
    let (te', _) = contained_tele_of_surface(Cons(Cons(c, EmptyTele), EmptyTele), te);
    let m_prop = ConsT(EmptyTele, Name("M"), EmptyTele, Prop);
    let portal = ConsT(EmptyTele, Name("_"), te', var(2, 0));
    Arrow(m_prop, Arrow(portal, var(1, 0)))
}

let rec program_of_surface (c : ctx, p : surface_program) : (program, list(ranged_error)) = switch(p) {
    | SurfaceEmpty => (Empty, [])
    | SurfaceAssume(r, tidy, te, d, p) =>
        let goal = goal_of_surface_signature(c, te);
        let** te' = contained_tele_of_surface(c, te);
        let** p' = program_of_surface(Cons(c, te'), p);
        (Assume(r, tidy, c, goal, d, p'), [])
    | SurfaceConstruct(r, tidy, te, d, p) => 
        let goal = goal_of_surface_signature(c, te);
        let** te' = contained_tele_of_surface(c, te);
        let** p' = program_of_surface(Cons(c, te'), p);
        (Construct(r, tidy, c, goal, d, p'), [])
    | SurfaceProve(r, tidy, z, a, d, p) => 
        let** goal = tm_of_surface(c, a);
        let (a', _) = tm_of_surface(Cons(c, EmptyTele), a);
        let te = ConsP(EmptyTele, z, a');
        let** p' = program_of_surface(Cons(c, te), p);
        (Prove(r, tidy, c, goal, d, p'), [])
}