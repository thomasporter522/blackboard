open Kernel.Term
open Demo
open Elab

type surface_program = 
    | SurfaceEmpty 
    | SurfaceAssume(range, bool, list(surface_tele_entry), demo, surface_program)
    | SurfaceConstruct(range, bool, list(surface_tele_entry), demo, surface_program)
    | SurfaceProve(range, bool, name, surface_tm, demo, surface_program)

type program = 
    | Empty 
    | Assume(range, bool, ctx, tm, demo, program)
    | Construct(range, bool, ctx, tm, demo, program)
    | Prove(range, bool, ctx, tm, demo, program)

// let rec signature_of_surface(c : ctx, s : surface_signature) : (ctx, signature) = switch(s) {
//     | [] => (c, [])
//     | [(x, ty, a),...s'] => {
//         let ty_elab = tm_of_surface(c, ty);
//         let c' = Cons(c, x, ty_elab, a);
//         let (c'', s'') = signature_of_surface(c', s');
//         (c'', [(x, ty_elab), ...s''])
//     }
// }

type program_check_report = list(report);

let rec check_program (p : program) : program_check_report = {
    switch(p) {
    | Empty => []
    | Assume(r, tidy, c, ty, d, p) => [check_demo_root(J(c, In(ty, Prop)), d, r, tidy),... check_program(p)]
    | Construct(r, tidy, c, ty, d, p) => [check_demo_root(J(c, ty), d, r, tidy),... check_program(p)]
    | Prove(r, tidy, c, ty, d, p) => [check_demo_root(J(c, ty), d, r, tidy),... check_program(p)]
    }
}

let goal_of_surface_signature(c : ctx, te : list(surface_tele_entry)) : tm = {
    let (te', _) = contained_tele_of_surface(Cons(Cons(c, EmptyTele), EmptyTele), te);
    let m_prop = ConsT(EmptyTele, Name("M"), EmptyTele, Prop);
    let portal = ConsP(EmptyTele, Name("_"), Arrow(te', var(2, 0)));
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